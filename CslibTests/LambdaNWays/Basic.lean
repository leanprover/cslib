/-
Copyright (c) 2026 Alex Korbonits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Korbonits
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic

/-! # Test harness for the `lambda-n-ways` normalization corpus

[`lambda-n-ways`](https://github.com/sweirich/lambda-n-ways) compares implementations of binding
by normalizing the λ-terms stored in its `lams/` directory and checking the result against a
stored normal form. Those files are vendored verbatim in `lams/` next to this module (see
`lams/README.md`); this module provides everything needed to run them against Cslib's locally
nameless representation:

* a parser for the concrete syntax of the `.lam` files (`parseTerms`, `parseTerm`);
* a translation from the parsed named terms into `LocallyNameless.Untyped.Term ℕ` (`Named.toLN`);
* a fuel-bounded normal-order normalizer built out of `Term.open'`, `Term.close`, `Term.subst`
  and `Term.fv` (`nf`), which can contract a β-redex either directly or by going through a fresh
  variable and substituting (`Beta`);
* the harness that runs a whole corpus file with both (`checkCorpus`, `checkTerm`).

Nothing here is a proof: the point of the exercise is that the *definitions* of opening, closing
and substitution could be consistently wrong in a way that still satisfies the metatheory in
`Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties`, so we pin them down by
computing with them on terms whose normal forms are known independently.

Note that α-equivalence is not needed to compare results: the locally nameless representation is
canonical, so terms are compared with `=`. Upstream, which works with a named representation,
has to convert to de Bruijn form before comparing.

## References

* <https://github.com/sweirich/lambda-n-ways>, in particular `lib/Util/Syntax/Lambda.hs`
  (concrete syntax), `lib/LocallyNameless/Ott.hs` (the normalizer transcribed here) and
  `tests/Main.hs` (the test suite).
-/

namespace CslibTests.LambdaNWays

open Cslib LambdaCalculus.LocallyNameless.Untyped

/-- Locally nameless λ-terms with free variables drawn from `ℕ`. -/
abbrev T := Term ℕ

deriving instance DecidableEq for Term

/-! ## Named terms

The concrete syntax of the corpus files is a named λ-calculus, so terms are parsed into `Named`
and translated afterwards. -/

/-- A λ-term with named variables, mirroring `Util.Syntax.Lambda.LC` upstream. -/
inductive Named where
  /-- A variable. -/
  | var (x : String)
  /-- An abstraction. -/
  | lam (x : String) (b : Named)
  /-- An application. -/
  | app (f a : Named)
  deriving Inhabited

namespace Named

/-- The names occurring free in a term, in no particular order. `bound` lists the binders that
are in scope and `acc` accumulates the names found so far. -/
def freeNamesAux (bound acc : List String) : Named → List String
  | .var x => if bound.contains x || acc.contains x then acc else x :: acc
  | .lam x b => freeNamesAux (x :: bound) acc b
  | .app f a => freeNamesAux bound (freeNamesAux bound acc f) a

/-- The names occurring free in a term, sorted.

Free variables are numbered by their position in this list. Sorting makes the numbering depend
only on the *set* of free names, so that a term and its expected normal form agree on it; this is
what upstream's `Util.Impl.toIdInt` achieves. -/
def freeNames (t : Named) : List String :=
  (freeNamesAux [] [] t).mergeSort (fun a b => decide (a ≤ b))

/-- Translation into the locally nameless representation. A variable becomes `Term.bvar i` when it
is bound by the `i`-th enclosing binder, and `Term.fvar n` when it is free, where `n` is its index
in `fvs`. -/
def toLNAux (fvs : List String) (binders : List String) : Named → Except String T
  | .var x =>
    match binders.findIdx? (· == x) with
    | some i => .ok (.bvar i)
    | none =>
      match fvs.findIdx? (· == x) with
      | some i => .ok (.fvar i)
      | none => .error s!"free variable '{x}' missing from the free variable list"
  | .lam x b => (Term.abs ·) <$> toLNAux fvs (x :: binders) b
  | .app f a => return .app (← toLNAux fvs binders f) (← toLNAux fvs binders a)

/-- Translation into the locally nameless representation. -/
def toLN (t : Named) : Except String T :=
  toLNAux (freeNames t) [] t

end Named

/-! ## Concrete syntax

The grammar, following `Util.Syntax.Lambda.pLC` upstream:

```text
term ::= '\' ident '.' term | 'let' def (';' def)* 'in' term | app
def  ::= ident '=' term
app  ::= atom+                            -- left associative
atom ::= ident | '(' term ')'
```

`let` is sugar: `let x = e in b` stands for `(\x.b) e`, and successive definitions are nested so
that earlier ones are in scope in later ones. Haskell-style `--` comments run to the end of the
line. -/

/-- A token of the `.lam` concrete syntax. -/
inductive Tok where
  /-- `\`, introducing an abstraction. -/
  | lam
  /-- `.`, separating an abstraction's binder from its body. -/
  | dot
  /-- `(`. -/
  | lparen
  /-- `)`. -/
  | rparen
  /-- `=`, in a `let` definition. -/
  | eq
  /-- `;`, separating `let` definitions. -/
  | semi
  /-- The keyword `let`. -/
  | «let»
  /-- The keyword `in`. -/
  | «in»
  /-- An identifier. -/
  | ident (s : String)
  deriving DecidableEq, Inhabited

/-- Characters that may occur in an identifier. -/
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- Tokenizer for the `.lam` concrete syntax. -/
partial def tokenize (s : String) : Except String (List Tok) := go s.toList
where
  /-- Tokenize the remaining characters. -/
  go : List Char → Except String (List Tok)
    | [] => .ok []
    | c :: cs =>
      if c.isWhitespace then go cs
      else if c == '\\' then (Tok.lam :: ·) <$> go cs
      else if c == '.' then (Tok.dot :: ·) <$> go cs
      else if c == '(' then (Tok.lparen :: ·) <$> go cs
      else if c == ')' then (Tok.rparen :: ·) <$> go cs
      else if c == '=' then (Tok.eq :: ·) <$> go cs
      else if c == ';' then (Tok.semi :: ·) <$> go cs
      else if isIdentChar c then
        let name := String.ofList (c :: cs.takeWhile isIdentChar)
        let tok := if name == "let" then .«let» else if name == "in" then .«in» else .ident name
        (tok :: ·) <$> go (cs.dropWhile isIdentChar)
      else .error s!"unexpected character '{c}'"

mutual

/-- Parse a term. -/
partial def parseNamed (ts : List Tok) : Except String (Named × List Tok) :=
  match ts with
  | .lam :: .ident x :: .dot :: ts => do
    let (b, ts) ← parseNamed ts
    return (.lam x b, ts)
  | .lam :: _ => .error "expected 'binder.' after '\\'"
  | .«let» :: ts => do
    let (defs, ts) ← parseDefs ts
    let (body, ts) ← parseNamed ts
    return (defs.foldr (fun (x, e) b => .app (.lam x b) e) body, ts)
  | ts => do
    let (h, ts) ← parseAtom ts
    parseApp h ts

/-- Parse the arguments of an application, given the function `acc` parsed so far. -/
partial def parseApp (acc : Named) (ts : List Tok) : Except String (Named × List Tok) :=
  match ts with
  | .ident _ :: _ | .lparen :: _ => do
    let (a, ts) ← parseAtom ts
    parseApp (.app acc a) ts
  | _ => .ok (acc, ts)

/-- Parse a variable or a parenthesized term. -/
partial def parseAtom (ts : List Tok) : Except String (Named × List Tok) :=
  match ts with
  | .ident x :: ts => .ok (.var x, ts)
  | .lparen :: ts => do
    let (e, ts) ← parseNamed ts
    match ts with
    | .rparen :: ts => .ok (e, ts)
    | _ => .error "expected ')'"
  | _ => .error "expected a variable or '('"

/-- Parse the definitions of a `let`, up to and including the closing `in`. -/
partial def parseDefs (ts : List Tok) : Except String (List (String × Named) × List Tok) :=
  match ts with
  | .ident x :: .eq :: ts => do
    let (e, ts) ← parseNamed ts
    match ts with
    | .semi :: ts => do
      let (ds, ts) ← parseDefs ts
      return ((x, e) :: ds, ts)
    | .«in» :: ts => return ([(x, e)], ts)
    | _ => .error "expected ';' or 'in' after a let definition"
  | _ => .error "expected 'name = term' in a let"

end

/-- Drop `--` comments, as upstream's `Util.Misc.stripComments` does. -/
def stripComments (s : String) : String :=
  String.intercalate "\n" <| s.splitOn "\n" |>.map fun line =>
    match line.splitOn "--" with
    | [] => line
    | before :: _ => before

/-- Parse a single term, translated into the locally nameless representation. -/
def parseTerm (s : String) : Except String T := do
  let ts ← tokenize (stripComments s)
  let (e, rest) ← parseNamed ts
  unless rest.isEmpty do throw "unexpected trailing input"
  Named.toLN e

/-- Parse a corpus file holding one term per line, as upstream's `Util.Impl.getTerms` does. -/
def parseTerms (s : String) : Except String (List T) :=
  (stripComments s).splitOn "\n" |>.filter (!·.all Char.isWhitespace) |>.mapM parseTerm

/-! ## Normalization

A transcription of the fuel-bounded normalizer of `lib/LocallyNameless/Ott.hs`, the locally
nameless implementation that upstream compares everything else against, on top of Cslib's
`Term.open'`, `Term.close` and `Term.subst`.

The fuel bounds the *depth* of the recursion, exactly as upstream's `nfi` does, and only exists to
make the definitions total: every corpus term normalizes. -/

/-- How a β-redex is contracted.

`Term.open'` is the primitive one: `open' b a` plugs the argument `a` into the body `b` of the
abstraction. Contracting instead by opening `b` with a *fresh* variable and then substituting the
argument for it routes every β-step of the corpus through `Term.subst`, which is otherwise not
exercised at all. The two agree by `Term.subst_intro`, so both must produce the same normal
forms. -/
inductive Beta where
  /-- Contract with `Term.open'`. -/
  | «open»
  /-- Contract with `Term.open'` on a fresh variable, then `Term.subst`. -/
  | subst
  deriving DecidableEq, Inhabited

/-- Contract the redex `Term.app (Term.abs b) a`, where `v` is fresher than every variable in
scope. Returns the updated supply of fresh variables along with the contractum. -/
def Beta.contract : Beta → ℕ → T → T → ℕ × T
  | .«open», v, b, a => (v, Term.open' b a)
  | .subst, v, b, a => (v + 1, (Term.open' b (.fvar v))[v := a])

/-- Weak head normal form, threading the supply `v` of fresh variables. -/
def whnf (β : Beta) : ℕ → ℕ → T → Option (ℕ × T)
  | 0, _, _ => none
  | _ + 1, v, .fvar x => some (v, .fvar x)
  | _ + 1, v, .bvar i => some (v, .bvar i)
  | _ + 1, v, .abs b => some (v, .abs b)
  | n + 1, v, .app f a =>
    match whnf β n v f with
    | none => none
    | some (v, .abs b) =>
      let (v, t) := β.contract v b a
      whnf β n v t
    | some (v, f') => some (v, .app f' a)

/-- Normal form, threading the supply `v` of fresh variables, which also provides the variables
used to go under binders. Seeding `v` above every free variable of the term and only ever
incrementing it makes each variable it hands out globally fresh, as upstream's `nfi` does. -/
def nfAux (β : Beta) : ℕ → ℕ → T → Option (ℕ × T)
  | 0, _, _ => none
  | _ + 1, v, .fvar x => some (v, .fvar x)
  | _ + 1, v, .bvar i => some (v, .bvar i)
  | n + 1, v, .abs b =>
    match nfAux β n (v + 1) (Term.open' b (.fvar v)) with
    | none => none
    | some (v', b') => some (v', .abs (Term.close b' v))
  | n + 1, v, .app f a =>
    match whnf β n v f with
    | none => none
    | some (v, .abs b) =>
      let (v, t) := β.contract v b a
      nfAux β n v t
    | some (v, f') =>
      match nfAux β n v f' with
      | none => none
      | some (v, f'') =>
        match nfAux β n v a with
        | none => none
        | some (v, a') => some (v, .app f'' a')

/-- Normal form. Returns `none` if `fuel` is exhausted. -/
def nf (β : Beta) (fuel : ℕ) (t : T) : Option T :=
  (nfAux β fuel (HasFresh.fresh t.fv) t).map Prod.snd

/-- The recursion depth allowed to `nf`. Far above what any corpus term needs. -/
def fuel : ℕ := 100000

/-! ## Running a corpus -/

/-- Wrap `s` in parentheses when `b` holds. -/
def parenIf (b : Bool) (s : String) : String := if b then "(" ++ s ++ ")" else s

/-- Render a term in the concrete syntax of the corpus files, naming the binder at depth `d`
`xd`, as upstream's `fromDB` does. Only used to report failures. -/
def render (t : T) : String := go 0 0 t
where
  /-- Render at binding depth `d` and precedence `prec`. -/
  go (d prec : ℕ) : T → String
    | .fvar x => s!"x{x}"
    | .bvar i => if i < d then s!"x{d - i - 1}" else s!"?{i}"
    | .abs b => parenIf (prec > 0) s!"\\x{d}.{go (d + 1) 0 b}"
    | .app f a => parenIf (prec > 1) s!"{go d 1 f} {go d 2 a}"

/-- Check that `t` normalizes to `expected`, contracting redexes with `β`. -/
def checkOne (β : Beta) (label : String) (t expected : T) : Except String Unit :=
  let how := match β with | .«open» => "Term.open'" | .subst => "Term.subst"
  match nf β fuel t with
  | none => .error s!"{label} ({how}): normalization exceeded a depth of {fuel} on {render t}"
  | some result =>
    if result = expected then .ok () else
      .error s!"{label} ({how}):\n  input:    {render t}\n  \
        produced: {render result}\n  expected: {render expected}"

/-- Check every term of a corpus file against the corresponding term of its `.nf` file, with
both ways of contracting a redex. -/
def checkCorpus (input expected : String) : Except String Unit := do
  let ts ← parseTerms input
  let es ← parseTerms expected
  unless ts.length == es.length do
    throw s!"{ts.length} terms but {es.length} expected normal forms"
  for β in [Beta.«open», Beta.subst] do
    for ((t, e), i) in (ts.zip es).zipIdx do
      checkOne β s!"term {i}" t e

/-- Check a corpus file holding a single term against its `.nf` file, with both ways of
contracting a redex. -/
def checkTerm (input expected : String) : Except String Unit := do
  let t ← parseTerm input
  let e ← parseTerm expected
  for β in [Beta.«open», Beta.subst] do
    checkOne β "term" t e

/-- Run a whole-file check, failing elaboration with a readable message. -/
def run (name : String) (check : Except String Unit) : IO Unit :=
  match check with
  | .ok _ => pure ()
  | .error e => throw <| IO.userError s!"lambda-n-ways corpus '{name}': {e}"

end CslibTests.LambdaNWays
