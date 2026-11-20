/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Languages.Mech.Common.Expr.Basic

/-! # Notation for local expressions

We define the syntactic category `mechExpr` for expressions. A local expression is either a braced
Lean computation `{...}`, which may read local variables with `$`, or a term of type `L.Expr α`,
such as `f <$> x <*> e` or `LocalSig.Expr.var x`. The braced form has priority, so `{...}` is not
read as a Lean term such as a singleton set. Since the longest parse wins, a longer Lean term that
begins with braces, such as `{s} ∪ t`, is still read as a term. The notation `` `(MechExpr| e) ``
produces the `L.Expr` denoted by `e`.

In `{f $x $y}`, the `$`-reads become arguments of a Lean function applied to `x` and `y`, and
`{value}` embeds a Lean value. A `$` name must not also occur as an ordinary identifier in the same
braces: this conservative restriction prevents accidentally capturing a binder. Rename the Lean
identifier or write `f <$> x <*> y` when that distinction is needed. Ambiguous parses containing
`$` are rejected; `f <$> x <*> y` can be used instead. Lean quotations within braces retain their
own antiquotations.
-/

@[expose] public section

namespace Cslib.Mech

/-- Syntactic category for local expressions. -/
declare_syntax_cat mechExpr

/-- A braced Lean computation, which may read local variables with `$`, as in `{$x + 1}`. -/
syntax (name := mechExprBraced) (priority := high) "{" term "}" : mechExpr

/-- A local expression given as a term of type `L.Expr α`. -/
syntax (name := mechExprTerm) term : mechExpr

/-- The local expression denoted by a `mechExpr`. -/
syntax "`(MechExpr| " mechExpr ")" : term

open Lean in
/-- Replace each `$`-read in the body of a braced computation with a fresh identifier.

Lean's term parser accepts `$x` anywhere in a term, as an antiquotation (syntax kind
`term.pseudo.antiquot`), so the body `$x + $y` of `{$x + $y}` parses as an ordinary term. This
function traverses that syntax tree and replaces each antiquotation `$x` with a fresh identifier
`b`. It returns the rewritten syntax together with the pairs `(b, x)`, in the order in which the
reads occur from left to right. Each occurrence gets its own identifier, also when the same variable
is read more than once.

For example, `f $x $y` becomes `f b₁ b₂`, with the reads `#[(b₁, x), (b₂, y)]`. -/
private meta partial def extractLocalReads (stx : Syntax) :
    MacroM (Syntax × Array (Ident × Ident)) := do
  -- Lean quotations have their own antiquotations, which must remain untouched.
  if stx.getKind == ``Lean.Parser.Term.quot || stx.getKind == ``Lean.Parser.Term.dynamicQuot ||
      stx.getKind == ``Lean.Parser.Term.precheckedQuot ||
      stx.getKind == ``Lean.Parser.Command.quot || stx.getKind == ``Lean.Parser.Tactic.quot then
    return (stx, #[])
  if stx.getKind == `term.pseudo.antiquot then
    -- The children of an antiquotation are: `$`, escaping `$`s (as in `$$x`), the antiquoted
    -- syntax, and an optional kind annotation (as in `$x:term`). We accept only `$x` for an
    -- identifier `x`.
    let target := stx[2]
    unless target.isIdent && stx[1].isNone && stx[3].isNone do
      Macro.throwErrorAt stx "expected a variable name after `$`"
    -- The fresh macro scope makes the identifier hygienic, so it cannot clash with any identifier
    -- written by the user.
    let binder ← withFreshMacroScope `(ident| localValue)
    return (binder.raw, #[(binder, ⟨target⟩)])
  -- Any other node: rewrite its children, collecting their reads from left to right.
  let mut args := #[]
  let mut reads := #[]
  for arg in stx.getArgs do
    let (arg', found) ← extractLocalReads arg
    args := args.push arg'
    reads := reads ++ found
  -- A `choice` node holds the alternative parses of ambiguous syntax. Each alternative would
  -- contribute its own reads, so we reject reads under ambiguity rather than guess.
  if stx.getKind == `choice && !reads.isEmpty then
    Macro.throwErrorAt stx
      "ambiguous Lean syntax containing `$`; write `f <$> x <*> y` for this expression"
  return (stx.setArgs args, reads)

open Lean in
/-- The identifiers occurring in `stx` outside `$`-reads and Lean quotations.

For example, the plain identifiers of `f $x y` are `f` and `y`. They are used to check that no
variable read with `$` also occurs as a plain identifier (see `expandBracedExpr`). -/
private meta partial def plainIdentifiers (stx : Syntax) : Array Ident := Id.run do
  if stx.getKind == `term.pseudo.antiquot || stx.getKind == ``Lean.Parser.Term.quot ||
      stx.getKind == ``Lean.Parser.Term.dynamicQuot ||
      stx.getKind == ``Lean.Parser.Term.precheckedQuot ||
      stx.getKind == ``Lean.Parser.Command.quot || stx.getKind == ``Lean.Parser.Tactic.quot then
    return #[]
  if stx.isIdent then return #[⟨stx⟩]
  let mut found := #[]
  for arg in stx.getArgs do
    found := found ++ plainIdentifiers arg
  return found

open Lean in
/-- Expand the body of a braced Lean computation into a local expression.

The body becomes a Lean function of the values read with `$`, which is applied to the reads with
`LocalSig.Expr.map` and `<*>`. For example, `{f $x $y}` expands to
```
LocalSig.Expr.map (fun (b₁ : LocalSig.Var.Type x) (b₂ : LocalSig.Var.Type y) => f b₁ b₂)
  (LocalSig.Expr.var x) <*> LocalSig.Expr.var y
```
where `b₁` and `b₂` are fresh identifiers, and a body without reads, such as `{3}`, expands to
`LocalSig.Expr.map (fun _ : PUnit => 3) (.val PUnit.unit)`. -/
private meta def expandBracedExpr (stx : Syntax) : MacroM (TSyntax `term) := do
  let (body, reads) ← extractLocalReads stx
  -- Reject a body where a variable read with `$` also occurs as a plain identifier, as in
  -- `{fun x => $x + x}`, where it is easy to confuse which `x` is meant.
  let plain := plainIdentifiers stx
  for (_, target) in reads do
    if plain.any (fun id => id.getId.eraseMacroScopes == target.getId.eraseMacroScopes) then
      Macro.throwErrorAt target
        "a `$` variable also occurs as a plain identifier in this expression; \
         rename the Lean identifier to avoid capturing a local binder"
  let body : TSyntax `term := ⟨body⟩
  let mut result : TSyntax `term ← if reads.isEmpty then
    -- Without reads, the body is a constant: map it over a dummy value.
    `(LocalSig.Expr.map (fun _ : PUnit => $body) (.val PUnit.unit))
  else do
    -- Abstract the body over the fresh identifiers, binding the first read outermost. Each binder
    -- is annotated with the type of the variable read, so the body elaborates with the right types.
    let mut fn := body
    for (binder, target) in reads.toList.reverse do
      fn ← `(fun ($binder : LocalSig.Var.Type $target) => $fn)
    -- Apply the function to the first read with `map`...
    let first := reads[0]!.2
    `(LocalSig.Expr.map $fn (LocalSig.Expr.var $first))
  -- ...and to each remaining read with `<*>`, from left to right.
  for (_, target) in reads.toList.drop 1 do
    result ← `($result <*> LocalSig.Expr.var $target)
  return result

open Lean in
/-- Whether the syntax contains a `$` read outside Lean quotations. This is used to reject reads in
local expressions that are not braced computations (see the `macro_rules` below). -/
private meta partial def hasLocalRead (stx : Syntax) : Bool :=
  if stx.getKind == ``Lean.Parser.Term.quot || stx.getKind == ``Lean.Parser.Term.dynamicQuot ||
      stx.getKind == ``Lean.Parser.Term.precheckedQuot ||
      stx.getKind == ``Lean.Parser.Command.quot || stx.getKind == ``Lean.Parser.Tactic.quot then
    false
  else
    stx.getKind == `term.pseudo.antiquot || stx.getArgs.any hasLocalRead

/- Expansion of `` `(MechExpr| e) ``. A braced computation is expanded by `expandBracedExpr`. Any
other local expression is a term of type `L.Expr α`, which is returned as it is. A `$` read in such
a term is an error: it would otherwise reach Lean's elaborator as an antiquotation outside a
quotation. This covers, for example, `f <$> $x`, and `{$x} + 1`, which parses as a term since it is
longer than the braced form `{$x}`. -/
macro_rules
  | `(`(MechExpr| { $body:term })) => expandBracedExpr body
  | `(`(MechExpr| $e:term)) => do
    if hasLocalRead e then
      Lean.Macro.throwErrorAt e
        "`$` reads are only allowed in a braced computation `{…}` that spans the whole expression"
    return e

end Cslib.Mech
