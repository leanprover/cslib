import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Mathlib.Data.List.Basic

/-!
# String Encoding of Algebraic Types

We define an encoding of non-recursive algebraic types and lists of such types
into strings over the alphabet `{(, ), 1, 2}`.

## Dyadic (bijective base-2) encoding of natural numbers

The dyadic encoding uses digits `1` and `2` (no zero digit):

- `dyadicEnc 0       = ""`
- `dyadicEnc (2k+1)  = dyadicEnc k ++ "1"`
- `dyadicEnc (2k+2)  = dyadicEnc k ++ "2"`

The full encoding of a natural number wraps the dyadic digits in parentheses:
`encNat n = "(" ++ dyadicEnc n ++ ")"`.

## Encoding of non-recursive inductive types

For a type with constructors `c₀, c₁, …, cₘ₋₁` (0-indexed), we define:
```
enc (cᵢ a₁ … aₙ) = "(" ++ encNat i ++ enc a₁ ++ … ++ enc aₙ ++ ")"
```

## Encoding of lists

```
enc l = "(" ++ enc x₁ ++ … ++ enc xₙ ++ ")"
```

## Key property

Every encoded value is enclosed in `()`, and every encodable type has a finite
nesting depth of parentheses. This means an encoded value can be skipped using
finite control only (no separate counter needed).

## Automatic derivation

For any non-recursive inductive type, `deriving StrEnc` automatically generates
the encoding instance following the rules above.
-/

/-! ### Dyadic encoding -/

/-- Dyadic (bijective base-2) encoding of a natural number as a string over `{1, 2}`.

    - `0       ↦ ""`
    - `2k + 1  ↦ dyadicEnc k ++ "1"`
    - `2k + 2  ↦ dyadicEnc k ++ "2"` -/
def dyadicEnc (n : ℕ) : String :=
  match n with
  | 0     => ""
  | n + 1 =>
    let m := n + 1
    if m % 2 = 1 then
      dyadicEnc (m / 2) ++ "1"
    else
      dyadicEnc (m / 2 - 1) ++ "2"
termination_by n
decreasing_by
  · omega
  · omega

/-- Encoding of a natural number: its dyadic representation enclosed in parentheses. -/
def encNat (n : ℕ) : String := "(" ++ dyadicEnc n ++ ")"

/-! #### Sanity checks for dyadic encoding -/

section DyadicExamples

#eval dyadicEnc 0  -- ""
#eval dyadicEnc 1  -- "1"
#eval dyadicEnc 2  -- "2"
#eval dyadicEnc 3  -- "11"
#eval dyadicEnc 4  -- "12"
#eval dyadicEnc 5  -- "21"
#eval dyadicEnc 6  -- "22"

#eval encNat 0  -- "()"
#eval encNat 1  -- "(1)"
#eval encNat 2  -- "(2)"
#eval encNat 3  -- "(11)"

end DyadicExamples

/-! ### Typeclass for string-encodable types -/

/-- Typeclass for types whose values can be encoded as strings over `{(, ), 1, 2}`.
    `depth` is the maximum parenthesis nesting depth of any encoded value.
    `fieldDepths[i][j]` is the depth of the `j`-th field of the `i`-th constructor
    (for types using the constructor-index encoding scheme).
    Set to `#[]` for `ℕ` and `List α`, which use their own encoding schemes. -/
class StrEnc (α : Type*) where
  enc         : α → String
  depth       : ℕ
  /-- For inductive types: `fieldDepths[i][j] = StrEnc.depth` of the `j`-th field
      of the `i`-th constructor.  Empty for `ℕ` and `List`. -/
  fieldDepths : Array (Array ℕ)

/-- Natural numbers are encoded via `encNat`. -/
instance : StrEnc ℕ where
  enc         := encNat
  depth       := 1
  fieldDepths := #[]

/-- Lists are encoded by concatenating the encodings of elements, wrapped in parens. -/
instance instStrEncList [StrEnc α] : StrEnc (List α) where
  enc         l := "(" ++ String.join (l.map StrEnc.enc) ++ ")"
  depth       := StrEnc.depth (α := α) + 1
  fieldDepths := #[]

/-! ### Automatic `deriving StrEnc` for non-recursive inductive types

The handler generates, for each constructor `cᵢ` (0-indexed) with fields `f₀ … fₙ`:
```
enc (cᵢ f₀ … fₙ) = "(" ++ encNat i ++ StrEnc.enc f₀ ++ … ++ StrEnc.enc fₙ ++ ")"
```
`StrEnc` instances for the field types are resolved via typeclass inference.
-/

section StrEncDeriving

open Lean Elab Meta Parser Term Elab.Deriving Elab.Command

/-- Build the match body for the `enc` function of `indVal`.
    For each constructor `cᵢ` (identified by `ctorInfo.cidx`) with fields `f₀ … fₙ`:
    `| cᵢ f₀ … fₙ => "(" ++ encNat i ++ StrEnc.enc f₀ ++ … ++ ")"` -/
private def mkStrEncMatch (header : Header) (indVal : InductiveVal) : TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  let mut alts : Array (TSyntax ``matchAlt) := #[]
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    -- Use simple names x0, x1, … for fields (no fresh-name generation which adds ✝).
    let fieldNames : Array Name := Array.range ctorInfo.numFields |>.map fun i =>
      Name.mkSimple s!"x{i}"
    let fieldIdents : Array (TSyntax `ident) := fieldNames.map mkIdent
    -- Pattern + RHS: use ident* splice so pattern is flat (avoids nested-app rejection)
    let idxLit : Term := Syntax.mkNumLit (toString ctorInfo.cidx)
    let mut rhs : Term ← `("(" ++ encNat $idxLit)
    for fv in fieldIdents do
      rhs ← `($rhs ++ StrEnc.enc $fv)
    rhs ← `($rhs ++ ")")
    alts := alts.push (← `(matchAltExpr| | $(mkIdent ctorName) $fieldIdents:ident* => $rhs))
  `(match $[$discrs],* with $alts:matchAlt*)

/-- Convert a field type `Expr` to a `Term`, substituting type-parameter free variables
    with the names actually used in the instance binder (`paramFVars[i] → paramNames[i]`).
    Runs in `MetaM` so it can be used directly inside `forallBoundedTelescope` callbacks. -/
private partial def exprToFieldTypeTerm
    (paramFVars : Array Expr) (paramNames : Array Name) : Expr → MetaM Term
  | .fvar fvarId => do
    match paramFVars.findIdx? (fun fv => fv.fvarId! == fvarId) with
    | some i => return mkIdent paramNames[i]!
    | none   => throwError "StrEnc depth: unexpected free variable in field type"
  | .const name _ => return mkIdent name   -- strip universe levels (List, Nat, Literal, …)
  | .app f arg => do
    let fTerm   ← exprToFieldTypeTerm paramFVars paramNames f
    let argTerm ← exprToFieldTypeTerm paramFVars paramNames arg
    `($fTerm $argTerm)
  | other =>
    throwError "StrEnc depth: unsupported field type expression {other}"

/-- Build the depth term for one constructor.
    Returns `MetaM Term` so it can be called inside `forallBoundedTelescope`. -/
private def mkCtorDepthTerm
    (ctorInfo : ConstructorVal) (typeParamNames : Array Name) : MetaM Term :=
  Meta.forallBoundedTelescope ctorInfo.type
      (some (ctorInfo.numParams + ctorInfo.numFields)) fun fvars _ => do
    let paramFVars := fvars.extract 0 ctorInfo.numParams
    let fieldFVars := fvars.extract ctorInfo.numParams (ctorInfo.numParams + ctorInfo.numFields)
    let mut acc : Term := Syntax.mkNumLit "1"
    for fv in fieldFVars do
      let fieldTy     ← Meta.inferType fv
      let fieldTyTerm ← exprToFieldTypeTerm paramFVars typeParamNames fieldTy
      acc ← `(Nat.max $acc (StrEnc.depth (α := $fieldTyTerm)))
    `(1 + $acc)

/-- Build a `Term` computing `depth` for the whole inductive type.
    `typeParamNames` must match the binder names in the generated instance. -/
private def mkTypeDepthTerm
    (indVal : InductiveVal) (typeParamNames : Array Name) : TermElabM Term := do
  let depths ← indVal.ctors.mapM fun ctorName => do
    let ctorInfo ← getConstInfoCtor ctorName
    liftMetaM (mkCtorDepthTerm ctorInfo typeParamNames)
  match depths with
  | []      => return Syntax.mkNumLit "0"
  | d :: ds => ds.foldlM (fun acc t => `(Nat.max $acc $t)) d

/-- For one constructor, build an `Array ℕ` term listing the `StrEnc.depth` of each field. -/
private def mkCtorFieldDepthsTerm
    (ctorInfo : ConstructorVal) (typeParamNames : Array Name) : MetaM Term :=
  Meta.forallBoundedTelescope ctorInfo.type
      (some (ctorInfo.numParams + ctorInfo.numFields)) fun fvars _ => do
    let paramFVars := fvars.extract 0 ctorInfo.numParams
    let fieldFVars := fvars.extract ctorInfo.numParams (ctorInfo.numParams + ctorInfo.numFields)
    let fieldTerms : Array Term ← fieldFVars.mapM fun fv => do
      let fieldTy     ← Meta.inferType fv
      let fieldTyTerm ← exprToFieldTypeTerm paramFVars typeParamNames fieldTy
      `(StrEnc.depth (α := $fieldTyTerm))
    `(#[$fieldTerms,*])

/-- Build the `Array (Array ℕ)` term for `fieldDepths` of the whole inductive type. -/
private def mkFieldDepthsTerm
    (indVal : InductiveVal) (typeParamNames : Array Name) : TermElabM Term := do
  let ctorTerms ← indVal.ctors.mapM fun ctorName => do
    let ctorInfo ← getConstInfoCtor ctorName
    liftMetaM (mkCtorFieldDepthsTerm ctorInfo typeParamNames)
  `(#[$(ctorTerms.toArray),*])

/-- Build the auxiliary `enc` function definition for `indVal`. -/
private def mkStrEncAuxFun (ctx : Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal     := ctx.typeInfos[i]!
  let header     ← mkHeader ``StrEnc 1 indVal
  let body       ← mkStrEncMatch header indVal
  `(private def $(mkIdent auxFunName) $header.binders:bracketedBinder* : String := $body)

open TSyntax.Compat in
/-- Build `instance` commands that wire the aux function into the `StrEnc` typeclass. -/
private def mkStrEncInstanceCmds (ctx : Deriving.Context) (typeNames : Array Name) :
    TermElabM (Array Command) := do
  let mut instances := #[]
  for i in [:ctx.typeInfos.size] do
    let indVal := ctx.typeInfos[i]!
    if typeNames.contains indVal.name then
      let auxFunName := ctx.auxFunNames[i]!
      let argNames   ← mkInductArgNames indVal
      let binders    ← mkImplicitBinders argNames
      let binders    := binders ++ (← mkInstImplicitBinders ``StrEnc indVal argNames)
      let indType    ← mkInductiveApp indVal argNames
      let type       ← `(StrEnc $indType)
      -- `mkImplicitBinders` uses `mkFreshUserName`; the resulting binder names (e.g. `α`)
      -- must be reconstructed from `argNames` because we generate instance commands BEFORE
      -- aux-function commands (see `mkStrEncCmds`), so `α` is still fresh here.
      -- NOTE: `mkInductArgNames` returns ONLY type-parameter names (no universe levels),
      -- so `argNames.length = indVal.numParams`; no offset by `levelParams.length` needed.
      let typeParamNames := argNames.extract 0 indVal.numParams
      let depthTerm       ← mkTypeDepthTerm indVal typeParamNames
      let fieldDepthsTerm ← mkFieldDepthsTerm indVal typeParamNames
      let instCmd    ← `(instance $binders:implicitBinder* : $type :=
                           ⟨$(mkIdent auxFunName), $depthTerm, $fieldDepthsTerm⟩)
      instances := instances.push instCmd
  return instances

/-- Gather all commands for deriving `StrEnc` for `indVal`.
    Instance commands are generated FIRST (before aux-function commands use up fresh names
    like `α` via `mkHeader`), so that `mkImplicitBinders` sees a clean name namespace and
    the depth term names match the binder names. The aux-function commands are placed first
    in the output so they are elaborated before the instance that references them. -/
private def mkStrEncCmds (indVal : InductiveVal) (declNames : Array Name) :
    TermElabM (Array Syntax) := do
  let ctx ← mkContext ``StrEnc "strEnc" indVal.name
  let instCmds ← mkStrEncInstanceCmds ctx declNames   -- generated first: names still fresh
  let funCmds  ← Array.range ctx.typeInfos.size |>.mapM (mkStrEncAuxFun ctx)
  return funCmds ++ instCmds  -- aux functions emitted before the instance that uses them

/-- Deriving handler: invoked when a user writes `deriving StrEnc` after an inductive type. -/
private def deriveStrEnc (declNames : Array Name) : CommandElabM Bool := do
  let mut seen : NameSet := {}
  for declName in declNames do
    if seen.contains declName then continue
    let indVal ← getConstInfoInduct declName
    if indVal.isRec then
      logWarning s!"StrEnc: skipping {declName}, which is recursive \
        (use instStrEncList for List)"
      return false
    seen := seen.append (NameSet.ofList indVal.all)
    let cmds ← liftTermElabM <| mkStrEncCmds indVal declNames
    elabCommand <| mkNullNode cmds
  return true

end StrEncDeriving

-- Register handler at *import* time (for files that import this module).
-- Note: `registerDerivingHandler` can only be called during initialization (enforced by
-- Lean 4), so `deriving StrEnc` does not work in the same file where the handler is
-- defined.  Use `derive_StrEnc T` instead (defined below).
open Lean Elab Lean.Elab.Deriving in
initialize registerDerivingHandler ``StrEnc deriveStrEnc

/-- `derive_StrEnc T` directly invokes the StrEnc derivation for the inductive type `T`,
    bypassing `registerDerivingHandler`.  Use this in the same file as the handler
    (where `deriving StrEnc` would give "no handlers implemented"). -/
syntax "derive_StrEnc" ident : command

elab_rules : command
  | `(command| derive_StrEnc $t:ident) => do
    let _ ← deriveStrEnc #[t.getId]

/-! ### SAT-related data types — using `deriving StrEnc` -/

/-- A propositional literal: a variable index tagged as positive or negative.
    Constructor indices (0-based): `pos` = 0, `neg` = 1. -/
inductive Literal : Type where
  | pos : ℕ → Literal   -- positive literal  xₙ
  | neg : ℕ → Literal   -- negative literal ¬xₙ
  deriving Repr
derive_StrEnc Literal

/-- A clause is a disjunction of literals. -/
abbrev Clause    := List Literal

/-- A propositional formula in CNF is a conjunction of clauses. -/
abbrev Formula   := List Clause

/-- An assignment is the list of variable indices assigned `true`. -/
abbrev Assignment := List ℕ

/-- Input to the SAT checker: a formula paired with an assignment.
    Encoded as a single-constructor inductive (constructor index = 0). -/
inductive SATInput : Type where
  | mk : Formula → Assignment → SATInput
  deriving Repr
derive_StrEnc SATInput

-- Clause, Formula, and Assignment inherit StrEnc from the List instance automatically.

/-! #### Verification examples -/

section SATExamples

-- ¬x₁  (neg, index 1; variable 1)  →  ((1)(1))
#eval StrEnc.enc (Literal.neg 1)
-- expected: "((1)(1))"

-- x₂   (pos, index 0; variable 2)  →  (()(2))
#eval StrEnc.enc (Literal.pos 2)
-- expected: "(()(2))"

-- Clause ¬x₁ ∨ x₂ = [neg 1, pos 2]
#eval StrEnc.enc ([Literal.neg 1, Literal.pos 2] : Clause)
-- expected: "(((1)(1))(()(2)))"

-- Formula  (¬x₁ ∨ x₂) ∧ (x₁ ∨ x₃)
#eval StrEnc.enc
  ([[Literal.neg 1, Literal.pos 2], [Literal.pos 1, Literal.pos 3]] : Formula)
-- expected: "((((1)(1))(()(2)))((()(1))(()(11))))"

end SATExamples

/-! #### Example: user-defined type with a type parameter -/

/-- A simple tagged value, to show `deriving StrEnc` works for parametrised types. -/
inductive Tagged (α : Type*) where
  | val  : α → Tagged α          -- constructor index 0
  | pair : (List α) → α → Tagged α     -- constructor index 1
derive_StrEnc Tagged

#eval StrEnc.enc (Tagged.val (42 : ℕ))           -- "(()(42))" ? let's check
#eval StrEnc.enc (Tagged.pair ([1]) (2 : ℕ))  -- "((1)(1)(2))"

/-! ### Basic properties of the encoding -/

/-- Every `encNat` is enclosed in parentheses. -/
theorem encNat_starts_with_paren (n : ℕ) : ∃ s, encNat n = "(" ++ s ++ ")" :=
  ⟨dyadicEnc n, rfl⟩

/-- Every list encoding is enclosed in parentheses. -/
theorem encList_starts_with_paren [StrEnc α] (l : List α) :
    ∃ s, StrEnc.enc l = "(" ++ s ++ ")" :=
  ⟨String.join (l.map StrEnc.enc), rfl⟩

/-- Every `Literal` encoding is enclosed in parentheses. -/
theorem encLiteral_starts_with_paren (lit : Literal) :
    ∃ s, StrEnc.enc lit = "(" ++ s ++ ")" := by
  cases lit with
  | pos n => exact ⟨encNat 0 ++ encNat n, rfl⟩
  | neg n => exact ⟨encNat 1 ++ encNat n, rfl⟩

/-- `dyadicEnc` only uses the characters `1` and `2`. -/
theorem dyadicEnc_chars (n : ℕ) :
    ∀ c ∈ (dyadicEnc n).toList, c = '1' ∨ c = '2' := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c hc
    match n with
    | 0 => simp [dyadicEnc] at hc
    | n + 1 =>
      by_cases h : (n + 1) % 2 = 1
      · -- Odd branch: dyadicEnc (n+1) = dyadicEnc ((n+1)/2) ++ "1"
        -- Use conv_lhs to unfold only the LHS occurrence of dyadicEnc
        have heq : dyadicEnc (n + 1) = dyadicEnc ((n + 1) / 2) ++ "1" := by
          conv_lhs => unfold dyadicEnc; dsimp only
          exact if_pos h
        simp only [heq, String.toList_append, List.mem_append] at hc
        rcases hc with hc | hc
        · exact ih ((n + 1) / 2) (by omega) c hc
        · simp at hc; exact .inl hc
      · -- Even branch: dyadicEnc (n+1) = dyadicEnc ((n+1)/2 - 1) ++ "2"
        have heq : dyadicEnc (n + 1) = dyadicEnc ((n + 1) / 2 - 1) ++ "2" := by
          conv_lhs => unfold dyadicEnc; dsimp only
          exact if_neg h
        simp only [heq, String.toList_append, List.mem_append] at hc
        rcases hc with hc | hc
        · exact ih ((n + 1) / 2 - 1) (by omega) c hc
        · simp at hc; exact .inr hc
