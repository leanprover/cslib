/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
public import Mathlib.Combinatorics.Colex

public meta import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure
public meta import Mathlib.Combinatorics.Colex
public meta import Mathlib.Data.Finset.Fold
public meta import Mathlib.Data.Fintype.Sigma
public meta import Mathlib.Data.Fintype.Sum
public meta import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Constructing integral atom structures from cycles

This module provides an elaborator `integral_cycles%` for constructing small integral relation
algebras. This is mildly optimized using a bitmask encoding to check associativity that scales
to roughly four to five atoms.

-/

@[expose] public meta section

namespace Cslib.RelationAlgebra
namespace IntegralAtom

variable {s n : ℕ}

/-- A natural number indexing of integral atoms. -/
def atomIndex : IntegralAtom s n → Fin (1 + s + 2 * n)
  | .one => ⟨0, by lia⟩
  | .symm i => ⟨i + 1, by lia⟩
  | .nsymm i b => ⟨1 + s + 2 * i + b.toNat, by grind [Bool.toNat]⟩

theorem atomIndex_injective : Function.Injective (@atomIndex s n) := by
  intro a b h
  cases a <;> cases b <;> grind [atomIndex, Bool.toNat]

theorem atomIndex_surjective : Function.Surjective (@atomIndex s n) := by
  rintro ⟨i, hi⟩
  rcases i with _ | i
  · exact ⟨.one, rfl⟩
  by_cases his : i < s
  · exact ⟨.symm ⟨i, his⟩, rfl⟩
  refine ⟨.nsymm ⟨(i - s) / 2, by lia⟩ (decide ((i - s) % 2 = 1)), ?_⟩
  grind [atomIndex, Bool.toNat]

/-- The embedding from cycles to natural numbers. -/
def cycleIndex : Cycle s n ↪ ℕ where
  toFun := fun (r, u, t) =>
    (atomIndex r * (1 + s + 2 * n) + atomIndex u) * (1 + s + 2 * n) + atomIndex t
  inj' := by
    rintro ⟨r, u, t⟩ ⟨r', u', t'⟩ h
    obtain ⟨h, ht⟩ := Prod.mk.inj ((Nat.divModEquiv _).symm.injective h)
    obtain ⟨hr, hu⟩ := Prod.mk.inj ((Nat.divModEquiv _).symm.injective h)
    ext
    · exact atomIndex_injective (Fin.val_injective hr)
    · exact atomIndex_injective hu
    · exact atomIndex_injective ht

/-- Encode a finset using `Finset.equivBitIndices` on its image under `code`. -/
def maskOfFinset {α : Type*} (code : α → ℕ) (xs : Finset α) : ℕ :=
  Finset.equivBitIndices.symm (xs.image code)

theorem testBit_maskOfFinset_iff {α : Type*} (code : α → ℕ) (xs : Finset α) (i : ℕ) :
    (maskOfFinset code xs).testBit i = true ↔ ∃ a ∈ xs, code a = i := by
  simp [maskOfFinset, ← Nat.mem_bitIndices, ← List.mem_toFinset]

theorem maskOfFinset_biUnion {α β : Type*} [DecidableEq β]
    (code : β → ℕ) (xs : Finset α) (f : α → Finset β) :
    maskOfFinset code (xs.biUnion f) =
      xs.fold (β := ℕ) (· ||| ·) 0 (fun a => maskOfFinset code (f a)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [Finset.fold_op_rel_iff_or (r := fun i => (Nat.testBit · i))] <;>
    grind [testBit_maskOfFinset_iff]

/-- An equivalent characterization of associativity using bitmasks. -/
def checkRows {α : Type*} [Fintype α] (conv : α → α) (row : α → α → Nat) : Bool :=
  Finset.univ.inf fun r =>
    Finset.univ.inf fun s =>
      Finset.univ.inf fun t =>
        Finset.univ.inf fun p =>
          (row (conv r) p &&& row s t == 0) || (row p (conv t) &&& row r s != 0)

theorem assoc_of_checkRows {α : Type*} [Fintype α] (cycles : Set (α × α × α))
    (conv : α → α) (row : α → α → Nat) (encode : α → Nat)
    (hconv : ∀ a, conv (conv a) = a)
    (hleft : ∀ {r s t}, (r, s, t) ∈ cycles → (conv r, t, s) ∈ cycles)
    (hright : ∀ {r s t}, (r, s, t) ∈ cycles → (t, conv s, r) ∈ cycles)
    (hrow : ∀ r s t, (r, s, t) ∈ cycles ↔ (row r s).testBit (encode t))
    (hbits : ∀ r s i, (row r s).testBit i → ∃ t, encode t = i)
    (hcheck : checkRows conv row) :
    ∀ {r q p s t}, (r, q, p) ∈ cycles → (s, t, q) ∈ cycles →
      ∃ q', (q', t, p) ∈ cycles ∧ (r, s, q') ∈ cycles := by
  intro r q p s t hrq hst
  have : (row (conv r) p &&& row s t).testBit (encode q) := by grind
  have : row (conv r) p &&& row s t ≠ 0 := by grind
  have : row p (conv t) &&& row r s ≠ 0 := by
    simp only [checkRows, ← top_eq_true, Finset.inf_eq_top_iff] at hcheck
    grind
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero this
  grind

/-- Extract particular bits from the encoding. -/
def maskRow (mask count r s : Nat) : Nat :=
  (mask >>> ((r * count + s) * count)) &&& (2 ^ count - 1)

theorem maskRow_testBit (mask count r s i : Nat) (hi : i < count) :
    (maskRow mask count r s).testBit i = mask.testBit ((r * count + s) * count + i) := by
  simp [maskRow, decide_eq_true hi]

theorem lt_of_maskRow_testBit {mask count r s i : Nat} (h : (maskRow mask count r s).testBit i) :
    i < count := by
  grind [maskRow]

theorem cycleClosure_assoc_of_checkRows (generators : Finset (Cycle s n)) (mask : ℕ)
    (hmask : maskOfFinset cycleIndex (cycleClosure generators) = mask)
    (hcheck : checkRows (α := IntegralAtom s n) conv
      (fun r u => maskRow mask (1 + s + 2 * n) (atomIndex r) (atomIndex u))) :
    ∀ {r q p u t}, (r, q, p) ∈ cycleClosure generators →
      (u, t, q) ∈ cycleClosure generators →
      ∃ q', (q', t, p) ∈ cycleClosure generators ∧
        (r, u, q') ∈ cycleClosure generators := by
  intro r q p u t hr hq
  apply assoc_of_checkRows _ conv _ (Fin.val ∘ atomIndex) conv_conv
    (cycleClosure_cycle_left generators) _ _ _ hcheck hr hq
  · intro r u t h
    simpa using
      cycleClosure_conv_cycles _ (cycleClosure_cycle_left _ (cycleClosure_conv_cycles _ h))
  · intro r u t
    rw [Function.comp_apply, maskRow_testBit _ _ _ _ _ (atomIndex t).is_lt, ← hmask]
    change (r, u, t) ∈ cycleClosure generators ↔
      (maskOfFinset cycleIndex (cycleClosure generators)).testBit (cycleIndex (r, u, t))
    simp [testBit_maskOfFinset_iff]
  · intro r u i hi
    obtain ⟨a, ha⟩ := atomIndex_surjective ⟨i, lt_of_maskRow_testBit hi⟩
    exact ⟨a, congrArg Fin.val ha⟩

open Lean Elab Term Meta Parser Tactic

/-- Options for `integral_cycles%`. -/
structure IntegralCyclesConfig where
  /-- Names of symmetric diversity atoms. -/
  symm : Array Name := #[]
  /-- Names of one representative from each pair of nonsymmetric atoms. -/
  nsymm : Array Name := #[]

/-- Elaborate an atom name. -/
private def elabIntegralCycleNames (item : ConfigEval.ConfigItem) : TermElabM (Array Name) := do
  item.checkNotBool
  match item.value with
  | `($name:ident) => return #[name.getId.eraseMacroScopes]
  | `([$names,*]) => names.getElems.mapM fun name => do
      unless name.raw.isIdent do throwErrorAt name "expected an atom name"
      return name.raw.getId.eraseMacroScopes
  | value => ConfigEval.evalTermOrExprWithElab ⟨value⟩

private declare_term_config_elab elabIntegralCyclesConfig IntegralCyclesConfig where
  option symm := fun cfg item => return { cfg with symm := ← elabIntegralCycleNames item }
  option nsymm := fun cfg item => return { cfg with nsymm := ← elabIntegralCycleNames item }

/--
The `integral_cycles%` term elaborator constructs an integral atom structure from cycle generators.
You must specify symmetric diversity atoms with `(symm := [a, ...])` and one representative of each
pair of nonsymmetric atoms with `(nsymm := [b, ...])`. Either may be omitted and for single atoms
`(symm := a)` is also accepted. All atom names must be distinct across both options.

After these options, list cycles as space-separated  triples with `(r, s, t)` for `t ≤ r * s`,
and use postfix `~` for converse. Only diversity atoms appear in these triples: the elaborator
inserts all identity cycles automatically and calculates the closure.

The elaborator checks the atom-structure axioms and returns an `AtomStructure (IntegralAtom s n)`,
where `s` and `n` are the lengths of the two lists. Its `ComplexAlgebra` has a `RelationAlgebra`
instance. For example:

```lean
example : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nsymm := b) (a, b, b~)
```
-/
syntax (name := integralCycles) "integral_cycles%" optConfig
  ("(" ident ("~")? "," ident ("~")? "," ident ("~")? ")")* : term

/-- Elaborate an `IntegralAtom` from `integral_cycles%`. -/
private def IntegralCyclesConfig.atomExpr (config : IntegralCyclesConfig)
    (ref : Ident) (isConverse : Bool) :
    TermElabM (IntegralAtom config.symm.size config.nsymm.size × Expr) := do
  let name := ref.getId.eraseMacroScopes
  let s := mkNatLit config.symm.size
  let n := mkNatLit config.nsymm.size
  if let some i := config.symm.findFinIdx? (· == name) then
    return (.symm i, mkApp3 (mkConst ``IntegralAtom.symm) s n (toExpr i))
  if let some i := config.nsymm.findFinIdx? (· == name) then
    return (.nsymm i isConverse,
      mkApp4 (mkConst ``IntegralAtom.nsymm) s n (toExpr i) (toExpr isConverse))
  throwErrorAt ref "undeclared atom '{name}'"

/-- Elaborate a theorem's next proof argument, reporting a stage-specific failure. -/
private def elabIntegralCyclesProof (f : Expr) (proof : Term)
    (errorMessage : MessageData) : TermElabM Expr := do
  let .forallE _ prop _ _ ← whnf (← inferType f) |
    throwError "internal error in `integral_cycles%`: unexpected proof handling"
  let saved ← Term.saveState
  try
    withSynthesize <| elabTermEnsuringType proof prop
  catch
    | .error .. =>
      saved.restore (restoreInfo := true)
      throwError errorMessage
    | ex => throw ex

/-- Elaborate `integral_cycles%`. -/
@[no_expose, term_elab integralCycles]
def elabIntegralCycles : TermElab := fun stx expectedType? => do
  let `(integral_cycles% $cfg:optConfig $[($r $[~%$rc]?, $s $[~%$sc]?, $t $[~%$tc]?)]*) := stx
    | throwUnsupportedSyntax
  let config ← elabIntegralCyclesConfig cfg (logExceptions := false)
  let mut names : NameSet := ∅
  for name in config.symm ++ config.nsymm do
    if names.contains name then throwErrorAt cfg "duplicate atom name '{name}'"
    names := names.insert name
  let mut cycleTerms : Array Expr := #[]
  let mut generators : Finset (Cycle config.symm.size config.nsymm.size) := ∅
  for r in r, rc in rc, s in s, sc in sc, t in t, tc in tc do
    let (rAtom, r) ← config.atomExpr r rc.isSome
    let (sAtom, s) ← config.atomExpr s sc.isSome
    let (tAtom, t) ← config.atomExpr t tc.isSome
    generators := insert (rAtom, sAtom, tAtom) generators
    cycleTerms := cycleTerms.push (← mkAppM ``Prod.mk #[r, ← mkAppM ``Prod.mk #[s, t]])
  let s := mkNatLit config.symm.size
  let n := mkNatLit config.nsymm.size
  let mask := mkNatLit (maskOfFinset cycleIndex (cycleClosure generators))
  let mut cycles := mkApp (mkConst ``Finset.empty [Level.zero]) (mkApp2 (mkConst ``Cycle) s n)
  for c in cycleTerms.reverse do cycles ← mkAppM ``Insert.insert #[c, cycles]
  withoutErrToSorry <| withSynthesize do
    let assoc := mkAppN (mkConst ``cycleClosure_assoc_of_checkRows) #[s, n, cycles, mask]
    let hmask ← elabIntegralCyclesProof assoc
      (← `((maskOfFinset_biUnion _ _ _).trans (by decide +kernel)))
      "internal error in `integral_cycles%`: failed to verify the cycle encoding"
    let hcheck ← elabIntegralCyclesProof (mkApp assoc hmask) (← `(by decide +kernel))
      "`integral_cycles%` could not prove associativity of the generated cycles"
    let hassoc := mkApp2 assoc hmask hcheck
    let result := mkAppN (mkConst ``ofCycles) #[s, n, cycles, hassoc]
    let hdiversity ← elabIntegralCyclesProof result (← `(by decide +kernel))
      "`integral_cycles%` could not prove that all generators are diversity cycles"
    ensureHasType expectedType? (mkApp result hdiversity)

end IntegralAtom

end Cslib.RelationAlgebra
