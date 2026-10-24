/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.AtomStructure
public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.DeriveFintype

public meta import Mathlib.Data.Finset.Fold
public meta import Mathlib.Data.Fintype.Sigma
public meta import Mathlib.Data.Fintype.Sum
public meta import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Integral atom structures

In the case of integral relation algebras with a single identity atom, we provide a method for
automatically constructing the algebra from its cycles. This implementation is mildly optimized by
translating into a natural number encoding, which scales to the point of four to five atoms.

## References

* Peter Jipsen, [*List of small integral relation algebras*](https://www1.chapman.edu/~jipsen/gap/ramaddux.html)

-/

@[expose] public section

namespace Cslib.RelationAlgebra

/--
The atoms of an integral atom structure: the identity atom, `s` symmetric diversity (non-identity)
atoms, and `n` pairs of nonsymmetric atoms.
-/
inductive IntegralAtom (s n : ℕ) where
  /-- The identity atom. -/
  | one
  /-- A symmetric diversity atom. -/
  | symm (i : Fin s)
  /-- A nonsymmetric atom. `nsymm i true` is the converse of `nsymm i false`. -/
  | nsymm (i : Fin n) (conv : Bool)
  deriving DecidableEq, Fintype

namespace IntegralAtom

variable {s n : ℕ}

/-- The converse of an atom, where just nonsymmetric atoms are flipped. -/
def conv : IntegralAtom s n → IntegralAtom s n
  | one => one
  | symm i => symm i
  | nsymm i b => nsymm i (!b)

abbrev Cycle (s n : ℕ) := IntegralAtom s n × IntegralAtom s n × IntegralAtom s n

def cycleOrbit : Cycle s n → Finset (Cycle s n)
  | (r, u, t) =>
    {(r, u, t), (conv u, conv r, conv t), (conv r, t, u),
      (conv t, r, conv u), (u, conv t, conv r), (t, conv u, r)}

def cycleClosure (generators : Finset (Cycle s n)) : Finset (Cycle s n) :=
  (generators ∪ Finset.univ.image (fun a => (one, a, a))).biUnion cycleOrbit

@[simp, grind =]
theorem conv_one : conv (one : IntegralAtom s n) = one := rfl

@[simp, grind =]
theorem conv_conv (a : IntegralAtom s n) : conv (conv a) = a := by
  cases a <;> simp [conv]

theorem cycleOrbit_conv_cycles {c : Cycle s n} {r u t : IntegralAtom s n}
    (h : (r, u, t) ∈ cycleOrbit c) : (conv u, conv r, conv t) ∈ cycleOrbit c := by
  simp only [cycleOrbit, Finset.mem_insert] at *
  grind

theorem cycleOrbit_cycle_left {c : Cycle s n} {r u t : IntegralAtom s n}
    (h : (r, u, t) ∈ cycleOrbit c) : (conv r, t, u) ∈ cycleOrbit c := by
  simp only [cycleOrbit, Finset.mem_insert] at *
  grind

theorem cycleClosure_id_exist (g : Finset (Cycle s n)) (r : IntegralAtom s n) :
    (r, one, r) ∈ cycleClosure g := by
  apply Finset.mem_biUnion.mpr
  use (one, conv r, conv r)
  simp [cycleOrbit]

theorem cycleClosure_conv_cycles (g : Finset (Cycle s n)) {r u t : IntegralAtom s n}
    (h : (r, u, t) ∈ cycleClosure g) :
    (conv u, conv r, conv t) ∈ cycleClosure g := by
  obtain ⟨c, hc, h⟩ := Finset.mem_biUnion.mp h
  exact Finset.mem_biUnion.mpr ⟨c, hc, cycleOrbit_conv_cycles h⟩

theorem cycleClosure_cycle_left (g : Finset (Cycle s n)) {r u t : IntegralAtom s n}
    (h : (r, u, t) ∈ cycleClosure g) : (conv r, t, u) ∈ cycleClosure g := by
  obtain ⟨c, hc, h⟩ := Finset.mem_biUnion.mp h
  exact Finset.mem_biUnion.mpr ⟨c, hc, cycleOrbit_cycle_left h⟩

theorem cycleClosure_id_cycle (g : Finset (Cycle s n))
    (hg : ∀ c ∈ g, let (r, u, t) := c; r ≠ one ∧ u ≠ one ∧ t ≠ one)
    {r p : IntegralAtom s n} (h : (r, one, p) ∈ cycleClosure g) : p = r := by
  obtain ⟨c, hc, h⟩ := Finset.mem_biUnion.mp h
  simp [cycleOrbit] at h
  grind [conv_conv, conv_one]

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

def cycleIndex : Cycle s n ↪ ℕ where
  toFun := fun (r, u, t) =>
    ((atomIndex r : ℕ) * (1 + s + 2 * n) + atomIndex u) * (1 + s + 2 * n) + atomIndex t
  inj' := by
    rintro ⟨r, u, t⟩ ⟨r', u', t'⟩ h
    obtain ⟨h, ht⟩ := Prod.mk.inj ((Nat.divModEquiv _).symm.injective h)
    obtain ⟨hr, hu⟩ := Prod.mk.inj ((Nat.divModEquiv _).symm.injective h)
    ext
    · exact atomIndex_injective (Fin.val_injective hr)
    · exact atomIndex_injective hu
    · exact atomIndex_injective ht

def maskOfFinset {α : Type*} (code : α → ℕ) (xs : Finset α) : ℕ := xs.fold (· ||| ·) 0 (2 ^ code ·)

theorem testBit_maskOfFinset_iff {α : Type*} (code : α → ℕ) (xs : Finset α) (i : ℕ) :
    (maskOfFinset code xs).testBit i = true ↔ ∃ a ∈ xs, code a = i := by
  unfold maskOfFinset
  rw [Finset.fold_op_rel_iff_or (r := fun i => (Nat.testBit · i))] <;> grind

theorem testBit_maskOfFinset {α : Type*} (code : α → ℕ) (hinj : Function.Injective code)
    (xs : Finset α) (a : α) :
    (maskOfFinset code xs).testBit (code a) = true ↔ a ∈ xs := by
  rw [testBit_maskOfFinset_iff]
  simp [hinj.eq_iff]

theorem maskOfFinset_biUnion {α β : Type*} [DecidableEq β]
    (code : β → ℕ) (xs : Finset α) (f : α → Finset β) :
    maskOfFinset code (xs.biUnion f) =
      xs.fold (β := ℕ) (· ||| ·) 0 (fun a => maskOfFinset code (f a)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [Finset.fold_op_rel_iff_or (r := fun i => (Nat.testBit · i))] <;>
    grind [testBit_maskOfFinset_iff]

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
    exact (testBit_maskOfFinset cycleIndex cycleIndex.injective
      (cycleClosure generators) (r, u, t)).symm
  · intro r u i hi
    obtain ⟨a, ha⟩ := atomIndex_surjective ⟨i, lt_of_maskRow_testBit hi⟩
    exact ⟨a, congrArg Fin.val ha⟩

def ofCycles (generators : Finset (Cycle s n)) (mask : ℕ)
    (hmask : maskOfFinset cycleIndex (cycleClosure generators) = mask)
    (hcheck : checkRows (α := IntegralAtom s n) conv
      (fun r u => maskRow mask (1 + s + 2 * n) (atomIndex r) (atomIndex u)))
    (hg : ∀ c ∈ generators, let (r, u, t) := c; r ≠ one ∧ u ≠ one ∧ t ≠ one) :
    AtomStructure (IntegralAtom s n) where
  conv := conv
  id := {one}
  cycles := cycleClosure generators
  assoc := cycleClosure_assoc_of_checkRows generators mask hmask hcheck
  id_cycle := by rintro _ _ _ rfl; exact cycleClosure_id_cycle _ hg
  id_exist r := ⟨one, rfl, cycleClosure_id_exist _ r⟩
  conv_cycles := cycleClosure_conv_cycles _
  cycle_left := cycleClosure_cycle_left _

public meta section

open Lean Elab Term Meta Parser Tactic

structure IntegralCyclesConfig where
  symm : Array Name := #[]
  nonsymm : Array Name := #[]

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
  option nonsymm := fun cfg item => return { cfg with nonsymm := ← elabIntegralCycleNames item }

syntax (name := integralCycles) "integral_cycles%" optConfig
  ("(" ident ("~")? "," ident ("~")? "," ident ("~")? ")")* : term

private def IntegralCyclesConfig.atomExpr (config : IntegralCyclesConfig)
    (ref : Ident) (isConverse : Bool) :
    TermElabM (IntegralAtom config.symm.size config.nonsymm.size × Expr) := do
  let name := ref.getId.eraseMacroScopes
  let s := mkNatLit config.symm.size
  let n := mkNatLit config.nonsymm.size
  if let some i := config.symm.findFinIdx? (· == name) then
    return (.symm i, mkApp3 (mkConst ``IntegralAtom.symm) s n (toExpr i))
  if let some i := config.nonsymm.findFinIdx? (· == name) then
    return (.nsymm i isConverse,
      mkApp4 (mkConst ``IntegralAtom.nsymm) s n (toExpr i) (toExpr isConverse))
  throwErrorAt ref "undeclared atom '{name}'"

set_option compiler.relaxedMetaCheck true in
@[no_expose, term_elab integralCycles]
def elabIntegralCycles : TermElab := fun stx expectedType? => do
  let `(integral_cycles% $cfg:optConfig $[($r $[~%$rc]?, $s $[~%$sc]?, $t $[~%$tc]?)]*) := stx
    | throwUnsupportedSyntax
  let config ← elabIntegralCyclesConfig cfg (logExceptions := false)
  let mut cycleTerms : Array Expr := #[]
  let mut generators : Finset (Cycle config.symm.size config.nonsymm.size) := ∅
  for r in r, rc in rc, s in s, sc in sc, t in t, tc in tc do
    let (rAtom, r) ← config.atomExpr r rc.isSome
    let (sAtom, s) ← config.atomExpr s sc.isSome
    let (tAtom, t) ← config.atomExpr t tc.isSome
    generators := insert (rAtom, sAtom, tAtom) generators
    cycleTerms := cycleTerms.push (← mkAppM ``Prod.mk #[r, ← mkAppM ``Prod.mk #[s, t]])
  let s := mkNatLit config.symm.size
  let n := mkNatLit config.nonsymm.size
  let mask := mkNatLit (maskOfFinset cycleIndex (cycleClosure generators))
  let mut cycles := mkApp (mkConst ``Finset.empty [Level.zero]) (mkApp2 (mkConst ``Cycle) s n)
  for c in cycleTerms.reverse do cycles ← mkAppM ``Insert.insert #[c, cycles]
  withoutErrToSorry <| withSynthesize do
    let mut result := mkAppN (mkConst ``ofCycles)
      #[mkNatLit config.symm.size, mkNatLit config.nonsymm.size, cycles, mask]
    for i in [:3] do
      let type ← whnf (← inferType result)
      let .forallE _ prop _ _ := type | throwError "expected a certificate"
      let proof ← if i == 0 then
        elabTermEnsuringType (← `(by rw [cycleClosure, maskOfFinset_biUnion]; decide)) prop
      else
        mkDecideProof prop
      result := mkApp result proof
    ensureHasType expectedType? result

end

namespace IdentityOnly

def entry1 : AtomStructure (IntegralAtom 0 0) := integral_cycles%

end IdentityOnly

namespace OneSymm

def entry1 : AtomStructure (IntegralAtom 1 0) :=
  integral_cycles% (symm := a)

def entry2 : AtomStructure (IntegralAtom 1 0) :=
  integral_cycles% (symm := a) (a, a, a)

end OneSymm

namespace OneConv

def entry1 : AtomStructure (IntegralAtom 0 1) :=
  integral_cycles% (nonsymm := a) (a, a, a)

def entry2 : AtomStructure (IntegralAtom 0 1) :=
  integral_cycles% (nonsymm := a) (a, a, a~)

def entry3 : AtomStructure (IntegralAtom 0 1) :=
  integral_cycles% (nonsymm := a) (a, a, a~) (a, a, a)

end OneConv

namespace TwoSymm

def entry1 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, b, b)

def entry2 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, b, b) (a, a, a)

def entry3 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, b, b) (b, b, b)

def entry4 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, b, b) (a, a, a) (b, b, b)

def entry5 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, a, b) (a, b, b)

def entry6 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, a, b) (a, b, b) (a, a, a)

def entry7 : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, a, b) (a, b, b) (a, a, a) (b, b, b)

end TwoSymm

namespace OneSymmOneConv

def entry1 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, b, b~)

def entry2 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, b, b) (a, b~, b~) (b, b, b~)

def entry3 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, b, b) (a, b~, b~) (b, b, b~) (a, a, a)

def entry4 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, b, b) (a, b, b~) (a, b~, b~) (a, a, a)

def entry5 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (b, b, b~)

def entry6 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (b, b, b~) (a, a, a)

def entry7 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~) (a, a, a)

def entry8 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~) (b, b, b~)

def entry9 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~) (b, b, b~)
    (a, a, a)

def entry10 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, b, b~) (b, b, b~) (b, b, b)

def entry11 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, b, b) (a, b~, b~) (b, b, b)

def entry12 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, b, b) (a, b~, b~) (a, a, a) (b, b, b)

def entry13 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, b, b) (a, b~, b~) (b, b, b~) (b, b, b)

def entry14 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, b, b) (a, b~, b~) (b, b, b~) (a, a, a) (b, b, b)

def entry15 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, b, b) (a, b, b~) (a, b~, b~) (a, a, a) (b, b, b)

def entry16 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, b, b) (a, b, b~) (a, b~, b~) (b, b, b~) (a, a, a)
    (b, b, b)

def entry17 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (b, b, b)

def entry18 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, a, a) (b, b, b)

def entry19 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (b, b, b~) (b, b, b)

def entry20 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (b, b, b~) (a, a, a) (b, b, b)

def entry21 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b~) (b, b, b)

def entry22 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b~) (a, a, a) (b, b, b)

def entry23 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b~) (b, b, b~) (b, b, b)

def entry24 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b~) (b, b, b~) (a, a, a) (b, b, b)

def entry25 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b~, b~) (a, a, a) (b, b, b)

def entry26 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b~) (a, b~, b~) (b, b, b)

def entry27 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b~) (a, b~, b~) (a, a, a) (b, b, b)

def entry28 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b~) (a, b~, b~) (b, b, b~) (b, b, b)

def entry29 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b~) (a, b~, b~) (b, b, b~) (a, a, a)
    (b, b, b)

def entry30 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b) (a, b~, b~) (b, b, b)

def entry31 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b) (a, b~, b~) (a, a, a) (b, b, b)

def entry32 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b) (a, b~, b~) (b, b, b~) (b, b, b)

def entry33 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b) (a, b~, b~) (b, b, b~) (a, a, a)
    (b, b, b)

def entry34 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~) (b, b, b)

def entry35 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~) (a, a, a)
    (b, b, b)

def entry36 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~) (b, b, b~)
    (b, b, b)

def entry37 : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nonsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~) (b, b, b~)
    (a, a, a) (b, b, b)

end OneSymmOneConv

namespace ThreeSymm

def entry1 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, c)

def entry2 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, c) (b, c, c) (b, b, b)

def entry3 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, c) (b, b, c) (b, c, c) (b, b, b) (c, c, c)

def entry4 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, c) (a, c, c) (b, c, c) (a, a, a) (b, b, b) (c, c, c)

def entry5 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, c) (a, c, c) (b, b, c) (b, c, c) (a, a, a) (c, c, c)

def entry6 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, c) (a, c, c) (b, b, c) (b, c, c) (a, a, a) (b, b, b)
    (c, c, c)

def entry7 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, c) (b, b, c) (c, c, c)

def entry8 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, c) (a, c, c) (b, b, c) (b, c, c) (c, c, c)

def entry9 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, c) (a, c, c) (b, b, c) (b, c, c) (a, a, a)
    (c, c, c)

def entry10 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, c) (a, c, c) (b, b, c) (b, c, c) (a, a, a)
    (b, b, b) (c, c, c)

def entry11 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c)

def entry12 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (a, a, a)

def entry13 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (b, b, b)

def entry14 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (a, a, a) (b, b, b)

def entry15 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (c, c, c)

def entry16 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (a, a, a) (c, c, c)

def entry17 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (b, b, b) (c, c, c)

def entry18 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (a, a, a) (b, b, b) (c, c, c)

def entry19 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, b, c) (a, c, c) (b, c, c) (a, a, a) (b, b, b)

def entry20 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, b, c) (a, c, c) (b, c, c) (a, a, a) (b, b, b)
    (c, c, c)

def entry21 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, b, c) (b, c, c)

def entry22 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, b, c) (b, c, c) (a, a, a)

def entry23 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, b, c) (b, c, c) (b, b, b)

def entry24 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, b, c) (b, c, c) (a, a, a) (b, b, b)

def entry25 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, b, c) (b, c, c) (b, b, b) (c, c, c)

def entry26 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, b, c) (b, c, c) (a, a, a) (b, b, b)
    (c, c, c)

def entry27 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c) (a, a, a)

def entry28 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c) (a, a, a)
    (b, b, b)

def entry29 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c) (a, a, a)
    (b, b, b) (c, c, c)

def entry30 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, c, c)

def entry31 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, c, c) (a, a, a)

def entry32 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, c, c) (a, a, a) (b, b, b)

def entry33 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, c, c) (a, a, a) (b, b, b)
    (c, c, c)

def entry34 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c)

def entry35 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c) (a, a, a)

def entry36 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c) (b, b, b)

def entry37 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c) (a, a, a)
    (b, b, b)

def entry38 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c) (c, c, c)

def entry39 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c) (a, a, a)
    (c, c, c)

def entry40 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c) (b, b, b)
    (c, c, c)

def entry41 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c) (a, a, a)
    (b, b, b) (c, c, c)

def entry42 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, c, c) (b, b, c)

def entry43 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (a, a, a)

def entry44 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (b, b, b)

def entry45 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (a, a, a) (b, b, b)

def entry46 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (a, a, a) (c, c, c)

def entry47 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (a, a, a) (b, b, b)
    (c, c, c)

def entry48 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (a, a, a)
    (c, c, c)

def entry49 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (a, a, a)
    (b, b, b) (c, c, c)

def entry50 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c)

def entry51 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c)
    (a, a, a)

def entry52 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c)
    (b, b, b)

def entry53 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c)
    (a, a, a) (b, b, b)

def entry54 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c)
    (c, c, c)

def entry55 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c)
    (a, a, a) (c, c, c)

def entry56 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c)
    (b, b, b) (c, c, c)

def entry57 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c)
    (a, a, a) (b, b, b) (c, c, c)

def entry58 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (b, c, c)

def entry59 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (b, c, c)
    (a, a, a)

def entry60 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (b, c, c)
    (a, a, a) (b, b, b)

def entry61 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (b, c, c)
    (a, a, a) (b, b, b) (c, c, c)

def entry62 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
    (b, c, c)

def entry63 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
    (b, c, c) (a, a, a)

def entry64 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
    (b, c, c) (a, a, a) (b, b, b)

def entry65 : AtomStructure (IntegralAtom 3 0) :=
  integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
    (b, c, c) (a, a, a) (b, b, b) (c, c, c)

end ThreeSymm

end IntegralAtom

end Cslib.RelationAlgebra
