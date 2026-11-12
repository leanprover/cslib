/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Hom
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.BooleanAlgebra.Set

/-!
# Atom structures

This module defines atom structures and their complex relation algebras. It also constructs the
atom structure of an atomic relation algebra and reconstructs a complete atomic relation algebra
from its atom structure.

## References

* [Steven Givant, *Advanced Topics in Relation Algebras*][Givant2017b]

-/

@[expose] public section

namespace Cslib.RelationAlgebra

/--
An axiomatic atom structure, used to construct a `RelationAlgebra` from its cycles.
-/
structure AtomStructure (α : Type*) where
  /-- The converse operation, presented as a function for stating the cycle rules. -/
  conv : α → α
  /-- The set of identity atoms. -/
  id : Set α
  /-- The set of atom cycles, where `(r, s, t)` represents `t ≤ r * s`. -/
  cycles : Set (α × α × α)
  assoc : (r, q, p) ∈ cycles → (s, t, q) ∈ cycles → ∃ q', (q', t, p) ∈ cycles ∧ (r, s, q') ∈ cycles
  id_cycle_right : s ∈ id → (r, s, p) ∈ cycles → p = r
  exists_id_cycle_right (r) : ∃ s ∈ id, (r, s, r) ∈ cycles
  cycle_left : (r, s, t) ∈ cycles → (conv r, t, s) ∈ cycles

namespace AtomStructure

variable {α : Type*} (A : AtomStructure α)

@[simp, grind =]
theorem conv_conv (r : α) : A.conv (A.conv r) = r := by
  grind [A.id_cycle_right, => A.cycle_left, A.exists_id_cycle_right r]

theorem conv_cycles {r s t : α} (h : (r, s, t) ∈ A.cycles) :
    (A.conv s, A.conv r, A.conv t) ∈ A.cycles := by
  obtain ⟨e, he, hs⟩ := A.exists_id_cycle_right s
  obtain ⟨q, hq, hsq⟩ := A.assoc (A.cycle_left hs) (A.cycle_left h)
  grind [A.id_cycle_right he (A.cycle_left hq)]

theorem assoc_symm {r s t p q : α} (h₁ : (q, t, p) ∈ A.cycles) (h₂ : (r, s, q) ∈ A.cycles) :
    ∃ q', (r, q', p) ∈ A.cycles ∧ (s, t, q') ∈ A.cycles := by
  obtain ⟨u, hu₁, hu₂⟩ := A.assoc (A.conv_cycles h₁) (A.conv_cycles h₂)
  exact ⟨A.conv u, by simpa using A.conv_cycles hu₁, by simpa using A.conv_cycles hu₂⟩

theorem conv_eq_self_of_mem_id {r : α} (hr : r ∈ A.id) : A.conv r = r := by
  grind [A.id_cycle_right, => A.cycle_left, A.exists_id_cycle_right r, A.conv_cycles]

theorem id_cycle_left {s r p : α} (hs : s ∈ A.id) (h : (s, r, p) ∈ A.cycles) : p = r :=
  Function.Involutive.injective A.conv_conv <|
    A.id_cycle_right hs (A.conv_eq_self_of_mem_id hs ▸ A.conv_cycles h)

theorem exists_id_cycle_left (r : α) : ∃ s ∈ A.id, (s, r, r) ∈ A.cycles := by
  obtain ⟨s, hs, h⟩ := A.exists_id_cycle_right (A.conv r)
  exact ⟨s, hs, by simpa [A.conv_eq_self_of_mem_id hs] using A.conv_cycles h⟩

end AtomStructure

/-- The complex relation algebra of an atom structure. "Complex" here means a subset of atoms. -/
structure ComplexAlgebra {α : Type*} (A : AtomStructure α) where
  /-- The underlying set. -/
  carrier : Set α

namespace ComplexAlgebra

variable {α : Type*} (A : AtomStructure α)

/-- Equivalence with the powerset of the atom type. -/
def equivSet : ComplexAlgebra A ≃ Set α where
  toFun := carrier
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Membership α (ComplexAlgebra A) := ⟨fun s a => a ∈ s.carrier⟩

instance : CompleteAtomicBooleanAlgebra (ComplexAlgebra A) :=
  (equivSet A).completeAtomicBooleanAlgebra

instance [Finite α] : Finite (ComplexAlgebra A) := Finite.of_equiv (Set α) (equivSet A).symm

/-- Order isomorphism with the powerset of the atom type. -/
def orderIsoSet : ComplexAlgebra A ≃o Set α where
  toEquiv := equivSet A
  map_rel_iff' := Iff.rfl

@[ext]
theorem ext {s t : ComplexAlgebra A} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t :=
  (equivSet A).injective (Set.ext h)

instance : One (ComplexAlgebra A) where
  one := ⟨A.id⟩

instance : Mul (ComplexAlgebra A) where
  mul x y := ⟨{t | ∃ r ∈ x, ∃ s ∈ y, (r, s, t) ∈ A.cycles}⟩

instance : Star (ComplexAlgebra A) where
  star x := ⟨A.conv '' x.carrier⟩

section

variable {A} {x y : ComplexAlgebra A} {a : α}

@[simp]
theorem mem_mk {s : Set α} : a ∈ (⟨s⟩ : ComplexAlgebra A) ↔ a ∈ s := .rfl

theorem mem_carrier : a ∈ x.carrier ↔ a ∈ x := .rfl

theorem le_def : x ≤ y ↔ ∀ a ∈ x, a ∈ y := .rfl

@[simp, grind =]
theorem mem_sup : a ∈ x ⊔ y ↔ a ∈ x ∨ a ∈ y := .rfl

@[simp, grind =]
theorem mem_compl : a ∈ xᶜ ↔ a ∉ x := .rfl

@[simp, grind =]
theorem mem_one : a ∈ (1 : ComplexAlgebra A) ↔ a ∈ A.id := .rfl

@[grind =]
theorem mem_mul : a ∈ x * y ↔ ∃ r ∈ x, ∃ s ∈ y, (r, s, a) ∈ A.cycles := .rfl

@[simp, grind =]
theorem mem_star : a ∈ star x ↔ A.conv a ∈ x :=
  Set.mem_image_iff_of_inverse A.conv_conv A.conv_conv

end

instance : RelationAlgebra (ComplexAlgebra A) where
  mul_assoc a b c := by ext p; grind [A.assoc, A.assoc_symm]
  one_mul x := by ext t; grind [A.id_cycle_left, A.exists_id_cycle_left t]
  mul_one x := by ext t; grind [A.id_cycle_right, A.exists_id_cycle_right t]
  star_involutive x := by ext; simp
  star_mul x y := by ext; grind [=> A.conv_cycles]
  sup_mul a b c := by ext; grind
  star_sup a b := by ext; simp
  tarski x y := by grind [le_def, => A.cycle_left]

instance : CompleteAtomicRelationAlgebra (ComplexAlgebra A) where

/-- A complex algebra is integral exactly when its identity set is a singleton. -/
theorem isIntegral_iff : IsIntegral (ComplexAlgebra A) ↔ ∃ a, A.id = {a} :=
  ((orderIsoSet A).isAtom_iff (1 : ComplexAlgebra A)).symm.trans Set.isAtom_iff

end ComplexAlgebra

/-- The atom structure formed by the atoms of an atomic relation algebra. -/
def atomStructure (α : Type*) [RelationAlgebra α] [IsAtomic α] :
    AtomStructure {a : α // IsAtom a} where
  conv a := ⟨star a.val, isAtom_star_iff.mpr a.property⟩
  id := {a | a.val ≤ 1}
  cycles := Set.ofPred fun (r, s, t) => t.val ≤ r.val * s.val
  assoc {r q p s t} h₁ h₂ := by
    have hp : (p : α) ≤ r * s * t := by
      rw [mul_assoc]
      exact h₁.trans (mul_le_mul_right h₂ _)
    obtain ⟨q', hq', hq'rs, hpq'⟩ := exists_atom_le_mul_left p.property hp
    exact ⟨⟨q', hq'⟩, hpq', hq'rs⟩
  id_cycle_right {s r p} hs h := by
    ext
    apply (r.property.le_iff_eq p.property.ne_bot).mp
    simpa using h.trans (mul_le_mul_right hs _)
  exists_id_cycle_right r := by
    obtain ⟨s, hs, hs1, hrs⟩ := exists_atom_le_mul_right r.property (le_of_eq (mul_one r.val).symm)
    exact ⟨⟨s, hs⟩, hs1, hrs⟩
  cycle_left {r s t} h := atom_cycle_left s.property t.property.ne_bot h

/-- The isomorphism from a complete atomic relation algebra to the complex algebra of its
atom structure. -/
noncomputable def complexAlgebraEquiv {α : Type*} [CompleteAtomicRelationAlgebra α] :
    RelationAlgebraEquiv α (ComplexAlgebra (atomStructure α)) where
  toOrderIso := CompleteAtomicBooleanAlgebra.toSetOfIsAtom.trans
    (ComplexAlgebra.orderIsoSet (atomStructure α)).symm
  map_mul' x y := by
    ext p
    constructor
    · intro hp
      obtain ⟨r, hr, hrx, hpr⟩ := exists_atom_le_mul_left p.property hp
      obtain ⟨s, hs, hsy, hps⟩ := exists_atom_le_mul_right p.property hpr
      exact ⟨⟨r, hr⟩, hrx, ⟨s, hs⟩, hsy, hps⟩
    · rintro ⟨r, hr, s, hs, h⟩
      exact h.trans (mul_le_mul' hr hs)
  map_star' x := by
    ext p
    constructor
    · intro hp
      refine ⟨(atomStructure α).conv p, ?_, (atomStructure α).conv_conv p⟩
      exact (star_mono hp).trans (le_of_eq (star_star x))
    · rintro ⟨a, ha, rfl⟩
      exact star_mono ha

theorem complexAlgebraEquiv_apply {α : Type*} [CompleteAtomicRelationAlgebra α] (x : α) :
    complexAlgebraEquiv x = ⟨{a | a.val ≤ x}⟩ := rfl

end Cslib.RelationAlgebra
