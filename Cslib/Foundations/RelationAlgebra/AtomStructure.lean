/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Hom
public import Mathlib.Order.BooleanAlgebra.Set

/-!
# Atom structures

The relation algebra characterized by its atoms. This has a relatively minimal API as it will mostly
be used for constructing a relation algebra.

## References

* [Steven Givant, *Advanced Topics in Relation Algebras*][Givant2017]

-/

@[expose] public section

namespace Cslib.RelationAlgebra

/--
The atom structure of a relation algebra in this axiomatic form (rather than as being derived from
an existing instance) so that this can be used to construct a `RelationAlgebra` from its cycles.
-/
structure AtomStructure (α : Type*) where
  /-- The converse operation. While this can also be formulated as a relation, it is conveinient to 
    present as a function for stating the cycle rules. -/
  conv : α → α
  /-- The set of identity atoms. -/
  id : Set α
  /-- The set of atom cyles, where (r, s, t) requires that `t ≤ r * s` -/
  cycles : Set (α × α × α)
  assoc : (r, q, p) ∈ cycles → (s, t, q) ∈ cycles → ∃ q', (q', t, p) ∈ cycles ∧ (r, s, q') ∈ cycles
  id_cycle : s ∈ id → (r, s, p) ∈ cycles → p = r
  id_exist (r) : ∃ s ∈ id, (r, s, r) ∈ cycles
  conv_cycles : (r, s, t) ∈ cycles → (conv s, conv r, conv t) ∈ cycles
  cycle_left : (r, s, t) ∈ cycles → (conv r, t, s) ∈ cycles

namespace AtomStructure

variable {α : Type*} (A : AtomStructure α)

@[simp, grind =]
theorem conv_conv (r : α) : A.conv (A.conv r) = r := by
  grind [A.id_cycle, => A.cycle_left, A.id_exist r]

theorem conv_eq_self_of_mem_id {r : α} (hr : r ∈ A.id) : A.conv r = r := by
  grind [A.id_cycle, => A.cycle_left, A.id_exist r, A.conv_cycles]

end AtomStructure

/-- The complex relation algebra of an atom structure. "Complex" here is older sense of subset. -/
structure ComplexAlgebra {α : Type*} (A : AtomStructure α) where
  /-- The underlying set. -/
  carrier : Set α

namespace ComplexAlgebra

variable {α : Type*} (A : AtomStructure α)

/-- Equivalence with the carrier set. -/
def equivSet : ComplexAlgebra A ≃ Set α where
  toFun := carrier
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Membership α (ComplexAlgebra A) := ⟨fun s a => a ∈ s.carrier⟩

instance : BooleanAlgebra (ComplexAlgebra A) := (equivSet A).booleanAlgebra

/-- Order isomorphism with the carrier set. -/
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

instance : RelationAlgebra (ComplexAlgebra A) where
  mul_assoc a b c := by
    ext p
    constructor
    · rintro ⟨q, ⟨r, hr, s, hs, hrs⟩, t, ht, hqt⟩
      obtain ⟨u, _⟩ := A.assoc (A.conv_cycles hqt) (A.conv_cycles hrs)
      refine ⟨r, hr, A.conv u, ⟨s, hs, t, ht, ?_⟩, ?_⟩ <;> grind [=> A.conv_cycles]
    · rintro ⟨r, hr, q, ⟨s, hs, t, ht, hst⟩, hrq⟩
      obtain ⟨u, hut, hrs⟩ := A.assoc hrq hst
      exact ⟨u, ⟨r, hr, s, hs, hrs⟩, t, ht, hut⟩
  one_mul x := by
    ext t
    constructor
    · rintro ⟨r, hr, s, hs, h⟩
      have h' := A.conv_cycles h
      rw [A.conv_eq_self_of_mem_id hr] at h'
      have heq := Function.Involutive.injective A.conv_conv (A.id_cycle hr h')
      grind
    · intro ht
      obtain ⟨s, hs, h⟩ := A.id_exist (A.conv t)
      refine ⟨s, hs, t, ht, ?_⟩
      simpa [A.conv_eq_self_of_mem_id hs] using A.conv_cycles h
  mul_one x := by
    ext t
    constructor
    · rintro ⟨r, hr, s, hs, h⟩
      grind [A.id_cycle hs]
    · intro ht
      obtain ⟨s, hs, h⟩ := A.id_exist t
      exact ⟨t, ht, s, hs, h⟩
  star_involutive x :=
    (equivSet A).injective (Function.LeftInverse.image_image A.conv_conv x.carrier)
  star_mul x y := by
    ext t
    constructor
    · rintro ⟨p, ⟨r, hr, s, hs, h⟩, rfl⟩
      exact ⟨A.conv s, ⟨s, hs, rfl⟩, A.conv r, ⟨r, hr, rfl⟩, A.conv_cycles h⟩
    · rintro ⟨s, ⟨s', hs, rfl⟩, r, ⟨r', hr, rfl⟩, h⟩
      refine ⟨A.conv t, ⟨r', hr, s', hs, ?_⟩, A.conv_conv t⟩
      simpa using A.conv_cycles h
  sup_mul a b c := by
    ext t
    exact (exists_congr fun r => or_and_right).trans exists_or
  star_sup a b := (equivSet A).injective (Set.image_union A.conv a.carrier b.carrier)
  tarski x y := by
    rintro t ⟨r, ⟨a, ha, rfl⟩, s, hs, h⟩ ht
    apply hs
    refine ⟨a, ha, t, ht, ?_⟩
    simpa using A.cycle_left h

end ComplexAlgebra

section Atomic

variable {α : Type*} [RelationAlgebra α]

private theorem exists_atom_le_mul_right [IsAtomic α] {a b p : α} (hp : IsAtom p) (h : p ≤ a * b) :
    ∃ s, IsAtom s ∧ s ≤ b ∧ p ≤ a * s := by
  have hmod : p ≤ a * (b ⊓ star a * p) := by simpa [inf_eq_right.mpr h] using left_modular a b p
  obtain hb | ⟨s, hs, hsb⟩ := eq_bot_or_exists_atom_le (b ⊓ star a * p)
  · rw [hb, mul_bot] at hmod
    exact (hp.ne_bot (le_bot_iff.mp hmod)).elim
  · use s, hs, hsb.trans inf_le_left
    simpa using atom_cycle_left hp hs (hsb.trans inf_le_right)

private theorem exists_atom_le_mul_left [IsAtomic α] {a b p : α} (hp : IsAtom p) (h : p ≤ a * b) :
    ∃ r, IsAtom r ∧ r ≤ a ∧ p ≤ r * b := by
  obtain ⟨s, hs, hsa, hps⟩ :=
    exists_atom_le_mul_right (isAtom_star_iff.mpr hp) (by simpa using star_mono h)
  exact ⟨star s, isAtom_star_iff.mpr hs, by simpa using star_mono hsa, by simpa using star_mono hps⟩

/-- The atom structure formed by the atoms of an atomic relation algebra. -/
def atomStructure (α : Type*) [RelationAlgebra α] [IsAtomic α] :
    AtomStructure {a : α // IsAtom a} where
  conv a := ⟨star a.val, isAtom_star_iff.mpr a.property⟩
  id := {a | a.val ≤ 1}
  cycles := Set.ofPred fun (r, s, t) => t.val ≤ r.val * s.val
  assoc {r q p s t} h₁ h₂ := by
    have hp : (p : α) ≤ r * s * t := by
      rw [mul_assoc]
      exact h₁.trans (mul_mono le_rfl h₂)
    obtain ⟨q', hq', hq'rs, hpq'⟩ := exists_atom_le_mul_left p.property hp
    aesop
  id_cycle {s r p} hs h := by
    ext
    apply (r.property.le_iff_eq p.property.ne_bot).mp
    simpa using h.trans (mul_mono le_rfl hs)
  id_exist r := by
    obtain ⟨s, hs, hs1, hrs⟩ := exists_atom_le_mul_right r.property (le_of_eq (mul_one r.val).symm)
    aesop
  conv_cycles {r s t} h := by
    change star t.val ≤ star s.val * star r.val
    simpa using star_mono h
  cycle_left {r s t} h := atom_cycle_left s.property t.property h

end Atomic

/-- The isomorphism between a relation algebra and its atoms. -/
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
      exact h.trans (mul_mono hr hs)
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
