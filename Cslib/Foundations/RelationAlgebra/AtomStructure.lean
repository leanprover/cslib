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
be used as an implementation detail for other methods of constructing a relation algebra.

## References

* [Steven Givant, *Advanced Topics in Relation Algebras*][Givant2017]

-/

@[expose] public section

namespace Cslib.RelationAlgebra

/--
The atom structure of a relation algebra in this axiomatic form (rather than as being derived from
an existing instance) so that this can be used to construct a `RelationAlgebra` from its cycles.
-/
class AtomStructure (α : Type*) where
  conv : α → α
  id : Set α
  cycles : Set (α × α × α)
  assoc : (r, q, p) ∈ cycles → (s, t, q) ∈ cycles → ∃ q', (q', t, p) ∈ cycles ∧ (r, s, q') ∈ cycles
  id_cycle : s ∈ id → (r, s, p) ∈ cycles → p = r
  id_exist (r) : ∃ s ∈ id, (r, s, r) ∈ cycles
  conv_cycles : (r, s, t) ∈ cycles → (conv s, conv r, conv t) ∈ cycles
  cycle_left : (r, s, t) ∈ cycles → (conv r, t, s) ∈ cycles

namespace AtomStructure

variable {α : Type*} [AtomStructure α]

@[simp, grind =]
theorem conv_conv (r : α) : conv (conv r) = r := by
  grind [id_cycle, => cycle_left, id_exist r]

theorem conv_eq_self_of_mem_id {r : α} (hr : r ∈ AtomStructure.id) : conv r = r := by
  grind [id_cycle, => cycle_left, id_exist r, conv_cycles]

end AtomStructure

/-- The complex relation algebra of an atom structure. "Complex" here is in the standard but archaic
  sense meaning subset. -/
def ComplexAlgebra (α : Type*) := Set α

namespace ComplexAlgebra

open AtomStructure

variable {α : Type*}

instance : Membership α (ComplexAlgebra α) := inferInstanceAs (Membership α (Set α))

instance : BooleanAlgebra (ComplexAlgebra α) := inferInstanceAs (BooleanAlgebra (Set α))

@[ext]
theorem ext {s t : ComplexAlgebra α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t :=
  Set.ext h

variable [AtomStructure α]

instance : One (ComplexAlgebra α) where
  one := AtomStructure.id

instance : Mul (ComplexAlgebra α) where
  mul x y := {t | ∃ r ∈ x, ∃ s ∈ y, (r, s, t) ∈ cycles}

instance : Star (ComplexAlgebra α) where
  star x := conv '' x

instance : RelationAlgebra (ComplexAlgebra α) where
  mul_assoc a b c := by
    ext p
    constructor
    · rintro ⟨q, ⟨r, hr, s, hs, hrs⟩, t, ht, hqt⟩
      obtain ⟨u, _⟩ := assoc (conv_cycles hqt) (conv_cycles hrs)
      refine ⟨r, hr, conv u, ⟨s, hs, t, ht, ?_⟩, ?_⟩ <;> grind [=> conv_cycles]
    · rintro ⟨r, hr, q, ⟨s, hs, t, ht, hst⟩, hrq⟩
      obtain ⟨u, hut, hrs⟩ := AtomStructure.assoc hrq hst
      exact ⟨u, ⟨r, hr, s, hs, hrs⟩, t, ht, hut⟩
  one_mul x := by
    ext t
    constructor
    · rintro ⟨r, hr, s, hs, h⟩
      have h' := conv_cycles h
      rw [conv_eq_self_of_mem_id hr] at h'
      have heq := Function.Involutive.injective conv_conv (id_cycle hr h')
      grind
    · intro ht
      obtain ⟨s, hs, h⟩ := id_exist (conv t)
      refine ⟨s, hs, t, ht, ?_⟩
      simpa [conv_eq_self_of_mem_id hs] using conv_cycles h
  mul_one x := by
    ext t
    constructor
    · rintro ⟨r, hr, s, hs, h⟩
      grind [id_cycle hs]
    · intro ht
      obtain ⟨s, hs, h⟩ := id_exist t
      exact ⟨t, ht, s, hs, h⟩
  star_involutive := Function.LeftInverse.image_image conv_conv
  star_mul x y := by
    ext t
    constructor
    · rintro ⟨p, ⟨r, hr, s, hs, h⟩, rfl⟩
      exact ⟨conv s, ⟨s, hs, rfl⟩, conv r, ⟨r, hr, rfl⟩, conv_cycles h⟩
    · rintro ⟨s, ⟨s', hs, rfl⟩, r, ⟨r', hr, rfl⟩, h⟩
      refine ⟨conv t, ⟨r', hr, s', hs, ?_⟩, conv_conv t⟩
      simpa using conv_cycles h
  sup_mul a b c := by
    ext t
    exact (exists_congr fun r => or_and_right).trans exists_or
  star_sup a b := Set.image_union conv a b
  tarski x y := by
    rintro t ⟨r, ⟨a, ha, rfl⟩, s, hs, h⟩ ht
    apply hs
    refine ⟨a, ha, t, ht, ?_⟩
    simpa using cycle_left h

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

instance [IsAtomic α] : AtomStructure {a : α // IsAtom a} where
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

noncomputable def complexAlgebraEquiv {α : Type*} [CompleteAtomicRelationAlgebra α] :
    RelationAlgebraEquiv α (ComplexAlgebra {a : α // IsAtom a}) where
  toOrderIso := CompleteAtomicBooleanAlgebra.toSetOfIsAtom
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
      refine ⟨AtomStructure.conv p, ?_, AtomStructure.conv_conv p⟩
      exact (star_mono hp).trans (le_of_eq (star_star x))
    · rintro ⟨a, ha, rfl⟩
      exact star_mono ha

theorem complexAlgebraEquiv_apply {α : Type*} [CompleteAtomicRelationAlgebra α] (x : α) :
    complexAlgebraEquiv x = {a | a.val ≤ x} := rfl

end Cslib.RelationAlgebra
