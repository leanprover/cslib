/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Basic
public import Mathlib.Order.BooleanAlgebra.Set

/-!
# Atom structures

The relation algebra characterized by its atoms. This has a relatively minimal API as it will mostly
be used as an implementation detail for other methods of constructing a relation algebra.

## References

* Steven Givant, *Advanced Topics in Relation Algebras* (2017)

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

end Cslib.RelationAlgebra
