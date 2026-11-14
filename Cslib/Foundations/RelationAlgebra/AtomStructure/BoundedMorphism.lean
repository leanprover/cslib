/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.AtomStructure

/-!
# Bounded morphisms of atom structures

A *bounded morphism* between atom structures is a map of atoms that preserves converse, preserves
and reflects identity atoms, preserves cycles, and satisfies a "back" condition for cycles. These
are the maps dual to homomorphisms of complex algebras: a bounded morphism `A → B` induces a
homomorphism `ComplexAlgebra B → ComplexAlgebra A` by taking preimages, which is injective when
the bounded morphism is surjective.

## Main definitions

* `Cslib.RelationAlgebra.AtomStructure.BoundedMorphism`: bounded morphisms of atom structures.
* `Cslib.RelationAlgebra.ComplexAlgebra.comap`: the induced homomorphism of complex algebras.

-/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {α β : Type*}

/-- A bounded morphism of atom structures. -/
structure AtomStructure.BoundedMorphism (A : AtomStructure α) (B : AtomStructure β) where
  /-- The underlying function on atoms. -/
  toFun : α → β
  map_conv' (a : α) : toFun (A.conv a) = B.conv (toFun a)
  map_mem_id_iff' {a : α} : toFun a ∈ B.id ↔ a ∈ A.id
  map_cycles' {r s t : α} : (r, s, t) ∈ A.cycles → (toFun r, toFun s, toFun t) ∈ B.cycles
  exists_of_cycles' {r' s' : β} {t : α} : (r', s', toFun t) ∈ B.cycles →
    ∃ r s, toFun r = r' ∧ toFun s = s' ∧ (r, s, t) ∈ A.cycles

namespace AtomStructure.BoundedMorphism

variable {A : AtomStructure α} {B : AtomStructure β}

instance : FunLike (BoundedMorphism A B) α β where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

variable (f : BoundedMorphism A B)

theorem map_conv (a : α) : f (A.conv a) = B.conv (f a) := f.map_conv' a

theorem map_mem_id_iff {a : α} : f a ∈ B.id ↔ a ∈ A.id := f.map_mem_id_iff'

theorem map_cycles {r s t : α} (h : (r, s, t) ∈ A.cycles) : (f r, f s, f t) ∈ B.cycles :=
  f.map_cycles' h

theorem exists_of_cycles {r' s' : β} {t : α} (h : (r', s', f t) ∈ B.cycles) :
    ∃ r s, f r = r' ∧ f s = s' ∧ (r, s, t) ∈ A.cycles :=
  f.exists_of_cycles' h

end AtomStructure.BoundedMorphism

namespace ComplexAlgebra

open AtomStructure

variable {A : AtomStructure α} {B : AtomStructure β}

/-- The homomorphism of complex algebras induced by a bounded morphism of atom structures, sending
a set of atoms to its preimage. -/
def comap (f : BoundedMorphism A B) : RelationAlgebraHom (ComplexAlgebra B) (ComplexAlgebra A) :=
  RelationAlgebraHom.mk' (fun x => ⟨f ⁻¹' x.carrier⟩)
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun x y => by
      ext t
      constructor
      · rintro ⟨r', hr', s', hs', h⟩
        obtain ⟨r, s, rfl, rfl, hrs⟩ := f.exists_of_cycles h
        exact ⟨r, hr', s, hs', hrs⟩
      · rintro ⟨r, hr, s, hs, h⟩
        exact ⟨f r, hr, f s, hs, f.map_cycles h⟩)
    (by ext a; exact f.map_mem_id_iff)
    (fun x => by
      ext a
      rw [mem_star]
      change f a ∈ star x ↔ f (A.conv a) ∈ x
      rw [mem_star, f.map_conv])

@[simp]
theorem mem_comap {f : BoundedMorphism A B} {x : ComplexAlgebra B} {a : α} :
    a ∈ comap f x ↔ f a ∈ x := .rfl

/-- The homomorphism induced by a surjective bounded morphism is injective. -/
theorem comap_injective {f : BoundedMorphism A B} (hf : Function.Surjective f) :
    Function.Injective (comap f) := by
  intro x y hxy
  ext b
  obtain ⟨a, rfl⟩ := hf b
  rw [← mem_comap, hxy, mem_comap]

end ComplexAlgebra

end Cslib.RelationAlgebra
