/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.AtomStructure
public import Cslib.Foundations.RelationAlgebra.Representation
public import Mathlib.Algebra.Group.Basic

/-!
# Group relation algebras

Every group forms an atom structure (and thus a complex algebra) by defining composition as
`X * Y = {f * g | f ∈ X, g ∈ Y}` and inheriting the inverse and (set containing) identity. These
are some of the most common ways of constructing the representation of a relation algebra, so we
also provide a predicate for being representable by a group and the data of the Cayley
representation.

## References

* [Steven Givant, *Introduction to Relation Algebras*][Givant2017a], Sections 3.5, 7.6
* [J. D. Monk, *On representable relation algebras*][Monk1964]

-/

@[expose] public section

universe u

namespace Cslib.RelationAlgebra

namespace AtomStructure

variable {G : Type*} [Group G]

variable (G) in
/-- The atom structure of a group. -/
def ofGroup : AtomStructure G where
  conv g := g⁻¹
  id := {1}
  cycles := {(f, g, h) | f * g = h}
  assoc := by simp +contextual [mul_assoc]
  id_cycle_right := by simp
  exists_id_cycle_right r := by simp
  cycle_left := by simp

@[simp]
theorem ofGroup_conv (g : G) : (ofGroup G).conv g = g⁻¹ := rfl

@[simp]
theorem mem_ofGroup_id {g : G} : g ∈ (ofGroup G).id ↔ g = 1 := .rfl

@[simp]
theorem mem_ofGroup_cycles {f g h : G} : (f, g, h) ∈ (ofGroup G).cycles ↔ f * g = h := .rfl

end AtomStructure

open AtomStructure

namespace ComplexAlgebra

variable {G : Type*} [Group G]

theorem isIntegral_ofGroup : IsIntegral (ComplexAlgebra (ofGroup G)) :=
  (isIntegral_iff _).mpr ⟨1, rfl⟩

variable (G) in
/-- The Cayley representation of the complex algebra of a group. -/
def cayley : RelationAlgebraHom (ComplexAlgebra (ofGroup G)) (SetRel G G) where
  toFun x := {(g, h) | g⁻¹ * h ∈ x}
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl
  map_one' := by ext ⟨_, _⟩; simp [inv_mul_eq_one]
  map_mul' x y := by
    ext ⟨g, h⟩
    refine .trans ?_ (mul_left_surjective g).exists.symm
    simp [mem_mul, ← eq_inv_mul_iff_mul_eq, mul_assoc]
  map_star' x := by ext ⟨_, _⟩; simp

@[simp]
theorem mem_cayley {x : ComplexAlgebra (ofGroup G)} {g h : G} :
    (g, h) ∈ cayley G x ↔ g⁻¹ * h ∈ x := .rfl

theorem cayley_injective : Function.Injective (cayley G) := by
  intro x y hxy
  ext g
  simpa using congrArg ((1, g) ∈ ·) hxy

theorem representable_ofGroup (G : Type u) [Group G] : Representable (ComplexAlgebra (ofGroup G)) :=
  ⟨PUnit, fun _ => G, ⟨.pi fun _ => cayley G, Function.const_injective.comp cayley_injective⟩⟩

end ComplexAlgebra

/-- A relation algebra is `GroupRepresentable` if it embeds into the complex algebra of a group. -/
def GroupRepresentable (α : Type u) [RelationAlgebra α] : Prop :=
  ∃ (G : Type u) (_ : Group G) (f : RelationAlgebraHom α (ComplexAlgebra (ofGroup G))),
    Function.Injective f

namespace GroupRepresentable

variable {α α' : Type u} [RelationAlgebra α] [RelationAlgebra α']

/-- A relation algebra that embeds into an algebra representable over a group is itself
representable over a group. -/
theorem of_injective (f : RelationAlgebraHom α α') (hf : Function.Injective f) :
    GroupRepresentable α' → GroupRepresentable α :=
  fun ⟨G, _, g, hg⟩ => ⟨G, inferInstance, g.comp f, hg.comp hf⟩

/-- A relation algebra representable over a group is representable. -/
theorem representable : GroupRepresentable α → Representable α :=
  fun ⟨G, _, f, hf⟩ => (ComplexAlgebra.representable_ofGroup G).of_injective f hf

/-- A relation algebra representable over a group is integral. -/
theorem isIntegral : GroupRepresentable α → IsIntegral α :=
  fun ⟨_, _, f, hf⟩ => f.isIntegral_of_injective hf ComplexAlgebra.isIntegral_ofGroup

end GroupRepresentable

end Cslib.RelationAlgebra
