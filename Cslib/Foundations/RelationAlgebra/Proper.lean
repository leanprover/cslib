/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Representation
public import Mathlib.MeasureTheory.SetSemiring

/-!
# Proper relation algebras

The carrier of a proper relation algebra inherits a `RelationAlgebra` structure, with Boolean
top given by its unit and complements taken relative to that unit.

`ProperRepresentation` packages an injective morphism into a proper relation algebra.
`Representation.toProper` converts a product representation using the disjoint union of its bases.
`ProperRepresentation.toRepresentation` restricts to the equivalence classes of the unit, indexed
by base points. These conversions preserve injectivity and allow empty bases. The latter indexing
can repeat classes, so the conversions need not recover the original indexing of a product.
The membership lemmas at the end recover the original relations after either round trip.
`Representation.properEquiv` gives an equivalence with proper representations on a fixed disjoint
union, whose inverse retains the original summand indexing.

-/

@[expose] public section

universe u v w

namespace Cslib.RelationAlgebra

/-- A ring of relations bounded by `unit`, containing the unit and identity, and closed under
converse and composition. -/
class ProperRelationAlgebra {α : Type u} (carrier : Set (SetRel α α))
    (unit : outParam (SetRel α α)) : Prop extends MeasureTheory.IsSetRing carrier where
  subset_unit {R} : R ∈ carrier → R ⊆ unit
  unit_mem : unit ∈ carrier
  id_mem : .id ∈ carrier
  inv_mem {R} : R ∈ carrier → R.inv ∈ carrier
  comp_mem {R S} : R ∈ carrier → S ∈ carrier → R.comp S ∈ carrier

namespace ProperRelationAlgebra

variable {α : Type u} {carrier : Set (SetRel α α)} {unit : SetRel α α}
  [ProperRelationAlgebra carrier unit]

instance : BooleanAlgebra carrier where
  __ := Subtype.distribLattice toIsSetRing.union_mem @toIsSetRing.inter_mem
  top := ⟨unit, unit_mem⟩
  bot := ⟨∅, toIsSetRing.empty_mem⟩
  compl R := ⟨unit \ R.val, toIsSetRing.sdiff_mem unit_mem R.property⟩
  sdiff R S := ⟨R.val \ S.val, toIsSetRing.sdiff_mem R.property S.property⟩
  inf_compl_le_bot _ := Set.disjoint_sdiff_right.le_bot
  top_le_sup_compl _ := le_sup_sdiff (α := SetRel α α)
  le_top R := subset_unit R.property
  bot_le _ := Set.empty_subset _
  sdiff_eq R S := by
    ext
    exact ⟨fun ⟨hR, hS⟩ => ⟨hR, subset_unit R.property hR, hS⟩, fun ⟨hR, _, hS⟩ => ⟨hR, hS⟩⟩

instance : Monoid carrier where
  one := ⟨.id, id_mem⟩
  mul R S := ⟨R.val.comp S.val, comp_mem R.property S.property⟩
  mul_assoc _ _ _ := Subtype.ext (SetRel.comp_assoc ..)
  one_mul _ := Subtype.ext (SetRel.id_comp _)
  mul_one _ := Subtype.ext (SetRel.comp_id _)

instance : StarMul carrier where
  star R := ⟨R.val.inv, inv_mem R.property⟩
  star_involutive _ := rfl
  star_mul _ _ := Subtype.ext (SetRel.inv_comp ..)

instance : RelationAlgebra carrier where
  sup_mul R S T := by
    ext
    exact (exists_congr fun y => or_and_right).trans exists_or
  star_sup _ _ := rfl
  tarski R S := by
    rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩
    use subset_unit (star R * (R * S)ᶜ).property ⟨y, hxy, hyz⟩
    exact fun hxz => hyz.2 ⟨x, hxy, hxz⟩

include carrier in
/-- The unit of a proper relation algebra is reflexive. -/
theorem unit_refl (x : α) : (x, x) ∈ unit :=
  subset_unit (carrier := carrier) id_mem rfl

include carrier in
/-- The unit of a proper relation algebra is symmetric. -/
theorem unit_symm {x y : α} (h : (x, y) ∈ unit) : (y, x) ∈ unit :=
  subset_unit (carrier := carrier) (inv_mem unit_mem) h

include carrier in
/-- The unit of a proper relation algebra is transitive. -/
theorem unit_trans {x y z : α} (hxy : (x, y) ∈ unit) (hyz : (y, z) ∈ unit) :
    (x, z) ∈ unit :=
  subset_unit (carrier := carrier) (comp_mem unit_mem unit_mem) ⟨y, hxy, hyz⟩

/-- Restrict each relation to every equivalence class of the unit, indexed by a point in that class.
This indexing may repeat classes, but requires neither quotients nor chosen representatives. -/
def toProductHom :
    RelationAlgebraHom carrier (∀ x : α, SquareRelations {y // (x, y) ∈ unit}) where
  toFun R _ := {p | (p.1.val, p.2.val) ∈ R.val}
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := by
    funext x
    apply Set.eq_univ_of_forall
    intro ⟨y, z⟩
    exact unit_trans (carrier := carrier) (unit_symm (carrier := carrier) y.property) z.property
  map_bot' := rfl
  map_one' := by
    funext x
    apply Set.ext
    intro ⟨y, z⟩
    exact Subtype.val_inj
  map_mul' R S := by
    funext x
    apply Set.ext
    intro ⟨y, z⟩
    constructor
    · rintro ⟨w, hyw, hwz⟩
      exact ⟨⟨w, unit_trans (carrier := carrier) y.property (subset_unit R.property hyw)⟩, hyw, hwz⟩
    · rintro ⟨w, hyw, hwz⟩
      exact ⟨w.val, hyw, hwz⟩
  map_star' _ := rfl

/-- Restriction to all unit-equivalence classes distinguishes relations in the carrier. -/
theorem toProductHom_injective : Function.Injective (toProductHom (carrier := carrier)) := by
  intro R S h
  apply Subtype.ext
  apply Set.ext
  intro ⟨x, y⟩
  have hxy (hy : (x, y) ∈ unit) : (x, y) ∈ R.val ↔ (x, y) ∈ S.val :=
    Set.ext_iff.mp (congrFun h x) (⟨x, unit_refl (carrier := carrier) x⟩, ⟨y, hy⟩)
  exact ⟨fun hr => (hxy (subset_unit R.property hr)).mp hr,
    fun hs => (hxy (subset_unit S.property hs)).mpr hs⟩

end ProperRelationAlgebra

namespace SquareRelations

variable {ι : Type v} (β : ι → Type w)

/-- Pairs in the same summand of a disjoint union. -/
def sumUnit : SetRel (Σ i, β i) (Σ i, β i) := {(⟨a, _⟩, ⟨b, _⟩) | a = b}

/-- Relations between points in the same summand of a disjoint union. -/
def sumCarrier : Set (SetRel (Σ i, β i) (Σ i, β i)) := {R | R ⊆ sumUnit β}

instance : ProperRelationAlgebra (sumCarrier β) (sumUnit β) where
  empty_mem := Set.empty_subset _
  union_mem _ _ hR hS := Set.union_subset hR hS
  sdiff_mem _ _ hR _ := Set.Subset.trans Set.sdiff_subset hR
  subset_unit hR := hR
  unit_mem := Set.Subset.rfl
  id_mem := by rintro ⟨x, y⟩ rfl; rfl
  inv_mem hR := fun _ hxy => (hR hxy).symm
  comp_mem hR hS := by
    rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩
    exact (hR hxy).trans (hS hyz)

/-- Assemble a family of relations as a relation on the disjoint union. -/
def sumRel (R : ∀ i, SetRel (β i) (β i)) : SetRel (Σ i, β i) (Σ i, β i) :=
  {(⟨a, ia⟩, ⟨b, ib⟩) | ∃ h : b = a, (ia, h ▸ ib) ∈ R a}

@[simp]
theorem mem_sumRel (R : ∀ i, SetRel (β i) (β i)) (i : ι) (x y : β i) :
    (⟨i, x⟩, ⟨i, y⟩) ∈ sumRel β R ↔ (x, y) ∈ R i := by
  simp [sumRel]

/-- Restricting relations on a disjoint union to its summands is an equivalence with the product
of square relation algebras. -/
def sumEquiv : RelationAlgebraEquiv (sumCarrier β) (∀ i, SquareRelations (β i)) where
  toFun R i := {p | (⟨i, p.1⟩, ⟨i, p.2⟩) ∈ R.val}
  invFun R := ⟨sumRel β R, fun _ ⟨h, _⟩ => h.symm⟩
  left_inv R := by
    apply Subtype.ext
    ext ⟨⟨i, x⟩, ⟨j, y⟩⟩
    constructor
    · rintro ⟨h, hR⟩
      subst j
      exact hR
    · intro h
      have hij : i = j := R.property h
      subst j
      exact ⟨rfl, h⟩
  right_inv R := by
    funext i
    apply Set.ext
    rintro ⟨x, y⟩
    exact mem_sumRel β R i x y
  map_rel_iff' := by
    intro R S
    constructor
    · intro h ⟨⟨i, x⟩, ⟨j, y⟩⟩ hR
      have hij : i = j := R.property hR
      subst j
      exact h i (a := (x, y)) hR
    · intro h i p hp
      exact h hp
  map_mul' R S := by
    funext i
    ext ⟨x, z⟩
    constructor
    · rintro ⟨⟨j, y⟩, hxy, hyz⟩
      have hij : i = j := R.property hxy
      subst j
      exact ⟨y, hxy, hyz⟩
    · rintro ⟨y, hxy, hyz⟩
      exact ⟨⟨i, y⟩, hxy, hyz⟩
  map_star' _ := rfl

end SquareRelations

/-- A representation by an injective morphism into a proper relation algebra. -/
structure ProperRepresentation (α : Type u) [RelationAlgebra α] {β : Type v}
    (carrier : Set (SetRel β β)) {unit : SetRel β β} [ProperRelationAlgebra carrier unit] where
  /-- The morphism into the carrier of the proper relation algebra. -/
  hom : RelationAlgebraHom α carrier
  /-- Distinct algebra elements are represented by distinct relations. -/
  injective : Function.Injective hom

/-- Convert a product representation to a proper representation on the disjoint union of its bases.
The unit relates exactly those points belonging to the same summand. -/
def Representation.toProper {α : Type u} [RelationAlgebra α] {ι : Type v} {β : ι → Type w}
    (ρ : Representation α ι β) : ProperRepresentation α (SquareRelations.sumCarrier β) where
  hom := (SquareRelations.sumEquiv β).symm.toHom.comp ρ.hom
  injective := (SquareRelations.sumEquiv β).symm.injective.comp ρ.injective

/-- Convert a proper representation to a product representation by restricting to the equivalence
classes of its unit, indexed by their base points. -/
def ProperRepresentation.toRepresentation {α : Type u} [RelationAlgebra α] {β : Type v}
    {carrier : Set (SetRel β β)} {unit : SetRel β β} [ProperRelationAlgebra carrier unit]
    (ρ : ProperRepresentation α carrier) :
    Representation α β (fun x => {y // (x, y) ∈ unit}) where
  hom := ProperRelationAlgebra.toProductHom.comp ρ.hom
  injective := ProperRelationAlgebra.toProductHom_injective.comp ρ.injective

/-- Converting a product representation to a proper representation and back recovers each
original relation in every copy of its factor, indexed by an anchor `x`. -/
@[simp]
theorem Representation.mem_toProper_toRepresentation
    {α : Type u} [RelationAlgebra α] {ι : Type v} {β : ι → Type w}
    (ρ : Representation α ι β) (a : α) (i : ι) (x y z : β i) :
    (⟨⟨i, y⟩, rfl⟩, ⟨⟨i, z⟩, rfl⟩) ∈
      (show SetRel _ _ from ρ.toProper.toRepresentation.hom a ⟨i, x⟩) ↔
      (y, z) ∈ (show SetRel _ _ from ρ.hom a i) :=
  SquareRelations.mem_sumRel β (ρ.hom a) i y z

/-- Converting a proper representation to a product representation and back recovers each
original relation on pairs in the unit, using the class indexed by the first endpoint. -/
@[simp]
theorem ProperRepresentation.mem_toRepresentation_toProper
    {α : Type u} [RelationAlgebra α] {β : Type v}
    {carrier : Set (SetRel β β)} {unit : SetRel β β} [ProperRelationAlgebra carrier unit]
    (ρ : ProperRepresentation α carrier) (a : α) (x y : β) (hxy : (x, y) ∈ unit) :
    (⟨x, ⟨x, ProperRelationAlgebra.unit_refl (carrier := carrier) x⟩⟩,
      ⟨x, ⟨y, hxy⟩⟩) ∈ (ρ.toRepresentation.toProper.hom a).val ↔
      (x, y) ∈ (ρ.hom a).val :=
  SquareRelations.mem_sumRel (fun x => {y // (x, y) ∈ unit}) (ρ.toRepresentation.hom a) x _ _

/-- Product representations correspond exactly to proper representations on the same disjoint
union of bases. The forward map is `toProper`; the inverse restricts to the original summands,
whereas `ProperRepresentation.toRepresentation` indexes the unit classes by all base points. -/
def Representation.properEquiv {α : Type u} [RelationAlgebra α] {ι : Type v} {β : ι → Type w} :
    Representation α ι β ≃ ProperRepresentation α (SquareRelations.sumCarrier β) where
  toFun := Representation.toProper
  invFun ρ :=
    { hom := (SquareRelations.sumEquiv β).toHom.comp ρ.hom
      injective := (SquareRelations.sumEquiv β).injective.comp ρ.injective }
  left_inv ρ := by
    cases ρ with
    | mk hom injective =>
      dsimp [Representation.toProper]
      congr 1
      exact RelationAlgebraHom.ext fun a => (SquareRelations.sumEquiv β).right_inv (hom a)
  right_inv ρ := by
    cases ρ with
    | mk hom injective =>
      dsimp [Representation.toProper]
      congr 1
      exact RelationAlgebraHom.ext fun a => (SquareRelations.sumEquiv β).left_inv (hom a)

end Cslib.RelationAlgebra
