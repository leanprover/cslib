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
  __ := Subtype.distribLattice toIsSetRing.union_mem (fun {_ _} ↦ toIsSetRing.inter_mem)
  top := ⟨unit, unit_mem⟩
  bot := ⟨∅, toIsSetRing.empty_mem⟩
  compl R := ⟨unit \ R.val, toIsSetRing.sdiff_mem unit_mem R.property⟩
  sdiff R S := ⟨R.val \ S.val, toIsSetRing.sdiff_mem R.property S.property⟩
  inf_compl_le_bot R := by
    change R.val ∩ (unit \ R.val) ⊆ ∅
    simp
  top_le_sup_compl R := by
    change unit ⊆ R.val ∪ (unit \ R.val)
    rw [Set.union_sdiff_cancel (subset_unit R.property)]
  le_top R := subset_unit R.property
  bot_le _ := Set.empty_subset _
  himp_eq _ _ := rfl
  sdiff_eq R S := by
    apply Subtype.ext
    change R.val \ S.val = R.val ∩ (unit \ S.val)
    rw [← Set.inter_sdiff_assoc, Set.inter_eq_left.mpr (subset_unit R.property)]

instance : Monoid carrier where
  one := ⟨.id, id_mem⟩
  mul R S := ⟨R.val.comp S.val, comp_mem R.property S.property⟩
  mul_assoc R S T := Subtype.ext (SetRel.comp_assoc R.val S.val T.val)
  one_mul R := Subtype.ext (SetRel.id_comp R.val)
  mul_one R := Subtype.ext (SetRel.comp_id R.val)

instance : StarMul carrier where
  star R := ⟨R.val.inv, inv_mem R.property⟩
  star_involutive _ := Subtype.ext SetRel.inv_inv
  star_mul R S := Subtype.ext (SetRel.inv_comp R.val S.val)

instance : RelationAlgebra carrier where
  sup_mul R S T := by
    ext
    exact (exists_congr fun y => or_and_right).trans exists_or
  star_sup _ _ := rfl
  tarski R S := by
    rintro ⟨x, z⟩ ⟨y, hxy, hyz⟩
    use subset_unit (star R * (R * S)ᶜ).property ⟨y, hxy, hyz⟩
    exact fun hxz => hyz.2 ⟨x, hxy, hxz⟩

end ProperRelationAlgebra

end Cslib.RelationAlgebra
