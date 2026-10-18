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

end ProperRelationAlgebra

end Cslib.RelationAlgebra
