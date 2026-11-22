/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Order.AlgebraIntervals
public import Cslib.Foundations.RelationAlgebra.Basic
public import Mathlib.Order.FixedPoints

/-! # Element properties for relation algebras

This file defines the notion of reflexive (`Cslib.RelationAlgebra.IsRelRefl`), symmetric
(`Cslib.RelationAlgebra.IsRelSymm`) and transitive (`Cslib.RelationAlgebra.IsRelTrans`) elements
in a relation algebra. These properties are packaged as typeclasses, so that instance syntheses
can find `RelationAlgebra (Set.Iic a)` for `a` a symmetric and transitive element in a relation
algebra (see `Set.Iic.instRelationAlgebra` in `RelationAlgebra/Relativization.lean`).

## References

- [S. Givant, *Introduction to Relation Algebras: Relation Algebras, Volume 1*][Givant2017a],
chapter 5.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {α β : Type*} {a b c : α}

/-- A reflexive element of a relation algebra. -/
class IsRelRefl [One α] [LE α] (a : α) : Prop where
  protected one_le : 1 ≤ a

/-- A symmetric element of a relation algebra. Note that this is a class version of Mathlib's
`IsSelfAdjoint`. -/
class IsRelSymm [Star α] (a : α) : Prop where
  protected star_eq : star a = a

/-- A transitive element of a relation algebra. -/
class IsRelTrans [Mul α] [LE α] (a : α) : Prop where
  protected mul_self_le : a * a ≤ a

/-- A reflexive element is above the identity. -/
lemma one_le_of_refl [One α] [LE α] (a : α) [IsRelRefl a] : 1 ≤ a := IsRelRefl.one_le

instance instIsRelReflMap [One α] [LE α] [One β] [LE β] (F : Type*) [FunLike F α β]
    [OrderHomClass F α β] [OneHomClass F α β] (f : F) (a : α) [IsRelRefl a] : IsRelRefl (f a) where
  one_le := map_one f ▸ RelHomClass.map_rel f (one_le_of_refl a)

lemma isRelRefl_iff [One α] [LE α] {a : α} : IsRelRefl a ↔ 1 ≤ a :=
  ⟨@IsRelRefl.one_le _ _ _ a, IsRelRefl.mk⟩

/-- A symmetric element is equal to its `star`. -/
lemma star_eq_of_symm [Star α] (a : α) [IsRelSymm a] : star a = a := IsRelSymm.star_eq

lemma isRelSymm_iff [Star α] {a : α} : IsRelSymm a ↔ star a = a :=
  ⟨@IsRelSymm.star_eq _ _ a, IsRelSymm.mk⟩

instance instIsRelSymmMap [Star α] [Star β] (F : Type*) [FunLike F α β] [StarHomClass F α β]
    (f : F) (a : α) [IsRelSymm a] : IsRelSymm (f a) where
  star_eq := by rw [← map_star f, star_eq_of_symm]

/-- For a transitive element `a`, `a * a ≤ a`. -/
lemma mul_self_le_of_trans [Mul α] [LE α] (a : α) [IsRelTrans a] : a * a ≤ a :=
  IsRelTrans.mul_self_le

lemma isRelTrans_iff [Mul α] [LE α] {a : α} : IsRelTrans a ↔ a * a ≤ a :=
  ⟨@IsRelTrans.mul_self_le _ _ _ a, IsRelTrans.mk⟩

instance instIsRelTransMap [Mul α] [LE α] [Mul β] [LE β] (F : Type*) [FunLike F α β]
  [OrderHomClass F α β] [MulHomClass F α β] (f : F) (a : α) [IsRelTrans a] : IsRelTrans (f a) where
  mul_self_le := map_mul f a a ▸ RelHomClass.map_rel f (mul_self_le_of_trans a)

variable [RelationAlgebra α]

/-! ### Reflexive elements -/

instance : IsRelRefl (1 : α) where
  one_le := le_rfl

instance : IsRelRefl (⊤ : α) where
  one_le := le_top

instance [IsRelRefl a] : IsRelRefl (star a) where
  one_le := by simpa [le_star_iff] using one_le_of_refl a

lemma le_mul_left [hb : IsRelRefl b] : a ≤ b * a := by
  nth_grw 1 [← one_mul a, one_le_of_refl b]

lemma le_mul_right [hb : IsRelRefl b] : a ≤ a * b := by
  nth_grw 1 [← mul_one a, one_le_of_refl b]

/-- The relation-algebra equivalent of `Relation.ReflGen`. -/
def reflGen (a : α) : α := 1 ⊔ a

instance : IsRelRefl (reflGen a) where
  one_le := le_sup_left

lemma le_reflGen : a ≤ reflGen a := le_sup_right

lemma reflGen_le [hb : IsRelRefl b] : reflGen a ≤ b ↔ a ≤ b := by
  simp [reflGen, one_le_of_refl b]

/-! ### Symmetric elements -/

instance : IsRelSymm (⊥ : α) where
  star_eq := star_bot

instance : IsRelSymm (1 : α) where
  star_eq := star_one α

instance : IsRelSymm (⊤ : α) where
  star_eq := star_top

instance [IsRelSymm a] : IsRelSymm (star a) where
  star_eq := (star_star a).trans (star_eq_of_symm a).symm

lemma IsRelSymm.of_star_le (ha : star a ≤ a) : IsRelSymm a where
  star_eq := ha.antisymm <| le_star_iff.mpr ha

lemma IsRelSymm.of_le_star (ha : a ≤ star a) : IsRelSymm a where
  star_eq := (le_star_iff.mp ha).antisymm ha

/-- The relation-algebra equivalent of `Relation.SymmGen`. -/
def symmGen (a : α) : α := a ⊔ star a

instance : IsRelSymm (symmGen a) where
  star_eq := by simp [symmGen, sup_comm]

lemma le_symmGen : a ≤ symmGen a := le_sup_left

lemma symmGen_le [IsRelSymm b] : symmGen a ≤ b ↔ a ≤ b := by
  simp [symmGen, star_le_iff, star_eq_of_symm]

lemma star_le_iff_of_isRelSymm [IsRelSymm b] : star a ≤ b ↔ a ≤ b := by
  simp [star_le_iff, star_eq_of_symm]

/-! ### Transitive elements -/

instance : IsRelTrans (⊥ : α) where
  mul_self_le := (mul_bot ⊥).le

instance : IsRelTrans (1 : α) where
  mul_self_le := (mul_one 1).le

instance : IsRelTrans (⊤ : α) where
  mul_self_le := le_top

instance [IsRelTrans a] : IsRelTrans (star a) where
  mul_self_le := by grw [← star_mul, mul_self_le_of_trans a]

lemma mul_le_of_isRelTrans [IsRelTrans c] (ha : a ≤ c) (hb : b ≤ c) : a * b ≤ c := by
  grw [← mul_self_le_of_trans c, ha, hb]

section Complete

variable {α : Type*} [CompleteRelationAlgebra α] {a b : α}

/-- Auxiliary definition for `RelationAlgebra.transGen`. -/
@[simps]
def transGenStep (a : α) : α →o α where
  toFun b := a ⊔ b * a
  monotone' a b h := by simp only; grw [h]

/-- The relation-algebra equivalent of `Relation.TransGen`. -/
def transGen (a : α) : α := (transGenStep a).lfp

lemma le_transGen (a : α) : a ≤ transGen a := by
  refine (transGenStep a).le_lfp fun b ↦ ?_
  grind [transGenStep_coe, sup_le_iff]

lemma transGen_mul_self_le (a : α) : transGen a * a ≤ transGen a :=
  le_sup_right.trans_eq (transGenStep a).map_lfp

lemma transGen_le [IsRelTrans b] : transGen a ≤ b ↔ a ≤ b := by
  refine ⟨le_transGen a |>.trans, fun h ↦ ?_⟩
  apply (transGenStep a).lfp_le
  grw [transGenStep_coe, h, mul_self_le_of_trans b, sup_idem]

instance : IsRelTrans (transGen a) where
  mul_self_le := by
    refine (transGenStep a).lfp_induction (p := (transGen a * · ≤ transGen a)) ?_ ?_
    · intro x hx _
      grw [transGenStep_coe, mul_sup, ← mul_assoc, hx, transGen_mul_self_le, sup_idem]
    · simp [mul_sSup]

end Complete

end Cslib.RelationAlgebra

/-! ### Element properties for `SetRel` -/

open Cslib.RelationAlgebra

namespace SetRel

variable {α : Type*} (r : SetRel α α)

theorem isRelRefl_iff_isRefl : IsRelRefl r ↔ r.IsRefl :=
  isRelRefl_iff.trans r.id_subset_iff

instance [hr : r.IsRefl] : IsRelRefl r := r.isRelRefl_iff_isRefl.mpr hr

theorem isRelSymm_iff_isSymm : IsRelSymm r ↔ r.IsSymm :=
  isRelSymm_iff.trans r.inv_eq_self_iff

instance [hr : r.IsSymm] : IsRelSymm r := r.isRelSymm_iff_isSymm.mpr hr

theorem isRelTrans_iff_isTrans : IsRelTrans r ↔ r.IsTrans :=
  isRelTrans_iff.trans r.isTrans_iff_comp_subset_self.symm

instance [hr : r.IsTrans] : IsRelTrans r := r.isRelTrans_iff_isTrans.mpr hr

variable {r : SetRel α α} {x y : α}

theorem mem_reflGen_iff : x ~[reflGen r] y ↔ Relation.ReflGen (· ~[r] ·) x y := by
  simp [reflGen, Relation.reflGen_iff, comm]

theorem mem_symmGen_iff : x ~[symmGen r] y ↔ Relation.SymmGen (· ~[r] ·) x y := by
  simp [symmGen, Relation.SymmGen]

theorem mem_transGen_iff : x ~[transGen r] y ↔ Relation.TransGen (· ~[r] ·) x y := by
  suffices transGen r = {p | Relation.TransGen (· ~[r] ·) p.1 p.2} by simp_all
  apply le_antisymm
  · rw [transGen_le]
    intro ⟨x, y⟩ h
    exact .single h
  · intro ⟨x, y⟩ (h : Relation.TransGen (· ~[r] ·) x y)
    induction h with
    | single h => exact le_transGen r h
    | @tail y z h h' ih => exact transGen_mul_self_le r ⟨y, ih, h'⟩

end SetRel
