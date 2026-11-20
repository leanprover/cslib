/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Order.AlgebraIntervals
public import Cslib.Foundations.RelationAlgebra.Basic
public import Mathlib.Order.FixedPoints

/-! # Element properties for relation algebras -/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {α β : Type*} {a b c : α}

class IsRelRefl [One α] [LE α] (a : α) : Prop where
  protected one_le : 1 ≤ a

class IsRelSymm [Star α] (a : α) : Prop where
  protected star_eq : star a = a

class IsRelTrans [Mul α] [LE α] (a : α) : Prop where
  protected mul_self_le : a * a ≤ a

lemma one_le_of_refl [One α] [LE α] (a : α) [IsRelRefl a] : 1 ≤ a := IsRelRefl.one_le

instance [One α] [LE α] [One β] [LE β] (F : Type*) [FunLike F α β] [OrderHomClass F α β]
    [OneHomClass F α β] (f : F) (a : α) [IsRelRefl a] : IsRelRefl (f a) where
  one_le := map_one f ▸ RelHomClass.map_rel f (one_le_of_refl a)

lemma isRelRefl_iff [One α] [LE α] {a : α} : IsRelRefl a ↔ 1 ≤ a :=
  ⟨@IsRelRefl.one_le _ _ _ a, IsRelRefl.mk⟩

@[simp] lemma star_eq_of_symm [Star α] (a : α) [IsRelSymm a] : star a = a := IsRelSymm.star_eq

lemma isRelSymm_iff [Star α] {a : α} : IsRelSymm a ↔ star a = a :=
  ⟨@IsRelSymm.star_eq _ _ a, IsRelSymm.mk⟩

instance [Star α] [Star β] (F : Type*) [FunLike F α β] [StarHomClass F α β]
    (f : F) (a : α) [IsRelSymm a] : IsRelSymm (f a) where
  star_eq := by rw [← map_star f, star_eq_of_symm]

lemma mul_self_le_of_trans [Mul α] [LE α] (a : α) [IsRelTrans a] : a * a ≤ a :=
  IsRelTrans.mul_self_le

lemma isRelTrans_iff [Mul α] [LE α] {a : α} : IsRelTrans a ↔ a * a ≤ a :=
  ⟨@IsRelTrans.mul_self_le _ _ _ a, IsRelTrans.mk⟩

instance [Mul α] [LE α] [Mul β] [LE β] (F : Type*) [FunLike F α β] [OrderHomClass F α β]
  [MulHomClass F α β] (f : F) (a : α) [IsRelTrans a] : IsRelTrans (f a) where
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

def reflGenRA (a : α) : α := 1 ⊔ a

instance : IsRelRefl (reflGenRA a) where
  one_le := le_sup_left

lemma le_reflGenRA : a ≤ reflGenRA a := le_sup_right

lemma reflGenRA_le [hb : IsRelRefl b] : reflGenRA a ≤ b ↔ a ≤ b := by
  simp [reflGenRA, one_le_of_refl b]

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

def symmGenRA (a : α) : α := a ⊔ star a

instance : IsRelSymm (symmGenRA a) where
  star_eq := by simp [symmGenRA, sup_comm]

lemma le_symmGenRA : a ≤ symmGenRA a := le_sup_left

lemma symmGenRA_le [IsRelSymm b] : symmGenRA a ≤ b ↔ a ≤ b := by
  simp [symmGenRA, star_le_iff]

lemma star_le_iff_of_isRelSymm [IsRelSymm b] : star a ≤ b ↔ a ≤ b := by simp [star_le_iff]

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

@[simps]
def transGenStep (a : α) : α →o α where
  toFun b := a ⊔ a * b
  monotone' a b h := by simp only; grw [h]

def transGenRA (a : α) : α := (transGenStep a).lfp

lemma le_transGenRA : a ≤ transGenRA a := by
  refine (transGenStep a).le_lfp fun b ↦ ?_
  grind [transGenStep_coe, sup_le_iff]

lemma transGenRA_le [hb : IsRelTrans b] : transGenRA a ≤ b ↔ a ≤ b := by
  refine ⟨le_transGenRA.trans, fun h ↦ ?_⟩
  apply (transGenStep a).lfp_le
  simp only [transGenStep_coe, sup_le_iff, h, true_and]
  grw [h, hb.mul_self_le]

end Complete

private lemma inf_one_mul_eq {a x : α} (h : x ≤ a) [IsRelSymm a] [IsRelTrans a] :
    (a ⊓ 1) * x = x := by
  apply le_antisymm
  · grw [inf_le_right, one_mul]
  · have : x ≤ (1 ⊓ x * star x) * x := by simpa using right_modular 1 x x
    nth_grw 1 [this, inf_comm, h, h, star_eq_of_symm a, mul_self_le_of_trans a]

@[simps! one_coe mul_coe star_coe]
instance _root_.Set.Iic.instRelationAlgebra (a : α) [IsRelSymm a] [IsRelTrans a] :
    RelationAlgebra (Set.Iic a) where
  one := ⟨a ⊓ 1, inf_le_left⟩
  mul x y := ⟨(x : α) * y, mul_le_of_isRelTrans x.prop y.prop⟩
  mul_assoc x y z := Subtype.ext <| mul_assoc (x : α) y z
  one_mul x := private_decl% (Subtype.ext <| inf_one_mul_eq x.prop)
  mul_one x := by
    refine Subtype.ext (star_injective ?_ : x * (a ⊓ 1) = x)
    simpa using inf_one_mul_eq (star_le_iff_of_isRelSymm.mpr x.prop)
  star x := ⟨star (x : α), star_le_iff_of_isRelSymm.mpr x.prop⟩
  star_involutive x := Subtype.ext <| star_involutive (x : α)
  star_mul x y := Subtype.ext <| star_mul (x : α) y
  sup_mul x y z := Subtype.ext <| sup_mul (x : α) y z
  star_sup x y := Subtype.ext <| star_sup (x : α) y
  tarski x y := by
    change star (x : α) * (a \ (x * y)) ≤ a \ y
    grw [sdiff_eq, sdiff_eq, mul_inf_le, tarski, (show x ≤ a from x.prop), star_eq_of_symm a,
      mul_self_le_of_trans a]

end Cslib.RelationAlgebra
