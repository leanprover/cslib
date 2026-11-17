/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Order.AlgebraIntervals
public import Cslib.Foundations.RelationAlgebra.Representation
public import Mathlib.Order.FixedPoints

/-!-/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {α β : Type*} [RelationAlgebra α] {a b c : α}

class IsReflRA (a : α) : Prop where
  protected one_le : 1 ≤ a

class IsSymmRA (a : α) : Prop where
  protected star_eq : star a = a

class IsTransRA (a : α) : Prop where
  protected mul_self_le : a * a ≤ a

lemma one_le_of_refl (a : α) [IsReflRA a] : 1 ≤ a := IsReflRA.one_le

lemma isReflRA_iff {a : α} : IsReflRA a ↔ 1 ≤ a :=
  ⟨@IsReflRA.one_le _ _ a, IsReflRA.mk⟩

@[simp] lemma star_eq_of_symm (a : α) [IsSymmRA a] : star a = a := IsSymmRA.star_eq

lemma isSymmRA_iff {a : α} : IsSymmRA a ↔ star a = a :=
  ⟨@IsSymmRA.star_eq _ _ a, IsSymmRA.mk⟩

lemma mul_self_le_of_trans (a : α) [IsTransRA a] : a * a ≤ a := IsTransRA.mul_self_le

lemma isTransRA_iff {a : α} : IsTransRA a ↔ a * a ≤ a :=
  ⟨@IsTransRA.mul_self_le _ _ a, IsTransRA.mk⟩

open IsReflRA IsSymmRA IsTransRA

/-! ### Reflexive elements -/

instance : IsReflRA (1 : α) where
  one_le := le_rfl

instance : IsReflRA (⊤ : α) where
  one_le := le_top

lemma le_mul_left [hb : IsReflRA b] : a ≤ b * a := by
  nth_grw 1 [← one_mul a, one_le_of_refl b]

lemma le_mul_right [hb : IsReflRA b] : a ≤ a * b := by
  nth_grw 1 [← mul_one a, one_le_of_refl b]

instance [RelationAlgebra β] (F : Type*) [FunLike F α β] [OrderHomClass F α β] [OneHomClass F α β]
    (f : F) (a : α) [IsReflRA a] : IsReflRA (f a) where
  one_le := map_one f ▸ OrderHomClass.mono f (one_le_of_refl a)

def reflGenRA (a : α) : α := 1 ⊔ a

instance : IsReflRA (reflGenRA a) where
  one_le := le_sup_left

lemma le_reflGenRA : a ≤ reflGenRA a := le_sup_right

lemma reflGenRA_le [hb : IsReflRA b] : reflGenRA a ≤ b ↔ a ≤ b := by
  simp [reflGenRA, one_le_of_refl b]

/-! ### Symmetric elements -/

instance : IsSymmRA (⊥ : α) where
  star_eq := star_bot

instance : IsSymmRA (1 : α) where
  star_eq := star_one α

instance : IsSymmRA (⊤ : α) where
  star_eq := star_top

lemma IsSymmRA.of_star_le (ha : star a ≤ a) : IsSymmRA a where
  star_eq := ha.antisymm <| le_star_iff.mpr ha

lemma IsSymmRA.of_le_star (ha : a ≤ star a) : IsSymmRA a where
  star_eq := (le_star_iff.mp ha).antisymm ha

instance [RelationAlgebra β] (F : Type*) [FunLike F α β] [StarHomClass F α β]
    (f : F) (a : α) [IsSymmRA a] : IsSymmRA (f a) where
  star_eq := map_star f a ▸ congr(f $(star_eq_of_symm a))

def symmGenRA (a : α) : α := a ⊔ star a

instance : IsSymmRA (symmGenRA a) where
  star_eq := by simp [symmGenRA, sup_comm]

lemma le_symmGenRA : a ≤ symmGenRA a := le_sup_left

lemma symmGenRA_le [IsSymmRA b] : symmGenRA a ≤ b ↔ a ≤ b := by
  simp [symmGenRA, star_le_iff]

lemma star_le_iff_of_isSymmRA [IsSymmRA b] : star a ≤ b ↔ a ≤ b := by simp [star_le_iff]

/-! ### Transitive elements -/

instance : IsTransRA (⊥ : α) where
  mul_self_le := (mul_bot ⊥).le

instance : IsTransRA (1 : α) where
  mul_self_le := (mul_one 1).le

instance : IsTransRA (⊤ : α) where
  mul_self_le := le_top

lemma mul_le_of_isTransRA [IsTransRA c] (ha : a ≤ c) (hb : b ≤ c) : a * b ≤ c := by
  grw [← mul_self_le_of_trans c, ha, hb]

instance [RelationAlgebra β] (F : Type*) [FunLike F α β] [OrderHomClass F α β] [MulHomClass F α β]
    (f : F) (a : α) [IsTransRA a] : IsTransRA (f a) where
  mul_self_le := map_mul f a a ▸ OrderHomClass.mono f (mul_self_le_of_trans a)

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

lemma transGenRA_le [hb : IsTransRA b] : transGenRA a ≤ b ↔ a ≤ b := by
  refine ⟨le_transGenRA.trans, fun h ↦ ?_⟩
  apply (transGenStep a).lfp_le
  simp only [transGenStep_coe, sup_le_iff, h, true_and]
  grw [h, hb.mul_self_le]

end Complete

/-! ### Subalgebra below an "equivalence relation" -/

instance (a : α) [IsReflRA a] [IsSymmRA a] [IsTransRA a] :
    RelationAlgebra (Set.Iic a) where
  one := ⟨1, one_le_of_refl a⟩
  mul x y := ⟨(x : α) * y, mul_le_of_isTransRA x.prop y.prop⟩
  mul_assoc x y z := Subtype.ext <| mul_assoc (x : α) y z
  one_mul x := Subtype.ext <| one_mul (x : α)
  mul_one x := Subtype.ext <| mul_one (x : α)
  star x := ⟨star (x : α), star_le_iff_of_isSymmRA.mpr x.prop⟩
  star_involutive x := Subtype.ext <| star_involutive (x : α)
  star_mul x y := Subtype.ext <| star_mul (x : α) y
  sup_mul x y z := Subtype.ext <| sup_mul (x : α) y z
  star_sup x y := Subtype.ext <| star_sup (x : α) y
  tarski x y := by
    change star (x : α) * (a \ (x * y)) ≤ a \ y
    grw [sdiff_eq, sdiff_eq, inf_mul_le, tarski, (show x ≤ a from x.prop), star_eq_of_symm a,
      mul_self_le_of_trans a]

/-! ### Properties for `SetRel` -/

section SetRel

omit [RelationAlgebra α]

lemma isReflRA_iff_setRel_isRefl (r : SetRel α α) : IsReflRA r ↔ r.IsRefl := by
  simp [isReflRA_iff, ← SetRel.id_subset_iff]
  rfl

lemma isSymmRA_iff_setRel_isSymm (r : SetRel α α) : IsSymmRA r ↔ r.IsSymm := by
  simp [isSymmRA_iff, ← SetRel.inv_eq_self_iff, star]

lemma isTransRA_iff_setRel_isTrans (r : SetRel α α) : IsTransRA r ↔ r.IsTrans := by
  simp [isTransRA_iff, SetRel.isTrans_iff_comp_subset_self]
  rfl

end SetRel

example (R : Representation' α β) (a : α) [IsReflRA a] : IsReflRA (R a) := inferInstance

example (R : Representation' α β) : IsReflRA (R ⊤) := inferInstance

example (R : Representation' α β) (a : α) [IsSymmRA a] : IsSymmRA (R a) := inferInstance

example (R : Representation' α β) : IsSymmRA (R ⊤) := inferInstance

example (R : Representation' α β) (a : α) [IsTransRA a] : IsTransRA (R a) := inferInstance

example (R : Representation' α β) : IsTransRA (R ⊤) := inferInstance

@[simps]
def Representation'.toHom (R : Representation' α β) :
    RelationAlgebraHom α (Set.Iic (R ⊤)) where
  toFun a := ⟨R a, R.mono le_top⟩
  map_sup' _ _ := Subtype.ext <| map_sup R ..
  map_inf' _ _ := Subtype.ext <| map_inf R ..
  map_top' := rfl
  map_bot' := Subtype.ext <| map_bot R
  map_one' := Subtype.ext <| map_one R
  map_mul' _ _ := Subtype.ext <| map_mul R ..
  map_star' _ := Subtype.ext <| map_star R ..

lemma Representation'.toHom_injective (R : Representation' α β) :
    Function.Injective R.toHom := Function.Injective.of_comp (f := Subtype.val) R.injective

open SetRel in
noncomputable def piToSigmaEquiv (ι : Type v) (α : ι → Type w) :
    RelationAlgebraEquiv (Π i, SetRel (α i) (α i)) (Set.Iic <| prodRepresentation' ι α ⊤) :=
  .ofBijective (prodRepresentation' ι α).toHom <| by
    refine ⟨(prodRepresentation' ι α).toHom_injective, ?_⟩
    simp_rw [Function.Surjective, Subtype.ext_iff, Subtype.forall, Set.mem_Iic,
        Representation'.toHom_toFun_coe, prodRepresentation'_toFun]
    intro r hr
    use fun i ↦ {p | ⟨i, p.1⟩ ~[r] ⟨i, p.2⟩}
    grind

end Cslib.RelationAlgebra
