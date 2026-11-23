/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Data.SetRel
public import Cslib.Foundations.Order.AlgebraIntervals
public import Cslib.Foundations.RelationAlgebra.Basic
public import Mathlib.Order.FixedPoints

/-! # Element properties for relation algebras

This file defines the notion of reflexive (`Cslib.RelationAlgebra.IsRelRefl`), symmetric
(`Cslib.RelationAlgebra.IsRelSymm`) and transitive (`Cslib.RelationAlgebra.IsRelTrans`) elements
in a relation algebra. These properties are packaged as typeclasses, so that instance syntheses
can find `RelationAlgebra (Set.Iic a)` for `a` a symmetric and transitive element in a relation
algebra (see `Set.Iic.instRelationAlgebra` in `RelationAlgebra/Relativization.lean`).

Coreflexive (`Cslib.RelationAlgebra.IsRelCorefl`) elements are defined as those below `1`, and are
shown to be the analogue in relation algebras of sets, via the domain and codomain maps `relDom`
and `relCod`.

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

/-- A coreflexive or subidentity element of a relation algebra. -/
class IsRelCorefl [One α] [LE α] (a : α) : Prop where
  protected le_one : a ≤ 1

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

lemma le_one_of_corefl [One α] [LE α] (a : α) [IsRelCorefl a] : a ≤ 1 :=
  IsRelCorefl.le_one

lemma isRelCorefl_iff [One α] [LE α] {a : α} : IsRelCorefl a ↔ a ≤ 1 :=
  ⟨@IsRelCorefl.le_one _ _ _ a, IsRelCorefl.mk⟩

instance instIsRelCoreflMap [One α] [LE α] [One β] [LE β] (F : Type*) [FunLike F α β]
    [OrderHomClass F α β] [OneHomClass F α β] (f : F) (a : α) [IsRelCorefl a] :
    IsRelCorefl (f a) where
  le_one := map_one f ▸ RelHomClass.map_rel f (le_one_of_corefl a)

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

instance : IsRelCorefl (⊥ : α) where
  le_one := bot_le

instance : IsRelCorefl (1 : α) where
  le_one := le_rfl

instance [IsRelCorefl a] : IsRelCorefl (star a) where
  le_one := by
    rw [star_le_iff, star_one]
    exact le_one_of_corefl a

lemma IsRelCorefl.of_le [IsRelCorefl b] (h : a ≤ b) : IsRelCorefl a where
  le_one := h.trans (le_one_of_corefl b)

lemma mul_left_le [IsRelCorefl a] : a * b ≤ b := by
  grw [le_one_of_corefl a, one_mul b]

lemma mul_right_le [IsRelCorefl b] : a * b ≤ a := by
  grw [le_one_of_corefl b, mul_one a]

instance [IsRelCorefl a] : IsRelTrans a where
  mul_self_le := mul_left_le

instance [IsRelCorefl a] : IsRelSymm a := .of_le_star <| by
  grw [le_mul_star_mul a, mul_right_le, mul_left_le]

lemma mul_eq_inf [IsRelCorefl a] [IsRelCorefl b] : a * b = a ⊓ b := by
  refine eq_of_forall_le_iff fun c ↦ (le_inf_iff.trans ?_).symm
  constructor
  · intro ⟨ha, hb⟩
    have := IsRelCorefl.of_le ha
    nth_grw 1 [le_mul_star_mul c, mul_right_le, star_eq_of_symm, ha, hb]
  · intro h
    exact ⟨h.trans mul_right_le, h.trans mul_left_le⟩

/-- The domain of an element in a relation algebra, as a coreflexive. -/
def relDom (a : α) : α := a * ⊤ ⊓ 1

instance : IsRelCorefl (relDom a) := ⟨inf_le_right⟩

/-- The codomain of an element in a relation algebra, as a coreflexive. -/
def relCod (a : α) : α := ⊤ * a ⊓ 1

instance : IsRelCorefl (relCod a) := ⟨inf_le_right⟩

@[simp, push]
lemma star_relDom : star (relDom a) = relCod (star a) := by
  rw [relDom, relCod]
  push star
  rfl

@[simp, push]
lemma star_relCod : star (relCod a) = relDom (star a) := star_injective <| by
  push star
  rfl

@[gcongr] lemma relDom_mono (h : a ≤ b) : relDom a ≤ relDom b := by grw [relDom, relDom, h]

@[gcongr] lemma relCod_mono (h : a ≤ b) : relCod a ≤ relCod b := by grw [relCod, relCod, h]

lemma relDom_le_iff_le_mul [IsRelCorefl b] : relDom a ≤ b ↔ a ≤ b * a := by
  constructor <;> intro h
  · grw [← h, relDom, inf_comm, ← le_top (a := star a), ← right_modular, one_mul, inf_idem]
  · grw [relDom, h, mul_assoc, left_modular, inf_le_right, star_eq_of_symm b, mul_one, mul_left_le]

/-- Reading left multiplication by a coreflexive element as restriction, this result characterises
`relDom a` as the largest coreflexive `b` such that the restriction of `a` to `b` is `a`. -/
theorem relDom_le_iff [IsRelCorefl b] : relDom a ≤ b ↔ b * a = a := by
  simp [relDom_le_iff_le_mul, le_antisymm_iff, mul_left_le]

lemma relDom_mul_self : relDom a * a = a := by simp [← relDom_le_iff (b := relDom a)]

lemma relCod_le_iff_le_mul [IsRelCorefl b] : relCod a ≤ b ↔ a ≤ a * b := by
  rw [← star_le_star_iff, star_relCod, relDom_le_iff_le_mul, ← star_mul, star_le_star_iff]

/-- Reading right multiplication by a coreflexive element as coerestriction (relating only those
pairs whose second components lies in some set), this result characterises `relDom a` as the
largest coreflexive `b` such that the corestriction of `a` to `b` is `a`. -/
theorem relCod_le_iff [IsRelCorefl b] : relCod a ≤ b ↔ a * b = a := by
  simp [relCod_le_iff_le_mul, le_antisymm_iff, mul_right_le]

lemma self_mul_relCod : a * relCod a = a := by simp [← relCod_le_iff (b := relCod a)]

lemma relDom_eq_mul_star (a : α) : relDom a = a * star a ⊓ 1 := by
  apply le_antisymm
  · have : IsRelCorefl (a * star a ⊓ 1) := ⟨inf_le_right⟩
    grw [relDom_le_iff_le_mul, inf_comm, ← right_modular, one_mul, inf_idem]
  · grw [relDom, le_top (a := star a)]

lemma relCod_eq_star_mul : relCod a = star a * a ⊓ 1 := star_injective <| by
  simpa using relDom_eq_mul_star (star a)

lemma relDom_corefl [IsRelCorefl a] : relDom a = a := by
  simpa [relDom_eq_mul_star, star_eq_of_symm a, mul_eq_inf] using le_one_of_corefl a

lemma relCod_corefl [IsRelCorefl a] : relCod a = a := by
  simpa [relCod_eq_star_mul, star_eq_of_symm a, mul_eq_inf] using le_one_of_corefl a

lemma relDom_bot : relDom (⊥ : α) = ⊥ := by simp [relDom]

lemma relDom_eq_bot_iff : relDom a = ⊥ ↔ a = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.symm ▸ relDom_bot⟩
  rw [← relDom_mul_self (a := a), h, bot_mul]

lemma relDom_eq_one_iff : relDom a = 1 ↔ a * ⊤ = ⊤ := by
  rw [relDom, inf_eq_right, eq_top_iff]
  refine ⟨?_, le_top.trans⟩
  intro h
  nth_grw 1 [← one_mul ⊤, h, mul_assoc, mul_self_le_of_trans ⊤]

lemma relCod_bot : relCod (⊥ : α) = ⊥ := by simp [relCod]

lemma relCod_eq_bot_iff : relCod a = ⊥ ↔ a = ⊥ := by
  rw [← star_inj, star_relCod, star_bot, relDom_eq_bot_iff, star_eq_iff_star_eq, star_bot, Eq.comm]

lemma relCod_eq_one_iff : relCod a = 1 ↔ ⊤ * a = ⊤ := by
  nth_rw 1 [← star_inj, star_one, star_relCod, relDom_eq_one_iff, ← star_top, ← star_mul,
    star_eq_iff_star_eq, star_top, Eq.comm]

lemma relDom_of_isRelRefl [IsRelRefl a] : relDom a = 1 := by
  apply (le_one_of_corefl <| relDom a).antisymm
  grw [← one_le_of_refl a]
  simp [relDom]

lemma relCod_of_isRelRefl [IsRelRefl a] : relCod a = 1 := star_injective <| by
  push star
  exact relDom_of_isRelRefl

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

theorem relDom_eq_ofSet : relDom r = ofSet r.dom := by
  ext ⟨x, y⟩
  simp [relDom, and_comm]

theorem relCod_eq_ofSet : relCod r = ofSet r.cod := by
  ext ⟨x, y⟩
  simp +contextual [relCod, and_comm]

theorem isRelCorefl_iff_eq_ofSet (r : SetRel α α) : IsRelCorefl r ↔ ∃ s, r = ofSet s := by
  constructor
  · intro h
    use r.dom
    nth_rw 1 [← relDom_corefl (a := r), relDom_eq_ofSet]
  · rw [isRelCorefl_iff]
    rintro ⟨s, rfl⟩ ⟨x, y⟩ ⟨(rfl : x = y), -⟩
    exact mem_one.mpr rfl

end SetRel
