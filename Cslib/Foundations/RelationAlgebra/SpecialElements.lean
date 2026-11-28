/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Data.SetRel
public import Cslib.Foundations.Order.AlgebraIntervals
public import Cslib.Foundations.Relation.Defs
public import Cslib.Foundations.RelationAlgebra.Basic
public import Mathlib.Order.FixedPoints

/-! # Element properties for relation algebras

This file defines the notion of reflexive (`Cslib.RelationAlgebra.IsRelRefl`), symmetric
(`Cslib.RelationAlgebra.IsRelSymm`) and transitive (`Cslib.RelationAlgebra.IsRelTrans`) elements
in a relation algebra. These properties are packaged as typeclasses, so that instance syntheses
can find `RelationAlgebra (Set.Iic a)` for `a` a symmetric and transitive element in a relation
algebra (see `Set.Iic.instRelationAlgebra` in `RelationAlgebra.Relativization.lean`).

Coreflexive (`Cslib.RelationAlgebra.IsRelCorefl`) elements are defined as those below `1`, and are
shown to be the analogue in relation algebras of sets, via the domain and codomain maps `relDom`
and `relCod`.

In general, most relational properties have RA equivalents, translating universal quantifiers using
`≤`, and existential quantifiers with `*`. We translate many of the properties defined on
`α → α → Prop` in `Foundations.Relation.Defs` to the relation algebra `SetRel α α`.

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

lemma le_reflGen (a : α) : a ≤ reflGen a := le_sup_right

lemma reflGen_le [hb : IsRelRefl b] : reflGen a ≤ b ↔ a ≤ b := by
  simp [reflGen, one_le_of_refl b]

@[gcongr] lemma reflGen_mono (h : a ≤ b) : reflGen a ≤ reflGen b := sup_le_sup_left h 1

lemma reflGen_eq_self_iff : reflGen a = a ↔ IsRelRefl a := by
  simp [reflGen, isRelRefl_iff]

lemma reflGen_of_refl (a : α) [IsRelRefl a] : reflGen a = a := reflGen_eq_self_iff.mpr inferInstance

@[simp, push] lemma star_reflGen (a : α) : star (reflGen a) = reflGen (star a) := by simp [reflGen]

instance [IsRelSymm a] : IsRelSymm (reflGen a) where
  star_eq := by rw [star_reflGen, star_eq_of_symm a]

instance [IsRelTrans a] : IsRelTrans (reflGen a) where
  mul_self_le := by
    grw [reflGen, mul_sup, sup_mul, sup_mul, mul_self_le_of_trans a]
    simp

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

lemma le_symmGen (a : α) : a ≤ symmGen a := le_sup_left

lemma symmGen_le [IsRelSymm b] : symmGen a ≤ b ↔ a ≤ b := by
  simp [symmGen, star_le_iff, star_eq_of_symm]

@[gcongr] lemma symmGen_mono (h : a ≤ b) : symmGen a ≤ symmGen b := by
  grw [symmGen, symmGen, h]

lemma symmGen_eq_self_iff : symmGen a = a ↔ IsRelSymm a := by
  simp [symmGen, isRelSymm_iff, le_antisymm_iff, star_le_iff]

lemma symmGen_of_symm (a : α) [IsRelSymm a] : symmGen a = a := symmGen_eq_self_iff.mpr inferInstance

@[simp] lemma symmGen_star (a : α) : symmGen (star a) = symmGen a := by simp [symmGen, sup_comm]

lemma star_le_iff_of_isRelSymm [IsRelSymm b] : star a ≤ b ↔ a ≤ b := by
  simp [star_le_iff, star_eq_of_symm]

instance [IsRelRefl a] : IsRelRefl (symmGen a) where
  one_le := (one_le_of_refl a).trans (le_symmGen a)

lemma symmGen_reflGen (a : α) : symmGen (reflGen a) = reflGen (symmGen a) := by
  simp [symmGen, reflGen]; grind

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

lemma mul_self_eq (a : α) [IsRelRefl a] [IsRelTrans a] : a * a = a :=
  (mul_self_le_of_trans a).antisymm le_mul_left

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

lemma self_mul_transGen_le (a : α) : a * transGen a ≤ transGen a :=
  (mul_le_mul_left (le_transGen a) (transGen a)).trans <| mul_self_le_of_trans (transGen a)

@[gcongr] lemma transGen_mono (h : a ≤ b) : transGen a ≤ transGen b :=
  transGen_le.mpr (h.trans <| le_transGen b)

lemma transGen_eq_self_iff : transGen a = a ↔ IsRelTrans a := by
  refine ⟨fun h ↦ h ▸ instIsRelTransTransGen, ?_⟩
  simp +contextual [le_antisymm_iff, le_transGen a, transGen_le]

lemma transGen_of_trans (a : α) [IsRelTrans a] : transGen a = a :=
  transGen_eq_self_iff.mpr inferInstance

@[simp, push] lemma star_transGen (a : α) : star (transGen a) = transGen (star a) := by
  suffices ∀ b, transGen (star b) ≤ star (transGen b) by
    refine le_antisymm ?_ (this a)
    nth_grw 1 [← star_star a, this (star a), star_star]
  intro b
  grw [transGen_le, le_transGen b]

lemma transGen_eq_sup (a : α) : transGen a = a ⊔ transGen a * a :=
  (transGenStep a).map_lfp.symm

lemma transGen_eq_sup' (a : α) : transGen a = a ⊔ a * transGen a := star_injective <| by
  push star
  exact transGen_eq_sup (star a)

instance [IsRelRefl a] : IsRelRefl (transGen a) where
  one_le := (one_le_of_refl a).trans (le_transGen a)

instance [IsRelSymm a] : IsRelSymm (transGen a) where
  star_eq := by rw [star_transGen, star_eq_of_symm a]

lemma symmGen_transGen_le (a : α) : symmGen (transGen a) ≤ transGen (symmGen a) := by
  grw [symmGen_le, le_symmGen a]

/-- The relation-algebra equivalent of `Relation.ReflTransGen`. -/
def reflTransGen (a : α) : α := reflGen (transGen a)

lemma reflGen_transGen (a : α) : reflGen (transGen a) = reflTransGen a := rfl

lemma transGen_reflGen (a : α) : transGen (reflGen a) = reflTransGen a := by
  apply le_antisymm
  · grw [← reflGen_transGen, transGen_le, le_transGen a]
  · grw [← reflGen_transGen, reflGen_le, le_reflGen a]

lemma le_reflTransGen (a : α) : a ≤ reflTransGen a := by
  grw [reflTransGen, le_transGen a, le_reflGen (transGen a)]

lemma reflTransGen_le [IsRelRefl b] [IsRelTrans b] : reflTransGen a ≤ b ↔ a ≤ b := by
  refine ⟨fun h ↦ (le_reflTransGen a).trans h, fun h ↦ ?_⟩
  rwa [reflTransGen, reflGen_le, transGen_le]

instance : IsRelRefl (reflTransGen a) := inferInstanceAs <| IsRelRefl (reflGen _)

instance : IsRelTrans (reflTransGen a) := inferInstanceAs <| IsRelTrans (reflGen _)

@[gcongr] lemma reflTransGen_mono (h : a ≤ b) : reflTransGen a ≤ reflTransGen b := by
  grw [reflTransGen, reflTransGen, h]

lemma reflTransGen_eq_self_iff : reflTransGen a = a ↔ IsRelRefl a ∧ IsRelTrans a := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨_, _⟩ ↦ ?eq⟩
  case eq => rw [reflTransGen, transGen_of_trans, reflGen_of_refl]
  all_goals
    rw [← h]
    infer_instance

lemma reflTransGen_of_refl_trans (a : α) [IsRelRefl a] [IsRelTrans a] : reflTransGen a = a :=
  reflTransGen_eq_self_iff.mpr ⟨inferInstance, inferInstance⟩

@[simp, push] lemma star_reflTransGen (a : α) : star (reflTransGen a) = reflTransGen (star a) := by
  simp [reflTransGen]

instance [IsRelSymm a] : IsRelSymm (reflTransGen a) := inferInstanceAs <| IsRelSymm (reflGen _)

lemma symmGen_reflTransGen_le (a : α) : symmGen (reflTransGen a) ≤ reflTransGen (symmGen a) := by
  grw [reflTransGen, symmGen_reflGen, symmGen_transGen_le, reflTransGen]

lemma reflTransGen_mul_self (a : α) : reflTransGen a * a = transGen a := by
  rw [reflTransGen, reflGen, sup_mul, one_mul, ← transGen_eq_sup]

lemma self_mul_reflTransGen (a : α) : a * reflTransGen a = transGen a := by
  rw [reflTransGen, reflGen, mul_sup, mul_one, ← transGen_eq_sup']

lemma reflTransGen_eq_sup (a : α) : reflTransGen a = 1 ⊔ reflTransGen a * a :=
  congr(1 ⊔ $((reflTransGen_mul_self a).symm))

lemma reflTransGen_eq_sup' (a : α) : reflTransGen a = 1 ⊔ a * reflTransGen a :=
  congr(1 ⊔ $((self_mul_reflTransGen a).symm))

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

lemma mul_top_inf_eq_mul [IsRelCorefl a] : a * ⊤ ⊓ b = a * b := by
  refine le_antisymm ?_ <| le_inf (mul_le_mul_right le_top a) mul_left_le
  grw [left_modular, top_inf_eq, mul_left_le, star_eq_of_symm a]

lemma top_mul_inf_eq_mul [IsRelCorefl a] : ⊤ * a ⊓ b = b * a := star_injective <| by
  push star
  exact mul_top_inf_eq_mul

/-- The domain of an element in a relation algebra, as a coreflexive. -/
def relDom (a : α) : α := a * ⊤ ⊓ 1

instance : IsRelCorefl (relDom a) := ⟨inf_le_right⟩

/-- The codomain of an element in a relation algebra, as a coreflexive. -/
def relCod (a : α) : α := ⊤ * a ⊓ 1

instance : IsRelCorefl (relCod a) := ⟨inf_le_right⟩

@[simp]
lemma relDom_star : relDom (star a) = relCod a := by
  rw [← star_eq_of_symm (relCod a), relCod, relDom]
  push star
  rfl

@[simp]
lemma relCod_star : relCod (star a) = relDom a := by
  rw [← star_eq_of_symm (relDom a), relDom, relCod]
  push star
  rfl

@[gcongr] lemma relDom_mono (h : a ≤ b) : relDom a ≤ relDom b := by grw [relDom, relDom, h]

@[gcongr] lemma relCod_mono (h : a ≤ b) : relCod a ≤ relCod b := by grw [relCod, relCod, h]

lemma relDom_le_iff_le_mul [IsRelCorefl b] : relDom a ≤ b ↔ a ≤ b * a := by
  constructor <;> intro h
  · grw [← h, relDom, inf_comm, ← le_top (a := star a), ← right_modular, one_mul, inf_idem]
  · grw [relDom, h, mul_assoc, left_modular, inf_le_right, star_eq_of_symm b, mul_one, mul_left_le]

/-- Reading left multiplication by a coreflexive element as restriction (cf
`SetRel.mem_ofSet_comp_iff` in `Cslib.Foundations.Data.SetRel`), this result characterises
`relDom a` as the smallest coreflexive `b` such that the restriction of `a` to `b` is `a`. -/
theorem relDom_le_iff [IsRelCorefl b] : relDom a ≤ b ↔ b * a = a := by
  simp [relDom_le_iff_le_mul, le_antisymm_iff, mul_left_le]

lemma relDom_mul_self (a : α) : relDom a * a = a := by simp [← relDom_le_iff]

lemma relCod_le_iff_le_mul [IsRelCorefl b] : relCod a ≤ b ↔ a ≤ a * b := by
  simp [← relDom_star, relDom_le_iff_le_mul, star_le_iff, star_eq_of_symm b]

/-- Reading right multiplication by a coreflexive element as corestriction (cf
`SetRel.mem_comp_ofSet_iff` in `Cslib.Foundations.Data.SetRel`), this result characterises
`relCod a` as the smallest coreflexive `b` such that the corestriction of `a` to `b` is `a`. -/
theorem relCod_le_iff [IsRelCorefl b] : relCod a ≤ b ↔ a * b = a := by
  simp [relCod_le_iff_le_mul, le_antisymm_iff, mul_right_le]

lemma self_mul_relCod (a : α) : a * relCod a = a := by simp [← relCod_le_iff]

lemma relDom_eq_mul_star (a : α) : relDom a = a * star a ⊓ 1 := by
  apply le_antisymm
  · have : IsRelCorefl (a * star a ⊓ 1) := ⟨inf_le_right⟩
    grw [relDom_le_iff_le_mul, inf_comm, ← right_modular, one_mul, inf_idem]
  · grw [relDom, le_top (a := star a)]

lemma relCod_eq_star_mul : relCod a = star a * a ⊓ 1 := by
  rw [← relDom_star, relDom_eq_mul_star, star_star]

lemma relDom_mul_top : relDom a * ⊤ = a * ⊤ := by
  apply le_antisymm
  · grw [relDom, inf_mul_le, mul_assoc, mul_self_eq ⊤]; simp
  · nth_rw 1 [← relDom_mul_self a, mul_assoc]
    exact mul_le_mul_right le_top (relDom a)

lemma top_mul_relCod : ⊤ * relCod a = ⊤ * a := star_injective <| by
  simpa [star_eq_of_symm, ← relDom_star] using relDom_mul_top

lemma relDom_eq_relDom_iff : relDom a = relDom b ↔ a * ⊤ = b * ⊤ := by
  constructor
  · intro h
    rw [← relDom_mul_top, h, relDom_mul_top]
  · simp +contextual [relDom]

lemma relCod_eq_relCod_iff : relCod a = relCod b ↔ ⊤ * a = ⊤ * b := by
  constructor
  · intro h
    rw [← top_mul_relCod, h, top_mul_relCod]
  · simp +contextual [relCod]

lemma relDom_mul_relDom : relDom (a * relDom b) = relDom (a * b) := by
  rw [relDom_eq_relDom_iff, mul_assoc, relDom_mul_top, mul_assoc]

lemma relDom_mul_le : relDom (a * b) ≤ relDom a := by
  grw [← relDom_mul_relDom, mul_right_le]

lemma relCod_relCod_mul : relCod (relCod a * b) = relCod (a * b) := by
  rw [relCod_eq_relCod_iff, ← mul_assoc, top_mul_relCod, ← mul_assoc]

lemma relCod_mul_le : relCod (a * b) ≤ relCod b := by
  grw [← relCod_relCod_mul, mul_left_le]

lemma relDom_of_isRelCorefl (a : α) [IsRelCorefl a] : relDom a = a := by
  rw [relDom, mul_top_inf_eq_mul, mul_one]

lemma relCod_of_isRelCorefl (a : α) [IsRelCorefl a] : relCod a = a := by
  rw [relCod, top_mul_inf_eq_mul, one_mul]

lemma relDom_bot : relDom (⊥ : α) = ⊥ := by simp [relDom]

lemma relCod_bot : relCod (⊥ : α) = ⊥ := by simp [relCod]

lemma relDom_eq_bot_iff : relDom a = ⊥ ↔ a = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.symm ▸ relDom_bot⟩
  rw [← relDom_mul_self a, h, bot_mul]

lemma relCod_eq_bot_iff : relCod a = ⊥ ↔ a = ⊥ := by
  nth_rw 1 [← relDom_star, relDom_eq_bot_iff, ← star_bot, star_inj]

lemma relDom_of_isRelRefl [IsRelRefl a] : relDom a = 1 := by
  apply (le_one_of_corefl <| relDom a).antisymm
  grw [← one_le_of_refl a]
  simp [relDom]

lemma relCod_of_isRelRefl [IsRelRefl a] : relCod a = 1 := by
  rw [← relDom_star, relDom_of_isRelRefl]

lemma relDom_eq_one_iff : relDom a = 1 ↔ a * ⊤ = ⊤ := by
  rw [← relDom_of_isRelRefl (a := ⊤), relDom_eq_relDom_iff, mul_self_eq]

lemma relCod_eq_one_iff : relCod a = 1 ↔ ⊤ * a = ⊤ := by
  rw [← relCod_of_isRelRefl (a := ⊤), relCod_eq_relCod_iff, mul_self_eq]

@[simp] lemma relDom_sup : relDom (a ⊔ b) = relDom a ⊔ relDom b := by
  simp [relDom, sup_mul, inf_sup_right]

@[simp] lemma relCod_sup : relCod (a ⊔ b) = relCod a ⊔ relCod b := by
  simp [relCod, mul_sup, inf_sup_right]

@[simp] lemma relDom_symmGen : relDom (symmGen a) = relDom a ⊔ relCod a := by
  rw [symmGen, relDom_sup, relDom_star]

@[simp] lemma relCod_symmGen : relCod (symmGen a) = relDom a ⊔ relCod a := by
  rw [← relDom_star, star_eq_of_symm, relDom_symmGen]

@[simp] lemma relDom_transGen {α : Type*} [CompleteRelationAlgebra α] (a : α) :
    relDom (transGen a) = relDom a := by
  refine le_antisymm (relDom_le_iff_le_mul.mpr ?_) (relDom_mono <| le_transGen a)
  refine (transGenStep a).lfp_induction (p := (· ≤ relDom a * transGen a)) ?_ (by simp)
  intro b hb hb'
  apply sup_le
  · grw [← le_transGen, relDom_mul_self a]
  · grw [hb, mul_assoc, transGen_mul_self_le]

@[simp] lemma relCod_transGen {α : Type*} [CompleteRelationAlgebra α] (a : α) :
    relCod (transGen a) = relCod a := by
  rw [← relDom_star, star_transGen, relDom_transGen, relDom_star]

end Cslib.RelationAlgebra

/-! ### Element properties for `SetRel` -/

open Cslib.RelationAlgebra

namespace SetRel

variable {α : Type*} (r : SetRel α α)

theorem isRefl_iff_isRelRefl : r.IsRefl ↔ IsRelRefl r :=
  isRelRefl_iff.trans r.id_subset_iff |>.symm

instance [hr : r.IsRefl] : IsRelRefl r := r.isRefl_iff_isRelRefl.mp hr

theorem isIrrefl_iff : r.IsIrrefl ↔ r ⊆ 1ᶜ := by
  simp_rw [SetRel.IsIrrefl, irrefl_iff_le_ne, Set.subset_def, LE.le, Prod.forall,
    Set.mem_compl_iff, mem_one]

theorem isSymm_iff_isRelSymm : r.IsSymm ↔ IsRelSymm r :=
  isRelSymm_iff.trans r.inv_eq_self_iff |>.symm

instance [hr : r.IsSymm] : IsRelSymm r := r.isSymm_iff_isRelSymm.mp hr

theorem isTrans_iff_isRelTrans : r.IsTrans ↔ IsRelTrans r :=
  r.isTrans_iff_comp_subset_self.trans isRelTrans_iff.symm

instance [hr : r.IsTrans] : IsRelTrans r := r.isTrans_iff_isRelTrans.mp hr

variable {s r : SetRel α α} {x y : α}

theorem reflGen_iff_mem_reflGen : Relation.ReflGen (· ~[r] ·) x y ↔ x ~[reflGen r] y := by
  simp [reflGen, Relation.reflGen_iff, comm]

theorem reflGen_eq :  Relation.ReflGen (· ~[r] ·) = (· ~[reflGen r] ·):= by
  ext
  exact reflGen_iff_mem_reflGen

theorem symmGen_iff_mem_symmGen : Relation.SymmGen (· ~[r] ·) x y ↔ x ~[symmGen r] y := .rfl

theorem symmGen_eq : (· ~[symmGen r] ·) = Relation.SymmGen (· ~[r] ·) := rfl

theorem transGen_iff_mem_transGen : Relation.TransGen (· ~[r] ·) x y ↔ x ~[transGen r] y := by
  suffices transGen r = {p | Relation.TransGen (· ~[r] ·) p.1 p.2} by simp_all
  apply le_antisymm
  · rw [transGen_le]
    intro ⟨x, y⟩ h
    exact .single h
  · intro ⟨x, y⟩ (h : Relation.TransGen (· ~[r] ·) x y)
    induction h with
    | single h => exact le_transGen r h
    | @tail y z h h' ih => exact transGen_mul_self_le r ⟨y, ih, h'⟩

theorem transGen_eq : Relation.TransGen (· ~[r] ·) = (· ~[transGen r] ·) := by
  ext
  exact transGen_iff_mem_transGen

theorem reflTransGen_iff_mem_reflTransGen :
    Relation.ReflTransGen (· ~[r] ·) x y ↔ x ~[reflTransGen r] y := by
  rw [reflTransGen, reflGen, Relation.reflTransGen_iff_eq_or_transGen, Eq.comm, Set.mem_union,
    mem_one, transGen_iff_mem_transGen]

theorem reflTransGen_eq : Relation.ReflTransGen (· ~[r] ·) = (· ~[reflTransGen r] ·) := by
  ext
  exact reflTransGen_iff_mem_reflTransGen

theorem ofSet_dom_eq : ofSet r.dom = relDom r := by
  ext ⟨x, y⟩
  simp [relDom, and_comm]

theorem ofSet_cod_eq : ofSet r.cod = relCod r := by
  ext ⟨x, y⟩
  simp +contextual [relCod, and_comm]

theorem isRelCorefl_iff_eq_ofSet (r : SetRel α α) : IsRelCorefl r ↔ ∃ s, r = ofSet s := by
  constructor
  · intro h
    use r.dom
    nth_rw 1 [← relDom_of_isRelCorefl r, ofSet_dom_eq]
  · rw [isRelCorefl_iff]
    rintro ⟨s, rfl⟩ ⟨x, y⟩ ⟨(rfl : x = y), -⟩
    exact mem_one.mpr rfl

theorem rightEuclidean_iff : Relation.RightEuclidean (· ~[r] ·) ↔ star r * r ⊆ r :=
  ⟨fun ⟨h⟩ ⟨_, _⟩ ⟨_, hb, ha ⟩ ↦ h hb ha, fun h ↦ ⟨fun hb ha ↦ h ⟨_, hb, ha⟩⟩⟩

theorem leftEuclidean_iff : Relation.LeftEuclidean (· ~[r] ·) ↔ r * star r ⊆ r :=
  ⟨fun ⟨h⟩ ⟨_, _⟩ ⟨_, ha, hb ⟩↦ h ha hb, fun h ↦ ⟨fun ha hb ↦ h ⟨_, ha, hb⟩⟩⟩

theorem rightTotal_iff : Relator.RightTotal (· ~[r] ·) ↔ relCod r = 1 := by
  simp only [Relator.RightTotal, relCod_eq_one_iff, Set.top_eq_univ, Set.eq_univ_iff_forall,
    Prod.forall, mem_mul, Set.mem_univ, true_and]
  exact ⟨fun h _ a ↦ h a, fun h a ↦ h a a⟩

theorem leftTotal_iff : Relator.LeftTotal (· ~[r] ·) ↔ relDom r = 1 := by
  simp only [Relator.LeftTotal, relDom_eq_one_iff, Set.top_eq_univ, Set.eq_univ_iff_forall,
    Prod.forall, mem_mul, Set.mem_univ, and_true]
  exact ⟨fun h a _ ↦ h a, fun h a ↦ h a a⟩

theorem rightUnique_iff : Relator.RightUnique (· ~[r] ·) ↔ star r * r ⊆ 1 := by
  simp [Relator.RightUnique, Set.subset_def]
  grind

theorem leftUnique_iff : Relator.LeftUnique (· ~[r] ·) ↔ r * star r ⊆ 1 := by
  simp [Relator.LeftUnique, Set.subset_def]

theorem reflOn_iff {s : Set α} : s.ReflOn (· ~[r] ·) ↔ ofSet s ⊆ r := by
  simp [Set.ReflOn, Set.subset_def]

theorem symmOn_iff {s : Set α} : s.SymmOn (· ~[r] ·) ↔ ofSet s * r * ofSet s ⊆ star r := by
  simp [Set.SymmOn, Set.subset_def]
  grind

theorem join_iff : Relation.Join (· ~[r] ·) x y ↔ x ~[r * star r] y := .rfl

theorem join₂_iff : Relation.Join₂ (· ~[s] ·) (· ~[r] ·) x y ↔ x ~[s * star r] y := .rfl

theorem diamondCommute_iff :
    Relation.DiamondCommute (· ~[s] ·) (· ~[r] ·) ↔ star s * r ⊆ r * star s := by
  simp [Relation.DiamondCommute, join₂_iff, Set.subset_def]
  grind

theorem diamond_iff : Relation.Diamond (· ~[r] ·) ↔ star r * r ⊆ r * star r :=
  diamondCommute_iff

theorem commute_iff : Relation.Commute (· ~[s] ·) (· ~[r] ·) ↔
    reflTransGen (star s) * reflTransGen r ⊆ reflTransGen r * reflTransGen (star s) := by
  rw [Relation.Commute, reflTransGen_eq, reflTransGen_eq, ← star_reflTransGen]
  exact diamondCommute_iff

theorem confluent_iff : Relation.Confluent (· ~[r] ·) ↔
    reflTransGen (star r) * reflTransGen r ⊆ reflTransGen r * reflTransGen (star r) :=
  commute_iff

theorem semiCommute_iff : Relation.SemiCommute (· ~[s] ·) (· ~[r] ·) ↔
    star s * reflTransGen r ⊆ reflTransGen r * reflTransGen (star s) := by
  simp [Relation.SemiCommute, reflTransGen_eq, Set.subset_def, ← star_reflTransGen, join₂_iff]
  grind

theorem semiConfluent_iff : Relation.SemiConfluent (· ~[r] ·) ↔
    star r * reflTransGen r ⊆ reflTransGen r * reflTransGen (star r) :=
  semiCommute_iff

theorem churchRosser_iff : Relation.ChurchRosser (· ~[r] ·) ↔
    reflTransGen (symmGen r) ⊆ reflTransGen r * reflTransGen (star r) := by
  simp [Relation.ChurchRosser, ← Relation.reflTransGen_symmGen, Set.subset_def, Relation.Join,
    reflTransGen_eq, ← symmGen_eq, ← star_reflTransGen]

theorem locallyCommute_iff : Relation.LocallyCommute (· ~[s] ·) (· ~[r] ·) ↔
    star s * r ⊆ reflTransGen r * reflTransGen (star s) := by
  simp [Relation.LocallyCommute, reflTransGen_eq, join₂_iff, Set.subset_def]
  grind

theorem locallyConfluent_iff : Relation.LocallyConfluent (· ~[r] ·) ↔
    star r * r ⊆ reflTransGen r * reflTransGen (star r) :=
  locallyCommute_iff

theorem stronglyCommute_iff : Relation.StronglyCommute (· ~[s] ·) (· ~[r] ·) ↔
    star s * r ⊆ reflGen r * reflTransGen (star s) := by
  simp [Relation.StronglyCommute, reflGen_eq, reflTransGen_eq, Set.subset_def, ← star_reflTransGen]
  grind

theorem stronglyConfluent_iff : Relation.StronglyConfluent (· ~[r] ·) ↔
    star r * r ⊆ reflGen r * reflTransGen (star r) :=
  stronglyCommute_iff

theorem ofSet_reducible_eq : ofSet {x | Relation.Reducible (· ~[r] ·) x} = relDom r := by
  rw [← ofSet_dom_eq]
  congr

theorem ofSet_normal_eq : ofSet {x | Relation.Normal (· ~[r] ·) x} = 1 \ relDom r := by
  rw [← ofSet_reducible_eq, one_eq_id, ← ofSet_compl_eq]
  congr

theorem ofSet_normalizable_eq :
    ofSet {x | Relation.Normalizable (· ~[r] ·) x} = relDom (reflTransGen r * (1 \ relDom r)) := by
  rw [← ofSet_dom_eq]
  congr
  simp [Relation.Normalizable, reflTransGen_iff_mem_reflTransGen, ← ofSet_dom_eq]

theorem normalizing_iff :
    Relation.Normalizing (· ~[r] ·) ↔ reflTransGen r * (1 \ relDom r) * ⊤ = ⊤ := by
  rw [← relDom_eq_one_iff, ← ofSet_normalizable_eq, Relation.Normalizing, one_eq_id,
    ofSet_eq_id_iff, Set.eq_univ_iff_forall]
  rfl

theorem ofSet_preimage_eq {s : Set α} : ofSet (r.preimage s) = relDom (r * ofSet s) := by
  simp [← ofSet_dom_eq, ofSet, and_comm]

theorem ofSet_image_eq {s : Set α} : ofSet (r.image s) = relCod (ofSet s * r) := by
  simp [← ofSet_cod_eq, ofSet]

theorem ofSet_core_eq {s : Set α} :
    ofSet (r.core s) = rightResidual (star r) (ofSet s * ⊤) ⊓ 1 := by
  ext ⟨a, b⟩
  simp [mem_rightResidual, and_comm]

end SetRel
