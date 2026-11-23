/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Order.AlgebraIntervals
public import Cslib.Foundations.Order.Setoid
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

class IsCoreflRA (a : α) : Prop where
  protected le_one : a ≤ 1

lemma one_le_of_refl (a : α) [IsReflRA a] : 1 ≤ a := IsReflRA.one_le

lemma isReflRA_iff {a : α} : IsReflRA a ↔ 1 ≤ a :=
  ⟨@IsReflRA.one_le _ _ a, IsReflRA.mk⟩

lemma star_eq_of_symm (a : α) [IsSymmRA a] : star a = a := IsSymmRA.star_eq

lemma isSymmRA_iff {a : α} : IsSymmRA a ↔ star a = a :=
  ⟨@IsSymmRA.star_eq _ _ a, IsSymmRA.mk⟩

lemma mul_self_le_of_trans (a : α) [IsTransRA a] : a * a ≤ a := IsTransRA.mul_self_le

lemma isTransRA_iff {a : α} : IsTransRA a ↔ a * a ≤ a :=
  ⟨@IsTransRA.mul_self_le _ _ a, IsTransRA.mk⟩

lemma le_one_of_corefl (a : α) [IsCoreflRA a] : a ≤ 1 := IsCoreflRA.le_one

lemma isCoreflRA_iff {a : α} : IsCoreflRA a ↔ a ≤ 1 :=
  ⟨@IsCoreflRA.le_one _ _ a, IsCoreflRA.mk⟩

open IsReflRA IsSymmRA IsTransRA

/-! ### Reflexive elements -/

instance : IsReflRA (1 : α) where
  one_le := le_rfl

instance : IsReflRA (⊤ : α) where
  one_le := le_top

instance [IsReflRA a] : IsReflRA (star a) where
  one_le := by simpa [le_star_iff] using one_le_of_refl a

lemma le_mul_left [hb : IsReflRA b] : a ≤ b * a := by
  nth_grw 1 [← one_mul a, one_le_of_refl b]

lemma le_mul_right [hb : IsReflRA b] : a ≤ a * b := by
  nth_grw 1 [← mul_one a, one_le_of_refl b]

instance [RelationAlgebra β] (F : Type*) [FunLike F α β] [OrderHomClass F α β] [OneHomClass F α β]
    (f : F) (a : α) [IsReflRA a] : IsReflRA (f a) where
  one_le := by grw [← map_one f, one_le_of_refl a]

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

instance [IsSymmRA a] : IsSymmRA (star a) where
  star_eq := (star_star a).trans (star_eq_of_symm a).symm

lemma IsSymmRA.of_star_le (ha : star a ≤ a) : IsSymmRA a where
  star_eq := ha.antisymm <| le_star_iff.mpr ha

lemma IsSymmRA.of_le_star (ha : a ≤ star a) : IsSymmRA a where
  star_eq := (le_star_iff.mp ha).antisymm ha

instance [RelationAlgebra β] (F : Type*) [FunLike F α β] [StarHomClass F α β]
    (f : F) (a : α) [IsSymmRA a] : IsSymmRA (f a) where
  star_eq := by rw [← map_star f, star_eq_of_symm]

def symmGenRA (a : α) : α := a ⊔ star a

instance : IsSymmRA (symmGenRA a) where
  star_eq := by simp [symmGenRA, sup_comm]

lemma le_symmGenRA : a ≤ symmGenRA a := le_sup_left

lemma symmGenRA_le [IsSymmRA b] : symmGenRA a ≤ b ↔ a ≤ b := by
  simp [symmGenRA, star_le_iff, star_eq_of_symm]

lemma star_le_iff_of_isSymmRA [IsSymmRA b] : star a ≤ b ↔ a ≤ b := by
  simp [star_le_iff, star_eq_of_symm]

/-! ### Transitive elements -/

instance : IsTransRA (⊥ : α) where
  mul_self_le := (mul_bot ⊥).le

instance : IsTransRA (1 : α) where
  mul_self_le := (mul_one 1).le

instance : IsTransRA (⊤ : α) where
  mul_self_le := le_top

instance [IsTransRA a] : IsTransRA (star a) where
  mul_self_le := by grw [← star_mul, mul_self_le_of_trans a]

lemma mul_le_of_isTransRA [IsTransRA c] (ha : a ≤ c) (hb : b ≤ c) : a * b ≤ c := by
  grw [← mul_self_le_of_trans c, ha, hb]

instance [RelationAlgebra β] (F : Type*) [FunLike F α β] [OrderHomClass F α β] [MulHomClass F α β]
    (f : F) (a : α) [IsTransRA a] : IsTransRA (f a) where
  mul_self_le := by grw [← map_mul f, mul_self_le_of_trans a]

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

/-! ### Coreflexive elements -/

instance : IsCoreflRA (⊥ : α) where
  le_one := bot_le

instance : IsCoreflRA (1 : α) where
  le_one := le_rfl

lemma mul_left_le [IsCoreflRA a] : a * b ≤ b := by grw [le_one_of_corefl a, one_mul b]

lemma mul_right_le [IsCoreflRA b] : a * b ≤ a := by grw [le_one_of_corefl b, mul_one a]

instance [IsCoreflRA a] : IsSymmRA a := by
  apply IsSymmRA.of_le_star
  grw [le_mul_star_mul a, mul_right_le, mul_left_le]

instance [IsCoreflRA a] : IsCoreflRA (star a) := by
  rw [star_eq_of_symm]
  infer_instance

instance [IsCoreflRA a] : IsTransRA a where
  mul_self_le := mul_left_le

lemma mul_self_of_isCoreflRA (a : α) [IsCoreflRA a] : a * a = a := by
  apply (mul_self_le_of_trans a).antisymm
  grw [le_mul_star_mul a, mul_right_le (b := star a)]

def domRA (a : α) : α := a * ⊤ ⊓ 1

instance : IsCoreflRA (domRA a) where
  le_one := inf_le_right

lemma domRA_le_iff_mul_le [IsCoreflRA b] : domRA a ≤ b ↔ a ≤ b * a := by
  constructor <;> intro h
  · grw [← h, domRA, inf_comm, ← le_top (a := star a), ← right_modular]
    simp
  · grw [domRA, h, mul_assoc, left_modular, inf_le_right, mul_one, star_eq_of_symm,
      mul_self_le_of_trans]

lemma domRA_le_iff [IsCoreflRA b] : domRA a ≤ b ↔ b * a = a := by
  simp_rw [le_antisymm_iff, mul_left_le, true_and, domRA_le_iff_mul_le]

lemma domRA_mul_self : domRA a * a = a := by rw [← domRA_le_iff]

lemma domRA_of_isCoreflRA [IsCoreflRA a] : domRA a = a := by
  apply le_antisymm
  · rw [domRA_le_iff_mul_le, mul_self_of_isCoreflRA]
  · refine le_inf ?_ (le_one_of_corefl a)
    nth_grw 1 [← mul_self_of_isCoreflRA a, ← le_top (a := a)]

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

@[simps]
def _root_.RelationAlgebraEquiv.IicOfEq {a b : α} (h : a = b)
    [IsReflRA a] [IsSymmRA a] [IsTransRA a] [IsReflRA b] [IsSymmRA b] [IsTransRA b] :
    RelationAlgebraEquiv (Set.Iic a) (Set.Iic b) where
  toFun x := ⟨x, x.prop.trans_eq h⟩
  invFun y := ⟨y, y.prop.trans_eq h.symm⟩
  map_rel_iff' := .rfl
  map_mul' _ _ := Subtype.ext rfl
  map_star' _ := Subtype.ext rfl

@[simps]
def equivIic {α β : Type*} [RelationAlgebra α] [RelationAlgebra β] (e : RelationAlgebraEquiv α β)
    {a : α} [IsReflRA a] [IsSymmRA a] [IsTransRA a]
    {b : β} [IsReflRA b] [IsSymmRA b] [IsTransRA b]
    (h : e a = b) : RelationAlgebraEquiv (Set.Iic a) (Set.Iic b) where
  toFun x := ⟨e x, (e.mono x.prop).trans_eq h⟩
  invFun y := ⟨e.symm y, (e.symm.mono y.prop).trans_eq <| by simp [← h]⟩
  map_rel_iff' := e.map_rel_iff
  map_mul' _ _ := Subtype.ext <| e.map_mul ..
  map_star' _ := Subtype.ext <| e.map_star' _
  left_inv _ := by simp
  right_inv _ := by simp

/-! ### Properties for `SetRel` -/

section SetRel

open SetRel

omit [RelationAlgebra α]

lemma isReflRA_iff_setRel_isRefl (r : SetRel α α) : IsReflRA r ↔ r.IsRefl := by
  simp [isReflRA_iff, ← SetRel.id_subset_iff]
  rfl

instance (r : SetRel α α) [h : SetRel.IsRefl r] : IsReflRA r :=
  (isReflRA_iff_setRel_isRefl r).mpr h

lemma isSymmRA_iff_setRel_isSymm (r : SetRel α α) : IsSymmRA r ↔ r.IsSymm := by
  simp [isSymmRA_iff, ← SetRel.inv_eq_self_iff, star]

instance (r : SetRel α α) [h : SetRel.IsSymm r] : IsSymmRA r :=
  (isSymmRA_iff_setRel_isSymm r).mpr h

lemma isTransRA_iff_setRel_isTrans (r : SetRel α α) : IsTransRA r ↔ r.IsTrans := by
  simp [isTransRA_iff, SetRel.isTrans_iff_comp_subset_self]
  rfl

instance (r : SetRel α α) [h : SetRel.IsTrans r] : IsTransRA r :=
  (isTransRA_iff_setRel_isTrans r).mpr h

def ofSet (s : Set α) : SetRel α α := {(x, x) | x ∈ s}

@[simp, grind =] lemma mem_ofSet {s : Set α} : x ~[ofSet s] y ↔ x ∈ s ∧ x = y := by
  grind [ofSet]

@[grind .] lemma eq_of_mem_ofSet {s : Set α} (h : x ~[ofSet s] y) : x = y := by grind

@[grind .] lemma left_mem_of_mem_ofSet {s : Set α} (h : x ~[ofSet s] y) : x ∈ s := by grind

@[grind .] lemma right_mem_of_mem_ofSet {s : Set α} (h : x ~[ofSet s] y) : y ∈ s := by grind

lemma isCoreflRA_iff_eq_ofSet (r : SetRel α α) : IsCoreflRA r ↔ ∃ s, r = ofSet s := by
  constructor
  · intro ⟨h⟩
    use r.dom
    ext ⟨x, y⟩
    rw [mem_ofSet, mem_dom]
    constructor
    · intro hxy
      exact ⟨⟨y, hxy⟩, h hxy⟩
    · rintro ⟨⟨y, hxy⟩, rfl⟩
      simpa [(h hxy : x = y).symm] using hxy
  · rintro ⟨s, rfl⟩
    simp [isCoreflRA_iff, Set.subset_def]

instance (s : Set α) : IsCoreflRA (ofSet s) := isCoreflRA_iff_eq_ofSet _ |>.mpr ⟨s, rfl⟩

lemma dom_eq_ofSet (r : SetRel α α) : domRA r = ofSet r.dom := by
  ext ⟨x, y⟩
  simp [domRA]

def toSetoid (r : SetRel α α) [IsReflRA r] [IsSymmRA r] [IsTransRA r] : Setoid α where
  r x y := (x, y) ∈ r
  iseqv :=
    ⟨(isReflRA_iff_setRel_isRefl r).mp inferInstance |>.refl,
      fun h ↦  (isSymmRA_iff_setRel_isSymm r).mp inferInstance |>.symm _ _ h,
      fun h h' ↦ (isTransRA_iff_setRel_isTrans r).mp inferInstance |>.trans _ _ _ h h' ⟩

lemma ofRel_toSetoid (r : SetRel α α) [IsReflRA r] [IsSymmRA r] [IsTransRA r] :
    .ofRel (toSetoid r) = r := rfl

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
@[simps! toFun]
noncomputable def piToSigmaEquiv (ι : Type v) (α : ι → Type w) :
    RelationAlgebraEquiv (Π i, SetRel (α i) (α i)) (Set.Iic <| prodRepresentation' ι α ⊤) :=
  .ofBijective (prodRepresentation' ι α).toHom <| by
    refine ⟨(prodRepresentation' ι α).toHom_injective, ?_⟩
    simp_rw [Function.Surjective, Subtype.ext_iff, Subtype.forall, Set.mem_Iic,
        Representation'.toHom_toFun_coe, prodRepresentation'_toFun]
    intro r hr
    use fun i ↦ {p | ⟨i, p.1⟩ ~[r] ⟨i, p.2⟩}
    grind

lemma prodRepresentation'_top (ι : Type v) (α : ι → Type w) :
    prodRepresentation' ι α ⊤ = SetRel.sigmaSetoid α α :=
  SetRel.piToSigma_top_eq_sigmaSetoid

open SetRel

@[simps]
def piToSigmaHom' (ι : Type v) (α : ι → Type w) :
    RelationAlgebraHom (Π i, SetRel (α i) (α i)) (Set.Iic <| sigmaSetoid α α) where
  toFun r := ⟨prodRepresentation' ι α r, by
    simp [← piToSigma_top_eq_sigmaSetoid, piToSigma_subset_iff]⟩
  map_sup' _ _ := Subtype.ext piToSigma_union
  map_inf' _ _ := Subtype.ext piToSigma_inter
  map_one' := Subtype.ext piToSigma_id
  map_mul' _ _ := Subtype.ext piToSigma_comp
  map_star' _ := Subtype.ext piToSigma_inv
  map_bot' := Subtype.ext piToSigma_bot
  map_top' := Subtype.ext piToSigma_top_eq_sigmaSetoid

noncomputable def piToSigmaEquiv' (ι : Type v) (α : ι → Type w) :
    RelationAlgebraEquiv (Π i, SetRel (α i) (α i)) (Set.Iic <| SetRel.sigmaSetoid α α) :=
  (piToSigmaEquiv ι α).trans <| RelationAlgebraEquiv.IicOfEq <| by
    simp [piToSigma_top_eq_sigmaSetoid]

@[simp]
lemma piToSigmaEquiv'_apply {ι : Type v} {α : ι → Type w} (r : Π i, SetRel (α i) (α i)) :
    (piToSigmaEquiv' ι α r : SetRel (Σ i, α i) (Σ i, α i)) = piToSigma r := rfl

noncomputable def equivIicPi {α : Type*} (s : SetRel α α) [IsReflRA s] [IsSymmRA s] [IsTransRA s] :
    RelationAlgebraEquiv (Set.Iic s)
      (Π i, SetRel ((toSetoid s).eqvClass i) ((toSetoid s).eqvClass i)) :=
  RelationAlgebraEquiv.trans
    (equivIic (RelationAlgebraEquiv.ofEquivSetRel (toSetoid s).toIndexedPartition.equivSigma) <|
      Setoid.equivSigma_map_eq_sigmaSetoid (toSetoid s))
    (piToSigmaEquiv' _ _).symm

noncomputable def Representation'.toRepresentation {α β : Type*} [RelationAlgebra α]
    (R : Representation' α β) :
    Representation α (Quotient <| toSetoid <| R ⊤) ((toSetoid <| R ⊤).eqvClass ·) where
  hom := (equivIicPi <| R ⊤).toHom.comp R.toHom
  injective := (equivIicPi <| R ⊤).toHom_injective.comp R.toHom_injective

end Cslib.RelationAlgebra
