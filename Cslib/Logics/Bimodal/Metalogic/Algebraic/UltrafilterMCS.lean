/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Algebraic.InteriorOperators
public import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties

/-!
# Ultrafilter-MCS Correspondence

This module establishes the bijection between ultrafilters of the Lindenbaum algebra
and maximal consistent sets.

## Main Results

- `mcsToUltrafilter`: MCS -> BoolAlgUltrafilter LindenbaumAlg
- `ultrafilter_to_mcs`: BoolAlgUltrafilter LindenbaumAlg -> MCS
- The two maps are inverses

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/Algebraic/UltrafilterMCS.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Algebraic.UltrafilterMCS

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Algebraic.LindenbaumQuotient
open Cslib.Logic.Bimodal.Metalogic.Algebraic.BooleanStructure
open Cslib.Logic.Bimodal.Metalogic.Core

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-- Local abbreviation for derivation at Base frame class. -/
local notation:50 Γ " ⊢ᴮ " φ => DerivationTree FrameClass.Base Γ φ

/-!
## Ultrafilter Definition for Boolean Algebras
-/

/--
An ultrafilter on a Boolean algebra. Named BoolAlgUltrafilter to avoid
collision with Mathlib's Ultrafilter.
-/
structure BoolAlgUltrafilter (α : Type*) [BooleanAlgebra α] where
  carrier : Set α
  top_mem : ⊤ ∈ carrier
  bot_not_mem : ⊥ ∉ carrier
  mem_of_le : ∀ {a b}, a ∈ carrier → a ≤ b → b ∈ carrier
  inf_mem : ∀ {a b}, a ∈ carrier → b ∈ carrier → a ⊓ b ∈ carrier
  compl_or : ∀ a, a ∈ carrier ∨ aᶜ ∈ carrier
  compl_not : ∀ a, a ∈ carrier → aᶜ ∉ carrier

@[ext]
theorem BoolAlgUltrafilter.ext {α : Type*} [BooleanAlgebra α] {uf1 uf2 : BoolAlgUltrafilter α}
    (h : uf1.carrier = uf2.carrier) : uf1 = uf2 := by
  cases uf1; cases uf2
  simp only [BoolAlgUltrafilter.mk.injEq]
  exact h

/-!
## MCS to Ultrafilter Direction
-/

def mcsToSet (Γ : Set (Formula Atom)) : Set (LindenbaumAlg Atom) :=
  { a | ∃ φ ∈ Γ, a = toQuot φ }

theorem mem_mcsToSet {Γ : Set (Formula Atom)} {φ : Formula Atom} (h : φ ∈ Γ) :
    toQuot φ ∈ mcsToSet Γ :=
  ⟨φ, h, rfl⟩

theorem mcsToSet_top {Γ : Set (Formula Atom)} (h_mcs : SetMaximalConsistent FrameClass.Base Γ) :
    ⊤ ∈ mcsToSet Γ := by
  have d_id : DerivationTree FrameClass.Base [] ((Formula.bot : Formula Atom).imp Formula.bot) :=
    Theorems.Combinators.identity Formula.bot
  have h : (Formula.bot : Formula Atom).imp Formula.bot ∈ Γ :=
    SetMaximalConsistent.closed_under_derivation h_mcs [] (fun _ h => by simp at h) d_id
  exact ⟨(Formula.bot : Formula Atom).imp Formula.bot, h, rfl⟩

theorem mcsToSet_bot_not_mem {Γ : Set (Formula Atom)} (h_mcs : SetMaximalConsistent FrameClass.Base Γ) :
    ⊥ ∉ mcsToSet Γ := by
  intro ⟨φ, h_mem, h_eq⟩
  have h_le : toQuot φ ≤ (⊥ : LindenbaumAlg Atom) := by rw [← h_eq]
  have h_derives : Derives φ Formula.bot := h_le
  obtain ⟨d_neg⟩ := h_derives
  have h_phi_incons : ¬Consistent (fc := FrameClass.Base) [φ] := by
    intro h_cons
    have d_phi : DerivationTree FrameClass.Base [φ] φ := DerivationTree.assumption [φ] φ (by simp)
    have d_bot : DerivationTree FrameClass.Base [φ] Formula.bot := DerivationTree.modus_ponens [φ] φ Formula.bot
      (DerivationTree.weakening [] [φ] (Formula.neg φ) d_neg (by simp)) d_phi
    exact h_cons ⟨d_bot⟩
  have h_cons : Consistent (fc := FrameClass.Base) [φ] := h_mcs.1 [φ] (by simp [h_mem])
  exact h_phi_incons h_cons

theorem mcsToSet_mem_of_le {Γ : Set (Formula Atom)} (h_mcs : SetMaximalConsistent FrameClass.Base Γ)
    {a b : LindenbaumAlg Atom} (ha : a ∈ mcsToSet Γ) (h_le : a ≤ b) :
    b ∈ mcsToSet Γ := by
  obtain ⟨φ, h_phi_mem, h_a_eq⟩ := ha
  induction b using Quotient.ind with
  | _ ψ =>
    rw [h_a_eq] at h_le
    have h_derives : Derives φ ψ := h_le
    obtain ⟨d_imp⟩ := h_derives
    have h_psi_in : ψ ∈ Γ := by
      by_contra h_not
      have h_incons : ¬SetConsistent FrameClass.Base (insert ψ Γ) := h_mcs.2 ψ h_not
      unfold SetConsistent at h_incons
      push_neg at h_incons
      obtain ⟨L, hL, hL_incons⟩ := h_incons
      have ⟨d_bot⟩ := inconsistent_derives_bot hL_incons
      let Γ' := L.filter (· ≠ ψ)
      have h_Γ'_sub : ∀ χ ∈ Γ', χ ∈ Γ := by
        intro χ hχ
        have hχ' := List.mem_filter.mp hχ
        have hχne : χ ≠ ψ := by simpa using hχ'.2
        specialize hL χ hχ'.1
        simp [Set.mem_insert_iff] at hL
        rcases hL with rfl | h_in_Γ
        · exact absurd rfl hχne
        · exact h_in_Γ
      have h_L_sub : L ⊆ ψ :: Γ' := by
        intro χ hχ
        by_cases hχψ : χ = ψ
        · simp [hχψ]
        · simp only [List.mem_cons]; right
          exact List.mem_filter.mpr ⟨hχ, by simpa⟩
      have d_bot' := DerivationTree.weakening L (ψ :: Γ') Formula.bot d_bot h_L_sub
      have d_neg_ψ := deduction_theorem Γ' ψ Formula.bot d_bot'
      have d_neg_ψ' := DerivationTree.weakening Γ' (φ :: Γ') ψ.neg d_neg_ψ
        (fun x hx => List.mem_cons_of_mem φ hx)
      have d_imp' := DerivationTree.weakening [] (φ :: Γ') (φ.imp ψ) d_imp (by simp)
      have d_φ : DerivationTree FrameClass.Base (φ :: Γ') φ := DerivationTree.assumption (φ :: Γ') φ (by simp)
      have d_ψ : DerivationTree FrameClass.Base (φ :: Γ') ψ := DerivationTree.modus_ponens (φ :: Γ') φ ψ d_imp' d_φ
      have d_bot'' : DerivationTree FrameClass.Base (φ :: Γ') Formula.bot := DerivationTree.modus_ponens (φ :: Γ') ψ Formula.bot d_neg_ψ' d_ψ
      have h_cons_list : Consistent (fc := FrameClass.Base) (φ :: Γ') := by
        apply h_mcs.1 (φ :: Γ')
        intro χ hχ
        simp at hχ
        rcases hχ with rfl | hχ'
        · exact h_phi_mem
        · exact h_Γ'_sub χ hχ'
      exact h_cons_list ⟨d_bot''⟩
    exact ⟨ψ, h_psi_in, rfl⟩

theorem mcsToSet_inf_mem {Γ : Set (Formula Atom)} (h_mcs : SetMaximalConsistent FrameClass.Base Γ)
    {a b : LindenbaumAlg Atom} (ha : a ∈ mcsToSet Γ) (hb : b ∈ mcsToSet Γ) :
    a ⊓ b ∈ mcsToSet Γ := by
  obtain ⟨φ, h_phi_mem, h_a_eq⟩ := ha
  obtain ⟨ψ, h_psi_mem, h_b_eq⟩ := hb
  have h_and_in : φ.and ψ ∈ Γ := by
    by_contra h_not
    have h_incons : ¬SetConsistent FrameClass.Base (insert (φ.and ψ) Γ) := h_mcs.2 (φ.and ψ) h_not
    unfold SetConsistent at h_incons
    push_neg at h_incons
    obtain ⟨L, hL, hL_incons⟩ := h_incons
    have ⟨d_bot⟩ := inconsistent_derives_bot hL_incons
    let Γ' := L.filter (· ≠ φ.and ψ)
    have h_Γ'_sub : ∀ χ ∈ Γ', χ ∈ Γ := by
      intro χ hχ
      have hχ' := List.mem_filter.mp hχ
      have hχne : χ ≠ φ.and ψ := by simpa using hχ'.2
      specialize hL χ hχ'.1
      simp [Set.mem_insert_iff] at hL
      rcases hL with rfl | h_in_Γ
      · exact absurd rfl hχne
      · exact h_in_Γ
    have h_L_sub : L ⊆ (φ.and ψ) :: Γ' := by
      intro χ hχ
      by_cases hχeq : χ = φ.and ψ
      · simp [hχeq]
      · simp only [List.mem_cons]; right
        exact List.mem_filter.mpr ⟨hχ, by simpa⟩
    have d_bot' := DerivationTree.weakening L ((φ.and ψ) :: Γ') Formula.bot d_bot h_L_sub
    have d_neg := deduction_theorem Γ' (φ.and ψ) Formula.bot d_bot'
    have d_neg' := DerivationTree.weakening Γ' (ψ :: φ :: Γ') (φ.and ψ).neg d_neg
      (fun x hx => by simp; right; right; exact hx)
    have d_φ : (ψ :: φ :: Γ') ⊢ᴮ φ := DerivationTree.assumption (ψ :: φ :: Γ') φ (by simp)
    have d_ψ : (ψ :: φ :: Γ') ⊢ᴮ ψ := DerivationTree.assumption (ψ :: φ :: Γ') ψ (by simp)
    have d_and : (ψ :: φ :: Γ') ⊢ᴮ φ.and ψ := by
      have d_hyp : (φ.imp ψ.neg :: ψ :: φ :: Γ') ⊢ᴮ φ.imp ψ.neg :=
        DerivationTree.assumption _ _ (by simp)
      have d_φ' : (φ.imp ψ.neg :: ψ :: φ :: Γ') ⊢ᴮ φ :=
        DerivationTree.assumption _ _ (by simp)
      have d_ψ' : (φ.imp ψ.neg :: ψ :: φ :: Γ') ⊢ᴮ ψ :=
        DerivationTree.assumption _ _ (by simp)
      have d_neg_ψ' := DerivationTree.modus_ponens (φ.imp ψ.neg :: ψ :: φ :: Γ') φ ψ.neg d_hyp d_φ'
      have d_bot' := DerivationTree.modus_ponens (φ.imp ψ.neg :: ψ :: φ :: Γ') ψ Formula.bot d_neg_ψ' d_ψ'
      exact deduction_theorem (ψ :: φ :: Γ') (φ.imp ψ.neg) Formula.bot d_bot'
    have d_bot'' := DerivationTree.modus_ponens (ψ :: φ :: Γ') (φ.and ψ) Formula.bot d_neg' d_and
    have h_cons : Consistent (fc := FrameClass.Base) (ψ :: φ :: Γ') := by
      apply h_mcs.1 (ψ :: φ :: Γ')
      intro χ hχ
      simp at hχ
      rcases hχ with rfl | rfl | hχ'
      · exact h_psi_mem
      · exact h_phi_mem
      · exact h_Γ'_sub χ hχ'
    exact h_cons ⟨d_bot''⟩
  use φ.and ψ, h_and_in
  rw [h_a_eq, h_b_eq]
  rfl

theorem mcsToSet_compl_or {Γ : Set (Formula Atom)} (h_mcs : SetMaximalConsistent FrameClass.Base Γ)
    (a : LindenbaumAlg Atom) : a ∈ mcsToSet Γ ∨ aᶜ ∈ mcsToSet Γ := by
  induction a using Quotient.ind with
  | _ φ =>
    by_cases h : φ ∈ Γ
    · left; exact ⟨φ, h, rfl⟩
    · right
      have h_incons : ¬SetConsistent FrameClass.Base (insert φ Γ) := h_mcs.2 φ h
      unfold SetConsistent at h_incons
      push_neg at h_incons
      obtain ⟨L, hL, hL_incons⟩ := h_incons
      have ⟨d_bot⟩ := inconsistent_derives_bot hL_incons
      let Γ' := L.filter (· ≠ φ)
      have h_Γ'_sub : ∀ χ ∈ Γ', χ ∈ Γ := by
        intro χ hχ
        have hχ' := List.mem_filter.mp hχ
        have hχne : χ ≠ φ := by simpa using hχ'.2
        specialize hL χ hχ'.1
        simp [Set.mem_insert_iff] at hL
        rcases hL with rfl | h_in_Γ
        · exact absurd rfl hχne
        · exact h_in_Γ
      have h_L_sub : L ⊆ φ :: Γ' := by
        intro χ hχ
        by_cases hχeq : χ = φ
        · simp [hχeq]
        · simp only [List.mem_cons]; right
          exact List.mem_filter.mpr ⟨hχ, by simpa⟩
      have d_bot' := DerivationTree.weakening L (φ :: Γ') Formula.bot d_bot h_L_sub
      have d_neg := deduction_theorem Γ' φ Formula.bot d_bot'
      have h_neg_in : φ.neg ∈ Γ := by
        by_contra h_neg_not
        have h_incons' : ¬SetConsistent FrameClass.Base (insert φ.neg Γ) := h_mcs.2 φ.neg h_neg_not
        unfold SetConsistent at h_incons'
        push_neg at h_incons'
        obtain ⟨L', hL', hL'_incons⟩ := h_incons'
        have ⟨d_bot'⟩ := inconsistent_derives_bot hL'_incons
        let Γ'' := L'.filter (· ≠ φ.neg)
        have h_Γ''_sub : ∀ χ ∈ Γ'', χ ∈ Γ := by
          intro χ hχ
          have hχ' := List.mem_filter.mp hχ
          have hχne : χ ≠ φ.neg := by simpa using hχ'.2
          specialize hL' χ hχ'.1
          simp [Set.mem_insert_iff] at hL'
          rcases hL' with rfl | h_in_Γ
          · exact absurd rfl hχne
          · exact h_in_Γ
        have h_L'_sub : L' ⊆ φ.neg :: Γ'' := by
          intro χ hχ
          by_cases hχeq : χ = φ.neg
          · simp [hχeq]
          · simp only [List.mem_cons]; right
            exact List.mem_filter.mpr ⟨hχ, by simp [hχeq]⟩
        have d_bot'' := DerivationTree.weakening L' (φ.neg :: Γ'') Formula.bot d_bot' h_L'_sub
        have d_neg_neg := deduction_theorem Γ'' φ.neg Formula.bot d_bot''
        have d_dne : DerivationTree FrameClass.Base [] (φ.neg.neg.imp φ) :=
          Theorems.Propositional.double_negation φ
        have d_dne' := DerivationTree.weakening [] Γ'' _ d_dne (by simp)
        have d_φ := DerivationTree.modus_ponens Γ'' φ.neg.neg φ d_dne' d_neg_neg
        have d_neg_combined := DerivationTree.weakening Γ' (Γ'' ++ Γ') φ.neg d_neg (by simp)
        have d_φ_combined := DerivationTree.weakening Γ'' (Γ'' ++ Γ') φ d_φ (by simp)
        have d_bot_combined := DerivationTree.modus_ponens (Γ'' ++ Γ') φ Formula.bot d_neg_combined d_φ_combined
        have h_combined_cons : Consistent (fc := FrameClass.Base) (Γ'' ++ Γ') := by
          apply h_mcs.1 (Γ'' ++ Γ')
          intro χ hχ
          simp at hχ
          rcases hχ with hχ'' | hχ'
          · exact h_Γ''_sub χ hχ''
          · exact h_Γ'_sub χ hχ'
        exact h_combined_cons ⟨d_bot_combined⟩
      use φ.neg, h_neg_in
      rfl

theorem mcsToSet_compl_not {Γ : Set (Formula Atom)} (h_mcs : SetMaximalConsistent FrameClass.Base Γ)
    {a : LindenbaumAlg Atom} (ha : a ∈ mcsToSet Γ) : aᶜ ∉ mcsToSet Γ := by
  obtain ⟨φ, h_phi_mem, h_a_eq⟩ := ha
  intro ⟨ψ, h_psi_mem, h_compl_eq⟩
  rw [h_a_eq] at h_compl_eq
  have h_eq : toQuot φ.neg = toQuot ψ := h_compl_eq
  have h_le1 : toQuot ψ ≤ toQuot φ.neg := by rw [← h_eq]
  obtain ⟨d_imp⟩ := (h_le1 : Derives ψ φ.neg)
  have d_φ : [φ, ψ] ⊢ᴮ φ := DerivationTree.assumption [φ, ψ] φ (by simp)
  have d_ψ : [φ, ψ] ⊢ᴮ ψ := DerivationTree.assumption [φ, ψ] ψ (by simp)
  have d_imp' : [φ, ψ] ⊢ᴮ ψ.imp φ.neg := DerivationTree.weakening [] [φ, ψ] (ψ.imp φ.neg) d_imp (by simp)
  have d_neg : [φ, ψ] ⊢ᴮ φ.neg := DerivationTree.modus_ponens [φ, ψ] ψ φ.neg d_imp' d_ψ
  have d_bot : [φ, ψ] ⊢ᴮ Formula.bot := DerivationTree.modus_ponens [φ, ψ] φ Formula.bot d_neg d_φ
  have h_cons : Consistent (fc := FrameClass.Base) [φ, ψ] := by
    apply h_mcs.1 [φ, ψ]
    intro χ hχ
    simp at hχ
    rcases hχ with rfl | rfl
    · exact h_phi_mem
    · exact h_psi_mem
  exact h_cons ⟨d_bot⟩

/-!
## MCS to Ultrafilter Construction
-/

def mcsToUltrafilter (Γ : {Omega : Set (Formula Atom) // SetMaximalConsistent FrameClass.Base Omega}) :
    BoolAlgUltrafilter (LindenbaumAlg Atom) where
  carrier := mcsToSet Γ.val
  top_mem := mcsToSet_top Γ.property
  bot_not_mem := mcsToSet_bot_not_mem Γ.property
  mem_of_le := fun ha h_le => mcsToSet_mem_of_le Γ.property ha h_le
  inf_mem := fun ha hb => mcsToSet_inf_mem Γ.property ha hb
  compl_or := mcsToSet_compl_or Γ.property
  compl_not := fun _ ha => mcsToSet_compl_not Γ.property ha

@[simp]
theorem mcsToUltrafilter_carrier (Γ : {Omega : Set (Formula Atom) // SetMaximalConsistent FrameClass.Base Omega}) :
    (mcsToUltrafilter Γ).carrier = mcsToSet Γ.val := rfl

/-!
## Fold-Derives Lemma
-/

theorem fold_le_of_derives (L : List (Formula Atom)) (ψ : Formula Atom)
    (h : DerivationTree FrameClass.Base L ψ) :
    List.foldl (fun acc φ => acc ⊓ toQuot φ) ⊤ L ≤ toQuot ψ := by
  induction L generalizing ψ with
  | nil =>
    simp only [List.foldl_nil]
    show top_quot ≤ toQuot ψ
    unfold top_quot
    show Derives ((Formula.bot : Formula Atom).imp Formula.bot) ψ
    unfold Derives
    have d_s : DerivationTree FrameClass.Base (Atom := Atom) [] (ψ.imp (((Formula.bot : Formula Atom).imp Formula.bot).imp ψ)) :=
      DerivationTree.axiom [] _ (Axiom.imp_s ψ ((Formula.bot : Formula Atom).imp Formula.bot)) trivial
    exact ⟨DerivationTree.modus_ponens [] _ _ d_s h⟩
  | cons φ L' ih =>
    simp only [List.foldl_cons]
    have d_imp := deduction_theorem L' φ ψ h
    have ih_applied := ih (φ.imp ψ) d_imp
    have fold_from_x : ∀ (M : List (Formula Atom)) (x : LindenbaumAlg Atom),
        List.foldl (fun acc χ => acc ⊓ toQuot χ) x M =
        x ⊓ List.foldl (fun acc χ => acc ⊓ toQuot χ) ⊤ M := by
      intro M
      induction M with
      | nil => intro x; simp
      | cons m M' ih_M =>
        intro x
        simp only [List.foldl_cons]
        rw [ih_M (x ⊓ toQuot m), ih_M (⊤ ⊓ toQuot m)]
        simp only [top_inf_eq]
        rw [← inf_assoc]
    rw [fold_from_x L' (⊤ ⊓ toQuot φ)]
    simp only [top_inf_eq]
    have mp_le : toQuot φ ⊓ toQuot (φ.imp ψ) ≤ toQuot ψ := by
      show and_quot (toQuot φ) (toQuot (φ.imp ψ)) ≤ toQuot ψ
      change Derives (φ.and (φ.imp ψ)) ψ
      unfold Derives
      have h_ctx : DerivationTree FrameClass.Base [φ.and (φ.imp ψ)] ψ := by
        have h_conj : [φ.and (φ.imp ψ)] ⊢ᴮ φ.and (φ.imp ψ) :=
          DerivationTree.assumption [φ.and (φ.imp ψ)] (φ.and (φ.imp ψ)) (by simp)
        have h_φ : DerivationTree FrameClass.Base [φ.and (φ.imp ψ)] φ := by
          apply DerivationTree.modus_ponens [φ.and (φ.imp ψ)] _ _
          · apply DerivationTree.weakening [] [φ.and (φ.imp ψ)]
            · exact Theorems.Propositional.lce_imp φ (φ.imp ψ)
            · intro; simp
          · exact h_conj
        have h_imp : DerivationTree FrameClass.Base [φ.and (φ.imp ψ)] (φ.imp ψ) := by
          apply DerivationTree.modus_ponens [φ.and (φ.imp ψ)] _ _
          · apply DerivationTree.weakening [] [φ.and (φ.imp ψ)]
            · exact Theorems.Propositional.rce_imp φ (φ.imp ψ)
            · intro; simp
          · exact h_conj
        exact DerivationTree.modus_ponens [φ.and (φ.imp ψ)] φ ψ h_imp h_φ
      exact ⟨deduction_theorem [] (φ.and (φ.imp ψ)) ψ h_ctx⟩
    calc toQuot φ ⊓ List.foldl (fun acc χ => acc ⊓ toQuot χ) ⊤ L'
        ≤ toQuot φ ⊓ toQuot (φ.imp ψ) := inf_le_inf_left (toQuot φ) ih_applied
      _ ≤ toQuot ψ := mp_le

/-!
## Ultrafilter to MCS Direction
-/

def ultrafilterToSet (uf : BoolAlgUltrafilter (LindenbaumAlg Atom)) : Set (Formula Atom) :=
  { φ | toQuot φ ∈ uf.carrier }

theorem ultrafilterToSet_mcs (uf : BoolAlgUltrafilter (LindenbaumAlg Atom)) :
    SetMaximalConsistent FrameClass.Base (ultrafilterToSet uf) := by
  constructor
  · intro L hL
    intro ⟨d_bot⟩
    have h_meet_in_uf : ∀ M : List (Formula Atom), (∀ ψ ∈ M, toQuot ψ ∈ uf.carrier) →
        List.foldl (fun acc φ => acc ⊓ toQuot φ) ⊤ M ∈ uf.carrier := by
      intro M
      induction M with
      | nil => intro _; exact uf.top_mem
      | cons ψ M ih =>
        intro hM
        have h_ψ := hM ψ (by simp)
        have h_rest : ∀ φ ∈ M, toQuot φ ∈ uf.carrier := fun φ hφ => hM φ (by simp [hφ])
        simp only [List.foldl_cons]
        have h_fold_preserves : ∀ N : List (Formula Atom), (∀ φ ∈ N, toQuot φ ∈ uf.carrier) →
            ∀ x : LindenbaumAlg Atom, x ∈ uf.carrier →
            List.foldl (fun acc φ => acc ⊓ toQuot φ) x N ∈ uf.carrier := by
          intro N
          induction N with
          | nil => intro _ x hx; simp; exact hx
          | cons m N ih_N =>
            intro hN x hx
            simp only [List.foldl_cons]
            apply ih_N (fun φ hφ => hN φ (by simp [hφ]))
            apply uf.inf_mem hx (hN m (by simp))
        apply h_fold_preserves M h_rest
        apply uf.inf_mem uf.top_mem h_ψ
    have h_all_in_uf : ∀ ψ ∈ L, toQuot ψ ∈ uf.carrier := hL
    have h_meet := h_meet_in_uf L h_all_in_uf
    have h_le_bot := fold_le_of_derives L Formula.bot d_bot
    have h_bot_eq : toQuot (Formula.bot : Formula Atom) = ⊥ := rfl
    rw [h_bot_eq] at h_le_bot
    have h_bot_in_uf : (⊥ : LindenbaumAlg Atom) ∈ uf.carrier := uf.mem_of_le h_meet h_le_bot
    exact uf.bot_not_mem h_bot_in_uf
  · intro φ hφ
    unfold ultrafilterToSet at hφ
    simp only [Set.mem_setOf_eq] at hφ
    have h_compl : (toQuot φ)ᶜ ∈ uf.carrier := by
      cases uf.compl_or (toQuot φ) with
      | inl h => exact absurd h hφ
      | inr h => exact h
    have h_neg_phi : toQuot φ.neg ∈ uf.carrier := h_compl
    have h_neg_in : φ.neg ∈ ultrafilterToSet uf := h_neg_phi
    intro h_cons
    have h_neg_in_insert : φ.neg ∈ insert φ (ultrafilterToSet uf) := Set.mem_insert_of_mem φ h_neg_in
    have h_phi_in_insert : φ ∈ insert φ (ultrafilterToSet uf) := Set.mem_insert φ (ultrafilterToSet uf)
    have h_L_cons : Consistent (fc := FrameClass.Base) [φ, φ.neg] := by
      apply h_cons [φ, φ.neg]
      intro ψ hψ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
      cases hψ with
      | inl h => rw [h]; exact h_phi_in_insert
      | inr h => rw [h]; exact h_neg_in_insert
    apply h_L_cons
    have h_phi : [φ, φ.neg] ⊢ᴮ φ := DerivationTree.assumption [φ, φ.neg] φ (by simp)
    have h_neg : [φ, φ.neg] ⊢ᴮ φ.neg := DerivationTree.assumption [φ, φ.neg] φ.neg (by simp)
    exact ⟨DerivationTree.modus_ponens [φ, φ.neg] φ Formula.bot h_neg h_phi⟩

/-!
## Bijection
-/

theorem SetMaximalConsistent.ultrafilter_correspondence :
    ∃ (f : {Γ : Set (Formula Atom) // SetMaximalConsistent FrameClass.Base Γ} → BoolAlgUltrafilter (LindenbaumAlg Atom))
      (g : BoolAlgUltrafilter (LindenbaumAlg Atom) → {Γ : Set (Formula Atom) // SetMaximalConsistent FrameClass.Base Γ}),
      Function.LeftInverse g f ∧ Function.RightInverse g f := by
  use mcsToUltrafilter
  use fun uf => ⟨ultrafilterToSet uf, ultrafilterToSet_mcs uf⟩
  constructor
  · intro Γ
    apply Subtype.ext
    ext φ
    simp only [ultrafilterToSet, Set.mem_setOf_eq]
    constructor
    · intro h_mem
      obtain ⟨ψ, h_psi_in, h_eq⟩ := h_mem
      have h_le : toQuot ψ ≤ toQuot φ := by rw [← h_eq]
      obtain ⟨d_imp⟩ := (h_le : Derives ψ φ)
      by_contra h_not
      have h_incons : ¬SetConsistent FrameClass.Base (insert φ Γ.val) := Γ.property.2 φ h_not
      unfold SetConsistent at h_incons
      push_neg at h_incons
      obtain ⟨L, hL, hL_incons⟩ := h_incons
      have ⟨d_bot⟩ := inconsistent_derives_bot hL_incons
      let Γ' := L.filter (· ≠ φ)
      have h_Γ'_sub : ∀ χ ∈ Γ', χ ∈ Γ.val := by
        intro χ hχ
        have hχ' := List.mem_filter.mp hχ
        have hχne : χ ≠ φ := by simpa using hχ'.2
        specialize hL χ hχ'.1
        simp [Set.mem_insert_iff] at hL
        rcases hL with rfl | h_in_Γ
        · exact absurd rfl hχne
        · exact h_in_Γ
      have h_L_sub : L ⊆ φ :: Γ' := by
        intro χ hχ
        by_cases hχeq : χ = φ
        · simp [hχeq]
        · simp only [List.mem_cons]; right
          exact List.mem_filter.mpr ⟨hχ, by simpa⟩
      have d_bot' := DerivationTree.weakening L (φ :: Γ') Formula.bot d_bot h_L_sub
      have d_neg := deduction_theorem Γ' φ Formula.bot d_bot'
      have d_neg' := DerivationTree.weakening Γ' (ψ :: Γ') φ.neg d_neg (fun x hx => List.mem_cons_of_mem ψ hx)
      have d_ψ : (ψ :: Γ') ⊢ᴮ ψ := DerivationTree.assumption (ψ :: Γ') ψ (by simp)
      have d_imp' : (ψ :: Γ') ⊢ᴮ ψ.imp φ := DerivationTree.weakening [] (ψ :: Γ') (ψ.imp φ) d_imp (by simp)
      have d_φ : (ψ :: Γ') ⊢ᴮ φ := DerivationTree.modus_ponens (ψ :: Γ') ψ φ d_imp' d_ψ
      have d_bot'' : (ψ :: Γ') ⊢ᴮ Formula.bot := DerivationTree.modus_ponens (ψ :: Γ') φ Formula.bot d_neg' d_φ
      have h_cons : Consistent (fc := FrameClass.Base) (ψ :: Γ') := by
        apply Γ.property.1 (ψ :: Γ')
        intro χ hχ
        simp at hχ
        rcases hχ with rfl | hχ'
        · exact h_psi_in
        · exact h_Γ'_sub χ hχ'
      exact h_cons ⟨d_bot''⟩
    · intro h_mem
      exact mem_mcsToSet h_mem
  · intro uf
    apply BoolAlgUltrafilter.ext
    simp only [mcsToUltrafilter]
    ext a
    constructor
    · intro ⟨φ, h_phi_in, h_eq⟩
      rw [h_eq]
      exact h_phi_in
    · intro h_mem
      induction a using Quotient.ind with
      | _ φ =>
        use φ
        exact ⟨h_mem, rfl⟩

/-!
## Helper Lemmas for Ultrafilter Properties
-/

theorem BoolAlgUltrafilter.compl_xor {α : Type*} [BooleanAlgebra α] (uf : BoolAlgUltrafilter α) (a : α) :
    (a ∈ uf.carrier ∧ aᶜ ∉ uf.carrier) ∨ (a ∉ uf.carrier ∧ aᶜ ∈ uf.carrier) := by
  cases uf.compl_or a with
  | inl h => exact Or.inl ⟨h, uf.compl_not a h⟩
  | inr h =>
    have h_not_a : a ∉ uf.carrier := fun ha => uf.compl_not a ha h
    exact Or.inr ⟨h_not_a, h⟩

theorem BoolAlgUltrafilter.mem_iff_compl_not_mem {α : Type*} [BooleanAlgebra α]
    (uf : BoolAlgUltrafilter α) (a : α) : a ∈ uf.carrier ↔ aᶜ ∉ uf.carrier := by
  constructor
  · exact uf.compl_not a
  · intro h
    cases uf.compl_or a with
    | inl ha => exact ha
    | inr hac => exact absurd hac h

theorem BoolAlgUltrafilter.not_mem_iff_compl_mem {α : Type*} [BooleanAlgebra α]
    (uf : BoolAlgUltrafilter α) (a : α) : a ∉ uf.carrier ↔ aᶜ ∈ uf.carrier := by
  constructor
  · intro h
    cases uf.compl_or a with
    | inl ha => exact absurd ha h
    | inr hac => exact hac
  · intro hac ha
    exact uf.compl_not a ha hac

theorem ultrafilter_neg_iff (uf : BoolAlgUltrafilter (LindenbaumAlg Atom)) (φ : Formula Atom) :
    toQuot φ ∈ uf.carrier ↔ toQuot φ.neg ∉ uf.carrier := by
  have h_compl : (toQuot φ)ᶜ = toQuot φ.neg := rfl
  rw [← h_compl]
  exact uf.mem_iff_compl_not_mem (toQuot φ)

theorem ultrafilter_neg_iff' (uf : BoolAlgUltrafilter (LindenbaumAlg Atom)) (φ : Formula Atom) :
    toQuot φ.neg ∈ uf.carrier ↔ toQuot φ ∉ uf.carrier := by
  have h_compl : (toQuot φ)ᶜ = toQuot φ.neg := rfl
  rw [← h_compl]
  exact uf.not_mem_iff_compl_mem (toQuot φ) |>.symm

noncomputable def ultrafilter_to_mcs (uf : BoolAlgUltrafilter (LindenbaumAlg Atom)) :
    {Γ : Set (Formula Atom) // SetMaximalConsistent FrameClass.Base Γ} :=
  ⟨ultrafilterToSet uf, ultrafilterToSet_mcs uf⟩

@[simp]
theorem ultrafilter_to_mcs_val (uf : BoolAlgUltrafilter (LindenbaumAlg Atom)) :
    (ultrafilter_to_mcs uf).val = ultrafilterToSet uf := rfl

theorem ultrafilter_mcs_round_trip (Γ : {Omega : Set (Formula Atom) // SetMaximalConsistent FrameClass.Base Omega}) :
    ultrafilter_to_mcs (mcsToUltrafilter Γ) = Γ := by
  apply Subtype.ext
  simp only [ultrafilter_to_mcs, ultrafilterToSet, mcsToUltrafilter]
  ext φ
  constructor
  · intro h_mem
    obtain ⟨ψ, h_psi_in, h_eq⟩ := h_mem
    have h_le : toQuot ψ ≤ toQuot φ := by rw [← h_eq]
    obtain ⟨d_imp⟩ := (h_le : Derives ψ φ)
    by_contra h_not
    have h_incons : ¬SetConsistent FrameClass.Base (insert φ Γ.val) := Γ.property.2 φ h_not
    unfold SetConsistent at h_incons
    push_neg at h_incons
    obtain ⟨L, hL, hL_incons⟩ := h_incons
    have ⟨d_bot⟩ := inconsistent_derives_bot hL_incons
    let Γ' := L.filter (· ≠ φ)
    have h_Γ'_sub : ∀ χ ∈ Γ', χ ∈ Γ.val := by
      intro χ hχ
      have hχ' := List.mem_filter.mp hχ
      have hχne : χ ≠ φ := by simpa using hχ'.2
      specialize hL χ hχ'.1
      simp [Set.mem_insert_iff] at hL
      rcases hL with rfl | h_in_Γ
      · exact absurd rfl hχne
      · exact h_in_Γ
    have h_L_sub : L ⊆ φ :: Γ' := by
      intro χ hχ
      by_cases hχeq : χ = φ
      · simp [hχeq]
      · simp only [List.mem_cons]; right
        exact List.mem_filter.mpr ⟨hχ, by simpa⟩
    have d_bot' := DerivationTree.weakening L (φ :: Γ') Formula.bot d_bot h_L_sub
    have d_neg := deduction_theorem Γ' φ Formula.bot d_bot'
    have d_neg' := DerivationTree.weakening Γ' (ψ :: Γ') φ.neg d_neg (fun x hx => List.mem_cons_of_mem ψ hx)
    have d_ψ : (ψ :: Γ') ⊢ᴮ ψ := DerivationTree.assumption (ψ :: Γ') ψ (by simp)
    have d_imp' : (ψ :: Γ') ⊢ᴮ ψ.imp φ := DerivationTree.weakening [] (ψ :: Γ') (ψ.imp φ) d_imp (by simp)
    have d_φ : (ψ :: Γ') ⊢ᴮ φ := DerivationTree.modus_ponens (ψ :: Γ') ψ φ d_imp' d_ψ
    have d_bot'' : (ψ :: Γ') ⊢ᴮ Formula.bot := DerivationTree.modus_ponens (ψ :: Γ') φ Formula.bot d_neg' d_φ
    have h_cons : Consistent (fc := FrameClass.Base) (ψ :: Γ') := by
      apply Γ.property.1 (ψ :: Γ')
      intro χ hχ
      simp at hχ
      rcases hχ with rfl | hχ'
      · exact h_psi_in
      · exact h_Γ'_sub χ hχ'
    exact h_cons ⟨d_bot''⟩
  · intro h_mem
    exact mem_mcsToSet h_mem

theorem mcs_ultrafilter_round_trip (uf : BoolAlgUltrafilter (LindenbaumAlg Atom)) :
    mcsToUltrafilter (ultrafilter_to_mcs uf) = uf := by
  apply BoolAlgUltrafilter.ext
  simp only [mcsToUltrafilter, ultrafilter_to_mcs, ultrafilterToSet]
  ext a
  constructor
  · intro ⟨φ, h_phi_in, h_eq⟩
    rw [h_eq]
    exact h_phi_in
  · intro h_mem
    induction a using Quotient.ind with
    | _ φ =>
      use φ
      exact ⟨h_mem, rfl⟩

end Cslib.Logic.Bimodal.Metalogic.Algebraic.UltrafilterMCS
