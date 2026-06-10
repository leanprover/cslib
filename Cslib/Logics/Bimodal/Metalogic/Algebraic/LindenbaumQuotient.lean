/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.ProofSystem.Derivation
public import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
public import Cslib.Logics.Bimodal.Theorems.Propositional.Connectives
public import Cslib.Logics.Bimodal.Theorems.Combinators
public import Cslib.Logics.Bimodal.Theorems.Perpetuity.Bridge
public import Cslib.Logics.Bimodal.Theorems.TemporalDerived

/-!
# Lindenbaum Quotient Construction

Quotient of formulas by provable equivalence forming the Lindenbaum-Tarski algebra.

Ported from BimodalLogic/Theories/Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean
(2 sorries: temp_k_dist in provEquiv_allFuture_congr -- now resolved using derived theorem)
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Algebraic.LindenbaumQuotient

open Cslib.Logic.Bimodal

variable {Atom : Type*}

def Derives (φ ψ : Formula Atom) : Prop := Nonempty (DerivationTree FrameClass.Base [] (φ.imp ψ))

def ProvEquiv (φ ψ : Formula Atom) : Prop := Derives φ ψ ∧ Derives ψ φ

scoped infix:50 " ≈ₚ " => ProvEquiv

theorem derives_refl (φ : Formula Atom) : Derives φ φ := by
  unfold Derives
  exact ⟨Theorems.Combinators.identity φ⟩

theorem provEquiv_refl (φ : Formula Atom) : φ ≈ₚ φ :=
  ⟨derives_refl φ, derives_refl φ⟩

theorem provEquiv_symm {φ ψ : Formula Atom} (h : φ ≈ₚ ψ) : ψ ≈ₚ φ :=
  ⟨h.2, h.1⟩

theorem derives_trans {φ ψ χ : Formula Atom} (h1 : Derives φ ψ) (h2 : Derives ψ χ) :
    Derives φ χ := by
  unfold Derives at *
  obtain ⟨d1⟩ := h1
  obtain ⟨d2⟩ := h2
  exact ⟨Theorems.Combinators.imp_trans d1 d2⟩

theorem provEquiv_trans {φ ψ χ : Formula Atom} (h1 : φ ≈ₚ ψ) (h2 : ψ ≈ₚ χ) : φ ≈ₚ χ :=
  ⟨derives_trans h1.1 h2.1, derives_trans h2.2 h1.2⟩

theorem provEquiv_equiv : Equivalence (ProvEquiv (Atom := Atom)) where
  refl := provEquiv_refl
  symm := provEquiv_symm
  trans := provEquiv_trans

instance provEquivSetoid : Setoid (Formula Atom) where
  r := ProvEquiv
  iseqv := provEquiv_equiv

def LindenbaumAlg (Atom : Type*) : Type _ := Quotient (provEquivSetoid (Atom := Atom))

def toQuot (φ : Formula Atom) : LindenbaumAlg Atom := Quotient.mk provEquivSetoid φ

scoped notation "⟦" φ "⟧" => toQuot φ

theorem derives_neg_antitone {φ ψ : Formula Atom} (h : Derives ψ φ) : Derives φ.neg ψ.neg := by
  unfold Derives at *
  obtain ⟨d⟩ := h
  exact ⟨Theorems.Propositional.contraposition d⟩

theorem provEquiv_neg_congr {φ ψ : Formula Atom} (h : φ ≈ₚ ψ) : φ.neg ≈ₚ ψ.neg := by
  unfold ProvEquiv at *
  exact ⟨derives_neg_antitone h.2, derives_neg_antitone h.1⟩

theorem provEquiv_box_congr {φ ψ : Formula Atom} (h : φ ≈ₚ ψ) : φ.box ≈ₚ ψ.box := by
  unfold ProvEquiv Derives at *
  obtain ⟨⟨d_fwd⟩, ⟨d_bwd⟩⟩ := h
  constructor
  · have d_box := DerivationTree.necessitation (φ.imp ψ) d_fwd
    have d_k := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.modal_k_dist φ ψ) trivial
    exact ⟨DerivationTree.modus_ponens [] _ _ d_k d_box⟩
  · have d_box := DerivationTree.necessitation (ψ.imp φ) d_bwd
    have d_k := DerivationTree.axiom (fc := FrameClass.Base) [] _ (Axiom.modal_k_dist ψ φ) trivial
    exact ⟨DerivationTree.modus_ponens [] _ _ d_k d_box⟩

theorem provEquiv_allFuture_congr {φ ψ : Formula Atom} (h : φ ≈ₚ ψ) :
    φ.allFuture ≈ₚ ψ.allFuture := by
  unfold ProvEquiv Derives at *
  obtain ⟨⟨d_fwd⟩, ⟨d_bwd⟩⟩ := h
  constructor
  · have d_temp := DerivationTree.temporal_necessitation (φ.imp ψ) d_fwd
    have d_k := Theorems.TemporalDerived.temp_k_dist_derived φ ψ
    exact ⟨DerivationTree.modus_ponens [] _ _ d_k d_temp⟩
  · have d_temp := DerivationTree.temporal_necessitation (ψ.imp φ) d_bwd
    have d_k := Theorems.TemporalDerived.temp_k_dist_derived ψ φ
    exact ⟨DerivationTree.modus_ponens [] _ _ d_k d_temp⟩

theorem provEquiv_allPast_congr {φ ψ : Formula Atom} (h : φ ≈ₚ ψ) :
    φ.allPast ≈ₚ ψ.allPast := by
  unfold ProvEquiv Derives at *
  obtain ⟨⟨d_fwd⟩, ⟨d_bwd⟩⟩ := h
  constructor
  · exact ⟨Theorems.Perpetuity.past_mono d_fwd⟩
  · exact ⟨Theorems.Perpetuity.past_mono d_bwd⟩

theorem provEquiv_imp_congr {φ₁ φ₂ ψ₁ ψ₂ : Formula Atom}
    (hφ : φ₁ ≈ₚ φ₂) (hψ : ψ₁ ≈ₚ ψ₂) : φ₁.imp ψ₁ ≈ₚ φ₂.imp ψ₂ := by
  unfold ProvEquiv Derives at *
  obtain ⟨⟨d_φ_fwd⟩, ⟨d_φ_bwd⟩⟩ := hφ
  obtain ⟨⟨d_ψ_fwd⟩, ⟨d_ψ_bwd⟩⟩ := hψ
  constructor
  · have b1 : DerivationTree FrameClass.Base [] ((ψ₁.imp ψ₂).imp ((φ₂.imp ψ₁).imp (φ₂.imp ψ₂))) :=
      Theorems.Combinators.b_combinator
    have h1 := DerivationTree.modus_ponens [] _ _ b1 d_ψ_fwd
    have b2_pre : DerivationTree FrameClass.Base [] ((φ₁.imp ψ₁).imp ((φ₂.imp φ₁).imp (φ₂.imp ψ₁))) :=
      Theorems.Combinators.b_combinator
    have flip2 : DerivationTree FrameClass.Base []
        (((φ₁.imp ψ₁).imp ((φ₂.imp φ₁).imp (φ₂.imp ψ₁))).imp
         ((φ₂.imp φ₁).imp ((φ₁.imp ψ₁).imp (φ₂.imp ψ₁)))) :=
      Theorems.Combinators.theorem_flip
    have b2 := DerivationTree.modus_ponens [] _ _ flip2 b2_pre
    have h2 := DerivationTree.modus_ponens [] _ _ b2 d_φ_bwd
    exact ⟨Theorems.Combinators.imp_trans h2 h1⟩
  · have b1 : DerivationTree FrameClass.Base [] ((ψ₂.imp ψ₁).imp ((φ₁.imp ψ₂).imp (φ₁.imp ψ₁))) :=
      Theorems.Combinators.b_combinator
    have h1 := DerivationTree.modus_ponens [] _ _ b1 d_ψ_bwd
    have b2_pre : DerivationTree FrameClass.Base [] ((φ₂.imp ψ₂).imp ((φ₁.imp φ₂).imp (φ₁.imp ψ₂))) :=
      Theorems.Combinators.b_combinator
    have flip2 : DerivationTree FrameClass.Base []
        (((φ₂.imp ψ₂).imp ((φ₁.imp φ₂).imp (φ₁.imp ψ₂))).imp
         ((φ₁.imp φ₂).imp ((φ₂.imp ψ₂).imp (φ₁.imp ψ₂)))) :=
      Theorems.Combinators.theorem_flip
    have b2 := DerivationTree.modus_ponens [] _ _ flip2 b2_pre
    have h2 := DerivationTree.modus_ponens [] _ _ b2 d_φ_fwd
    exact ⟨Theorems.Combinators.imp_trans h2 h1⟩

theorem provEquiv_and_congr {φ₁ φ₂ ψ₁ ψ₂ : Formula Atom}
    (hφ : φ₁ ≈ₚ φ₂) (hψ : ψ₁ ≈ₚ ψ₂) : φ₁.and ψ₁ ≈ₚ φ₂.and ψ₂ := by
  have hψ_neg := provEquiv_neg_congr hψ
  have h_imp := provEquiv_imp_congr hφ hψ_neg
  exact provEquiv_neg_congr h_imp

theorem provEquiv_or_congr {φ₁ φ₂ ψ₁ ψ₂ : Formula Atom}
    (hφ : φ₁ ≈ₚ φ₂) (hψ : ψ₁ ≈ₚ ψ₂) : φ₁.or ψ₁ ≈ₚ φ₂.or ψ₂ := by
  have hφ_neg := provEquiv_neg_congr hφ
  exact provEquiv_imp_congr hφ_neg hψ

noncomputable def neg_quot : LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift (fun φ => toQuot φ.neg)
    (fun _ _ h => Quotient.sound (provEquiv_neg_congr h))

noncomputable def imp_quot : LindenbaumAlg Atom → LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift₂ (fun φ ψ => toQuot (φ.imp ψ))
    (fun _ _ _ _ h1 h2 => Quotient.sound (provEquiv_imp_congr h1 h2))

noncomputable def and_quot : LindenbaumAlg Atom → LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift₂ (fun φ ψ => toQuot (φ.and ψ))
    (fun _ _ _ _ h1 h2 => Quotient.sound (provEquiv_and_congr h1 h2))

noncomputable def or_quot : LindenbaumAlg Atom → LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift₂ (fun φ ψ => toQuot (φ.or ψ))
    (fun _ _ _ _ h1 h2 => Quotient.sound (provEquiv_or_congr h1 h2))

noncomputable def box_quot : LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift (fun φ => toQuot φ.box)
    (fun _ _ h => Quotient.sound (provEquiv_box_congr h))

noncomputable def G_quot : LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift (fun φ => toQuot φ.allFuture)
    (fun _ _ h => Quotient.sound (provEquiv_allFuture_congr h))

noncomputable def H_quot : LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift (fun φ => toQuot φ.allPast)
    (fun _ _ h => Quotient.sound (provEquiv_allPast_congr h))

def top_quot : LindenbaumAlg Atom := toQuot (Formula.bot.imp Formula.bot)
def bot_quot : LindenbaumAlg Atom := toQuot Formula.bot

theorem swapTemporal_derives {φ ψ : Formula Atom} (h : Derives φ ψ) :
    Derives φ.swapTemporal ψ.swapTemporal := by
  unfold Derives at *
  obtain ⟨d⟩ := h
  have d_swap := DerivationTree.temporal_duality (φ.imp ψ) d
  simp only [Formula.swapTemporal] at d_swap
  exact ⟨d_swap⟩

theorem provEquiv_swapTemporal_congr {φ ψ : Formula Atom} (h : φ ≈ₚ ψ) :
    φ.swapTemporal ≈ₚ ψ.swapTemporal :=
  ⟨swapTemporal_derives h.1, swapTemporal_derives h.2⟩

noncomputable def sigma_quot : LindenbaumAlg Atom → LindenbaumAlg Atom :=
  Quotient.lift (fun φ => toQuot φ.swapTemporal)
    (fun _ _ h => Quotient.sound (provEquiv_swapTemporal_congr h))

theorem sigma_quot_involution (a : LindenbaumAlg Atom) : sigma_quot (sigma_quot a) = a := by
  induction a using Quotient.ind
  rename_i φ
  show toQuot (φ.swapTemporal.swapTemporal) = toQuot φ
  rw [Formula.swapTemporal_involution]

theorem sigma_quot_neg (a : LindenbaumAlg Atom) :
    sigma_quot (neg_quot a) = neg_quot (sigma_quot a) := by
  induction a using Quotient.ind
  rename_i φ
  show toQuot (φ.neg.swapTemporal) = neg_quot (toQuot (φ.swapTemporal))
  simp only [Formula.neg, Formula.swapTemporal]
  rfl

theorem sigma_quot_sup (a b : LindenbaumAlg Atom) :
    sigma_quot (or_quot a b) = or_quot (sigma_quot a) (sigma_quot b) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i φ ψ
  show toQuot ((φ.or ψ).swapTemporal) = or_quot (toQuot φ.swapTemporal) (toQuot ψ.swapTemporal)
  simp only [Formula.or, Formula.neg, Formula.swapTemporal]
  rfl

theorem sigma_quot_G_H (a : LindenbaumAlg Atom) :
    sigma_quot (G_quot a) = H_quot (sigma_quot a) := by
  induction a using Quotient.ind
  rename_i φ
  show toQuot (φ.allFuture.swapTemporal) = H_quot (toQuot φ.swapTemporal)
  simp only [Formula.swapTemporal_allFuture]
  rfl

theorem sigma_quot_H_G (a : LindenbaumAlg Atom) :
    sigma_quot (H_quot a) = G_quot (sigma_quot a) := by
  induction a using Quotient.ind
  rename_i φ
  show toQuot (φ.allPast.swapTemporal) = G_quot (toQuot φ.swapTemporal)
  simp only [Formula.swapTemporal_allPast]
  rfl

theorem sigma_quot_box (a : LindenbaumAlg Atom) :
    sigma_quot (box_quot a) = box_quot (sigma_quot a) := by
  induction a using Quotient.ind
  rename_i φ
  show toQuot (φ.box.swapTemporal) = box_quot (toQuot φ.swapTemporal)
  simp only [Formula.swapTemporal]
  rfl

end Cslib.Logic.Bimodal.Metalogic.Algebraic.LindenbaumQuotient
