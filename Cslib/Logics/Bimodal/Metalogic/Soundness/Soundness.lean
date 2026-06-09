/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
import Cslib.Logics.Bimodal.ProofSystem.Derivation
import Cslib.Logics.Bimodal.Semantics.Validity
import Cslib.Logics.Bimodal.Metalogic.Soundness.FrameClassVariants

/-!
# Soundness Theorem for TM Logic

Main soundness theorems for bimodal logic TM:
- Individual axiom validity lemmas
- Combined axiom validators (`axiom_valid`, `axiom_dense_valid`, `axiom_discrete_valid`)
- Full derivation soundness (`soundness`, `soundness_dense`, `soundness_discrete`)
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Classical Logic Helper -/

/-- Helper lemma for extracting conjunction from negated implication encoding. -/
private theorem and_of_not_imp_not {p q : Prop} (h : (p → q → False) → False) : p ∧ q :=
  ⟨Classical.byContradiction (fun hp => h (fun a _ => hp a)),
   Classical.byContradiction (fun hq => h (fun _ b => hq b))⟩

/-! ## Individual Axiom Validity Theorems -/

theorem prop_k_valid (φ ψ χ : Formula Atom) :
    ⊨ ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h1 h2 h_phi; exact h1 h_phi (h2 h_phi)

theorem prop_s_valid (φ ψ : Formula Atom) : ⊨ (φ.imp (ψ.imp φ)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_phi _; exact h_phi

theorem modal_t_valid (φ : Formula Atom) : ⊨ (φ.box.imp φ) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ h_mem t
  simp only [truth_at]
  intro h_box; exact h_box τ h_mem

theorem modal_4_valid (φ : Formula Atom) : ⊨ ((φ.box).imp (φ.box.box)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_box σ _h_σ_mem ρ h_ρ_mem; exact h_box ρ h_ρ_mem

theorem modal_b_valid (φ : Formula Atom) : ⊨ (φ.imp (φ.diamond.box)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ h_mem t
  simp only [Formula.diamond, Formula.neg, truth_at]
  intro h_phi σ _h_σ_mem h_box_neg; exact h_box_neg τ h_mem h_phi

theorem modal_5_collapse_valid (φ : Formula Atom) : ⊨ (φ.box.diamond.imp φ.box) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.diamond, Formula.neg, truth_at]
  intro h_diamond_box ρ h_ρ_mem
  by_contra h_not; apply h_diamond_box
  intro σ h_σ_mem h_box; exact h_not (h_box ρ h_ρ_mem)

theorem ex_falso_valid (φ : Formula Atom) : ⊨ (Formula.bot.imp φ) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_bot; exfalso; exact h_bot

theorem peirce_valid (φ ψ : Formula Atom) : ⊨ (((φ.imp ψ).imp φ).imp φ) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_peirce
  by_cases h : truth_at M Omega τ t φ
  · exact h
  · exact h_peirce (fun h_phi => absurd h_phi h)

theorem modal_k_dist_valid (φ ψ : Formula Atom) :
    ⊨ ((φ.imp ψ).box.imp (φ.box.imp ψ.box)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_box_imp h_box_phi σ h_σ_mem
  exact h_box_imp σ h_σ_mem (h_box_phi σ h_σ_mem)

theorem serial_future_axiom_valid :
    ⊨ ((Formula.bot.imp (Formula.bot : Formula Atom)).imp (Formula.some_future (Formula.bot.imp Formula.bot))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro _; obtain ⟨s, hts⟩ := exists_gt t
  exact ⟨s, hts, fun h => h, fun _ _ _ hf => absurd hf not_false⟩

theorem serial_past_axiom_valid :
    ⊨ ((Formula.bot.imp (Formula.bot : Formula Atom)).imp (Formula.some_past (Formula.bot.imp Formula.bot))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro _; obtain ⟨s, hst⟩ := exists_lt t
  exact ⟨s, hst, fun h => h, fun _ _ _ hf => absurd hf not_false⟩

theorem temp_4_valid (φ : Formula Atom) : ⊨ ((φ.all_future).imp (φ.all_future.all_future)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_Gφ ⟨s, hts, h_neg_Gφs, _⟩
  apply h_neg_Gφs; intro ⟨r, hsr, h_neg_φr, _⟩
  apply h_Gφ; exact ⟨r, lt_trans hts hsr, h_neg_φr, fun _ _ _ hf => absurd hf not_false⟩

theorem temp_a_valid (φ : Formula Atom) : ⊨ (φ.imp (Formula.all_future φ.some_past)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_phi ⟨s, hts, h_neg, _⟩
  apply h_neg; exact ⟨t, hts, h_phi, fun _ _ _ hf => absurd hf not_false⟩

theorem temp_a_dual_valid (φ : Formula Atom) : ⊨ (φ.imp (Formula.all_past φ.some_future)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_phi ⟨s, hst, h_neg, _⟩
  apply h_neg; exact ⟨t, hst, h_phi, fun _ _ _ hf => absurd hf not_false⟩

theorem temp_l_valid (φ : Formula Atom) :
    ⊨ (φ.always.imp (Formula.all_future (Formula.all_past φ))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  -- Always encodes: Hφ ∧ φ ∧ Gφ (conjunction via double negation)
  -- h_always encodes △φ = Hφ ∧ φ ∧ Gφ (conjunction via double negation)
  intro h_always ⟨s, _hts, h_neg_Hφs, _⟩
  apply h_neg_Hφs; intro ⟨r, hrs, h_neg_φr, _⟩
  -- Extract Hφ, (φ ∧ Gφ) from h_always
  have h1 := and_of_not_imp_not h_always
  obtain ⟨h_past, h_middle⟩ := h1
  have h2 := and_of_not_imp_not h_middle
  obtain ⟨h_now, h_future⟩ := h2
  -- h_past : ¬∃ s < t, ¬φ(s) ∧ guard (i.e., Hφ)
  -- h_now : truth_at ... t φ
  -- h_future : ¬∃ s > t, ¬φ(s) ∧ guard (i.e., Gφ)
  rcases lt_trichotomy r t with h_lt | h_eq | h_gt
  · exact h_neg_φr (by by_contra h_neg; apply h_past; exact ⟨r, h_lt, h_neg, fun _ _ _ hf => absurd hf not_false⟩)
  · exact h_neg_φr (h_eq ▸ h_now)
  · exact h_neg_φr (by by_contra h_neg; apply h_future; exact ⟨r, h_gt, h_neg, fun _ _ _ hf => absurd hf not_false⟩)

theorem modal_future_valid (φ : Formula Atom) : ⊨ ((φ.box).imp ((φ.all_future).box)) := by
  intro D _ _ _ _ ℱ M Omega h_sc τ _h_mem t
  simp only [truth_at]
  intro h_box σ h_σ_mem ⟨s, hts, h_neg_φs, _⟩
  have h_phi := h_box (WorldHistory.time_shift σ (s - t)) (h_sc σ h_σ_mem (s - t))
  exact h_neg_φs ((TimeShift.time_shift_preserves_truth M Omega h_sc σ t s φ).mp h_phi)

theorem left_mono_until_G_valid (φ χ ψ : Formula Atom) :
    ⊨ ((φ.imp χ).all_future.imp ((Formula.untl ψ φ).imp (Formula.untl ψ χ))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_G ⟨s, hts, h_event, h_guard⟩
  refine ⟨s, hts, h_event, fun r htr hrs => ?_⟩
  by_contra h_neg; apply h_G
  exact ⟨r, htr, fun h_imp => h_neg (h_imp (h_guard r htr hrs)),
    fun _ _ _ hf => absurd hf not_false⟩

theorem left_mono_since_H_valid (φ χ ψ : Formula Atom) :
    ⊨ ((φ.imp χ).all_past.imp ((Formula.snce ψ φ).imp (Formula.snce ψ χ))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_H ⟨s, hst, h_event, h_guard⟩
  refine ⟨s, hst, h_event, fun r hsr hrt => ?_⟩
  by_contra h_neg; apply h_H
  exact ⟨r, hrt, fun h_imp => h_neg (h_imp (h_guard r hsr hrt)),
    fun _ _ _ hf => absurd hf not_false⟩

theorem right_mono_until_valid (φ ψ χ : Formula Atom) :
    ⊨ ((φ.imp ψ).all_future.imp ((Formula.untl φ χ).imp (Formula.untl ψ χ))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_G ⟨s, hts, h_φs, h_guard⟩
  have h_ψs : truth_at M Omega τ s ψ := by
    by_contra h_neg; apply h_G
    exact ⟨s, hts, fun h_imp => h_neg (h_imp h_φs),
      fun _ _ _ hf => absurd hf not_false⟩
  exact ⟨s, hts, h_ψs, h_guard⟩

theorem right_mono_since_valid (φ ψ χ : Formula Atom) :
    ⊨ ((φ.imp ψ).all_past.imp ((Formula.snce φ χ).imp (Formula.snce ψ χ))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_H ⟨s, hst, h_φs, h_guard⟩
  have h_ψs : truth_at M Omega τ s ψ := by
    by_contra h_neg; apply h_H
    exact ⟨s, hst, fun h_imp => h_neg (h_imp h_φs),
      fun _ _ _ hf => absurd hf not_false⟩
  exact ⟨s, hst, h_ψs, h_guard⟩

theorem connect_future_valid (φ : Formula Atom) : ⊨ (φ.imp (φ.some_past.all_future)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_φt ⟨s, hts, h_neg, _⟩
  apply h_neg; exact ⟨t, hts, h_φt, fun _ _ _ hf => absurd hf not_false⟩

theorem connect_past_valid (φ : Formula Atom) : ⊨ (φ.imp (φ.some_future.all_past)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_φt ⟨s, hst, h_neg, _⟩
  apply h_neg; exact ⟨t, hst, h_φt, fun _ _ _ hf => absurd hf not_false⟩

theorem enrichment_until_valid (φ ψ p : Formula Atom) :
    ⊨ (Formula.and p (Formula.untl ψ φ) |>.imp
      (Formula.untl (Formula.and ψ (Formula.snce p φ)) φ)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.and, Formula.neg, truth_at]
  intro h_conj
  have h_pt : truth_at M Omega τ t p := by
    by_contra h_neg; exact h_conj (fun h_p _ => h_neg h_p)
  have h_until : ∃ s, t < s ∧ truth_at M Omega τ s ψ ∧
      ∀ r, t < r → r < s → truth_at M Omega τ r φ := by
    by_contra h_neg; exact h_conj (fun _ h_u => h_neg h_u)
  obtain ⟨s, hts, h_ψs, h_guard⟩ := h_until
  refine ⟨s, hts, ?_, h_guard⟩
  intro h_imp; exact h_imp h_ψs ⟨t, hts, h_pt, fun r htr hrs => h_guard r htr hrs⟩

theorem enrichment_since_valid (φ ψ p : Formula Atom) :
    ⊨ (Formula.and p (Formula.snce ψ φ) |>.imp
      (Formula.snce (Formula.and ψ (Formula.untl p φ)) φ)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.and, Formula.neg, truth_at]
  intro h_conj
  have h_pt : truth_at M Omega τ t p := by
    by_contra h_neg; exact h_conj (fun h_p _ => h_neg h_p)
  have h_since : ∃ s, s < t ∧ truth_at M Omega τ s ψ ∧
      ∀ r, s < r → r < t → truth_at M Omega τ r φ := by
    by_contra h_neg; exact h_conj (fun _ h_s => h_neg h_s)
  obtain ⟨s, hst, h_ψs, h_guard⟩ := h_since
  refine ⟨s, hst, ?_, h_guard⟩
  intro h_imp; exact h_imp h_ψs ⟨t, hst, h_pt, fun r hsr hrt => h_guard r hsr hrt⟩

theorem self_accum_until_valid (φ ψ : Formula Atom) :
    ⊨ ((Formula.untl ψ φ).imp (Formula.untl ψ (Formula.and φ (Formula.untl ψ φ)))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.and, Formula.neg, truth_at]
  intro ⟨s, hts, h_ψs, h_guard⟩
  refine ⟨s, hts, h_ψs, fun r htr hrs h_imp => ?_⟩
  exact h_imp (h_guard r htr hrs) ⟨s, hrs, h_ψs, fun q hqr hqs => h_guard q (lt_trans htr hqr) hqs⟩

theorem self_accum_since_valid (φ ψ : Formula Atom) :
    ⊨ ((Formula.snce ψ φ).imp (Formula.snce ψ (Formula.and φ (Formula.snce ψ φ)))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.and, Formula.neg, truth_at]
  intro ⟨s, hst, h_ψs, h_guard⟩
  refine ⟨s, hst, h_ψs, fun r hsr hrt h_imp => ?_⟩
  exact h_imp (h_guard r hsr hrt) ⟨s, hsr, h_ψs, fun q hsq hqr => h_guard q hsq (lt_trans hqr hrt)⟩

theorem absorb_until_valid (φ ψ : Formula Atom) :
    ⊨ ((Formula.untl (Formula.and φ (Formula.untl ψ φ)) φ).imp (Formula.untl ψ φ)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.and, Formula.neg, truth_at]
  intro ⟨s₁, hts₁, h_conj, h_guard₁⟩
  have ⟨h_φs₁, s₂, hs₁s₂, h_ψs₂, h_guard₂⟩ :
      truth_at M Omega τ s₁ φ ∧ (∃ s₂, s₁ < s₂ ∧ truth_at M Omega τ s₂ ψ ∧
        ∀ q, s₁ < q → q < s₂ → truth_at M Omega τ q φ) := by
    exact ⟨by by_contra h; exact h_conj (fun a _ => h a),
           by by_contra h; exact h_conj (fun _ b => h b)⟩
  refine ⟨s₂, lt_trans hts₁ hs₁s₂, h_ψs₂, fun q htq hqs₂ => ?_⟩
  rcases lt_trichotomy q s₁ with h_lt | h_eq | h_gt
  · exact h_guard₁ q htq h_lt
  · exact h_eq ▸ h_φs₁
  · exact h_guard₂ q h_gt hqs₂

theorem absorb_since_valid (φ ψ : Formula Atom) :
    ⊨ ((Formula.snce (Formula.and φ (Formula.snce ψ φ)) φ).imp (Formula.snce ψ φ)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.and, Formula.neg, truth_at]
  intro ⟨s₁, hs₁t, h_conj, h_guard₁⟩
  have ⟨h_φs₁, s₂, hs₂s₁, h_ψs₂, h_guard₂⟩ :
      truth_at M Omega τ s₁ φ ∧ (∃ s₂, s₂ < s₁ ∧ truth_at M Omega τ s₂ ψ ∧
        ∀ q, s₂ < q → q < s₁ → truth_at M Omega τ q φ) := by
    exact ⟨by by_contra h; exact h_conj (fun a _ => h a),
           by by_contra h; exact h_conj (fun _ b => h b)⟩
  refine ⟨s₂, lt_trans hs₂s₁ hs₁t, h_ψs₂, fun q hs₂q hqt => ?_⟩
  rcases lt_trichotomy q s₁ with h_lt | h_eq | h_gt
  · exact h_guard₂ q hs₂q h_lt
  · exact h_eq ▸ h_φs₁
  · exact h_guard₁ q h_gt hqt

theorem linear_until_valid (φ ψ χ θ : Formula Atom) :
    ⊨ (Formula.and (Formula.untl ψ φ) (Formula.untl θ χ) |>.imp
      (Formula.or (Formula.or (Formula.untl (Formula.and ψ θ) (Formula.and φ χ))
          (Formula.untl (Formula.and ψ χ) (Formula.and φ χ)))
        (Formula.untl (Formula.and φ θ) (Formula.and φ χ)))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.and, Formula.or, Formula.neg, truth_at]
  intro h_conj
  have h_both : (∃ s, t < s ∧ truth_at M Omega τ s ψ ∧
      ∀ r, t < r → r < s → truth_at M Omega τ r φ) ∧
    (∃ s, t < s ∧ truth_at M Omega τ s θ ∧
      ∀ r, t < r → r < s → truth_at M Omega τ r χ) := by
    constructor
    · by_contra h; exact h_conj (fun h1 _ => h h1)
    · by_contra h; exact h_conj (fun _ h2 => h h2)
  obtain ⟨⟨s₁, hts₁, h_ψs₁, h_guard₁⟩, s₂, hts₂, h_θs₂, h_guard₂⟩ := h_both
  rcases lt_trichotomy s₁ s₂ with h_lt | h_eq | h_gt
  · intro h_neg; exfalso; apply h_neg; intro _
    refine ⟨s₁, hts₁, ?_, fun r htr hrs h_imp => ?_⟩
    · intro h_neg; exact h_neg h_ψs₁ (h_guard₂ s₁ hts₁ h_lt)
    · exact h_imp (h_guard₁ r htr hrs) (h_guard₂ r htr (lt_trans hrs h_lt))
  · intro h_outer; exfalso; apply h_outer; intro h_inner; exfalso; apply h_inner
    refine ⟨s₁, hts₁, ?_, fun r htr hrs h_imp => ?_⟩
    · intro h_neg; exact h_neg h_ψs₁ (h_eq ▸ h_θs₂)
    · exact h_imp (h_guard₁ r htr hrs) (h_guard₂ r htr (h_eq ▸ hrs))
  · intro _
    refine ⟨s₂, hts₂, ?_, fun r htr hrs h_imp => ?_⟩
    · intro h_neg; exact h_neg (h_guard₁ s₂ hts₂ h_gt) h_θs₂
    · exact h_imp (h_guard₁ r htr (lt_trans hrs h_gt)) (h_guard₂ r htr hrs)

theorem linear_since_valid (φ ψ χ θ : Formula Atom) :
    ⊨ (Formula.and (Formula.snce ψ φ) (Formula.snce θ χ) |>.imp
      (Formula.or (Formula.or (Formula.snce (Formula.and ψ θ) (Formula.and φ χ))
          (Formula.snce (Formula.and ψ χ) (Formula.and φ χ)))
        (Formula.snce (Formula.and φ θ) (Formula.and φ χ)))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.and, Formula.or, Formula.neg, truth_at]
  intro h_conj
  have h_both : (∃ s, s < t ∧ truth_at M Omega τ s ψ ∧
      ∀ r, s < r → r < t → truth_at M Omega τ r φ) ∧
    (∃ s, s < t ∧ truth_at M Omega τ s θ ∧
      ∀ r, s < r → r < t → truth_at M Omega τ r χ) := by
    constructor
    · by_contra h; exact h_conj (fun h1 _ => h h1)
    · by_contra h; exact h_conj (fun _ h2 => h h2)
  obtain ⟨⟨s₁, hs₁t, h_ψs₁, h_guard₁⟩, s₂, hs₂t, h_θs₂, h_guard₂⟩ := h_both
  rcases lt_trichotomy s₁ s₂ with h_lt | h_eq | h_gt
  · intro _
    refine ⟨s₂, hs₂t, ?_, fun r hs₂r hrt h_imp => ?_⟩
    · intro h_neg; exact h_neg (h_guard₁ s₂ h_lt hs₂t) h_θs₂
    · exact h_imp (h_guard₁ r (lt_trans h_lt hs₂r) hrt) (h_guard₂ r hs₂r hrt)
  · intro h_outer; exfalso; apply h_outer; intro h_inner; exfalso; apply h_inner
    refine ⟨s₁, hs₁t, ?_, fun r hs₁r hrt h_imp => ?_⟩
    · intro h_neg; exact h_neg h_ψs₁ (h_eq ▸ h_θs₂)
    · exact h_imp (h_guard₁ r hs₁r hrt) (h_guard₂ r (h_eq ▸ hs₁r) hrt)
  · intro h_neg; exfalso; apply h_neg; intro _
    refine ⟨s₁, hs₁t, ?_, fun r hs₁r hrt h_imp => ?_⟩
    · intro h_neg; exact h_neg h_ψs₁ (h_guard₂ s₁ h_gt hs₁t)
    · exact h_imp (h_guard₁ r hs₁r hrt) (h_guard₂ r (lt_trans h_gt hs₁r) hrt)

theorem until_F_valid (φ ψ : Formula Atom) :
    ⊨ ((Formula.untl ψ φ).imp (Formula.some_future ψ)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro ⟨s, hts, h_ψs, _⟩
  exact ⟨s, hts, h_ψs, fun _ _ _ hf => absurd hf not_false⟩

theorem since_P_valid (φ ψ : Formula Atom) :
    ⊨ ((Formula.snce ψ φ).imp (Formula.some_past ψ)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro ⟨s, hst, h_ψs, _⟩
  exact ⟨s, hst, h_ψs, fun _ _ _ hf => absurd hf not_false⟩

theorem temp_linearity_valid (φ ψ : Formula Atom) :
    ⊨ (Formula.and (Formula.some_future φ) (Formula.some_future ψ) |>.imp
      (Formula.or (Formula.some_future (Formula.and φ ψ))
        (Formula.or (Formula.some_future (Formula.and φ (Formula.some_future ψ)))
          (Formula.some_future (Formula.and (Formula.some_future φ) ψ))))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.and, Formula.or, Formula.neg, truth_at]
  intro h_conj
  have h_F_phi : ∃ s, t < s ∧ truth_at M Omega τ s φ ∧ ∀ r, t < r → r < s → False → False := by
    by_contra h; exact h_conj (fun h1 _ => h h1)
  have h_F_psi : ∃ s, t < s ∧ truth_at M Omega τ s ψ ∧ ∀ r, t < r → r < s → False → False := by
    by_contra h; exact h_conj (fun _ h2 => h h2)
  obtain ⟨s1, hs1t, h_phi_s1, _⟩ := h_F_phi
  obtain ⟨s2, hs2t, h_psi_s2, _⟩ := h_F_psi
  rcases lt_trichotomy s1 s2 with h_lt | h_eq | h_gt
  · intro _; intro h_neg; exfalso
    exact h_neg ⟨s1, hs1t, fun h_imp => h_imp h_phi_s1
      ⟨s2, h_lt, h_psi_s2, fun _ _ _ hf => absurd hf not_false⟩,
      fun _ _ _ hf => absurd hf not_false⟩
  · subst h_eq; intro h_neg; exfalso
    exact h_neg ⟨s1, hs1t, fun h_imp => h_imp h_phi_s1 h_psi_s2,
      fun _ _ _ hf => absurd hf not_false⟩
  · intro _; intro _
    exact ⟨s2, hs2t, fun h_imp => h_imp
      ⟨s1, h_gt, h_phi_s1, fun _ _ _ hf => absurd hf not_false⟩ h_psi_s2,
      fun _ _ _ hf => absurd hf not_false⟩

theorem temp_linearity_past_valid (φ ψ : Formula Atom) :
    ⊨ (Formula.and (Formula.some_past φ) (Formula.some_past ψ) |>.imp
      (Formula.or (Formula.some_past (Formula.and φ ψ))
        (Formula.or (Formula.some_past (Formula.and φ (Formula.some_past ψ)))
          (Formula.some_past (Formula.and (Formula.some_past φ) ψ))))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.and, Formula.or, Formula.neg, truth_at]
  intro h_conj
  have h_P_phi : ∃ s, s < t ∧ truth_at M Omega τ s φ ∧ ∀ r, s < r → r < t → False → False := by
    by_contra h; exact h_conj (fun h1 _ => h h1)
  have h_P_psi : ∃ s, s < t ∧ truth_at M Omega τ s ψ ∧ ∀ r, s < r → r < t → False → False := by
    by_contra h; exact h_conj (fun _ h2 => h h2)
  obtain ⟨s1, hs1t, h_phi_s1, _⟩ := h_P_phi
  obtain ⟨s2, hs2t, h_psi_s2, _⟩ := h_P_psi
  rcases lt_trichotomy s1 s2 with h_lt | h_eq | h_gt
  · intro _; intro _
    exact ⟨s2, hs2t, fun h_imp => h_imp
      ⟨s1, h_lt, h_phi_s1, fun _ _ _ hf => absurd hf not_false⟩ h_psi_s2,
      fun _ _ _ hf => absurd hf not_false⟩
  · subst h_eq; intro h_neg; exfalso
    exact h_neg ⟨s1, hs1t, fun h_imp => h_imp h_phi_s1 h_psi_s2,
      fun _ _ _ hf => absurd hf not_false⟩
  · intro _; intro h_neg; exfalso
    exact h_neg ⟨s1, hs1t, fun h_imp => h_imp h_phi_s1
      ⟨s2, h_gt, h_psi_s2, fun _ _ _ hf => absurd hf not_false⟩,
      fun _ _ _ hf => absurd hf not_false⟩

theorem F_until_equiv_valid (φ : Formula Atom) :
    ⊨ ((Formula.some_future φ).imp (Formula.untl φ (Formula.bot.imp Formula.bot))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro ⟨s, hts, h_φs, _⟩; exact ⟨s, hts, h_φs, fun _ _ _ => id⟩

theorem P_since_equiv_valid (φ : Formula Atom) :
    ⊨ ((Formula.some_past φ).imp (Formula.snce φ (Formula.bot.imp Formula.bot))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro ⟨s, hst, h_φs, _⟩; exact ⟨s, hst, h_φs, fun _ _ _ => id⟩

/-! ## Frame-Class-Specific Axiom Validity -/

theorem dense_indicator_valid :
    valid_dense (Formula.untl (Formula.bot.imp (Formula.bot : Formula Atom)) Formula.bot).neg := by
  intro D _ _ _ h_dense _ ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.neg, truth_at]
  intro ⟨s, hts, _h_top, h_guard⟩
  obtain ⟨r, htr, hrs⟩ := @DenselyOrdered.dense D _ h_dense t s hts
  exact h_guard r htr hrs

theorem density_valid (φ : Formula Atom) :
    valid_dense ((φ.all_future.all_future).imp φ.all_future) := by
  intro D _ _ _ h_dense _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_GG ⟨s, hts, h_neg_φs, _⟩
  obtain ⟨r, htr, hrs⟩ := exists_between hts
  apply h_GG
  refine ⟨r, htr, fun h_Gφr => ?_, fun _ _ _ hf => absurd hf not_false⟩
  -- h_Gφr : Gφ(r) = (∃ q > r, ¬φ(q) ∧ guard) → False
  -- We have s > r and ¬φ(s), so feed to Gφ(r) to get False
  apply h_Gφr
  exact ⟨s, hrs, h_neg_φs, fun _ _ _ hf => absurd hf not_false⟩

theorem discrete_symm_fwd_valid :
    ⊨ ((Formula.untl (Formula.bot.imp (Formula.bot : Formula Atom)) Formula.bot).imp
      (Formula.snce (Formula.bot.imp Formula.bot) Formula.bot)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro ⟨s, hts, _h_top, h_guard⟩
  refine ⟨t - (s - t), sub_lt_self t (sub_pos.mpr hts), fun h => h, fun c hrc hct => ?_⟩
  have h1 : t < c + (s - t) :=
    calc t = t - (s - t) + (s - t) := (sub_add_cancel t (s - t)).symm
      _ < c + (s - t) := add_lt_add_left hrc (s - t)
  have h2 : c + (s - t) < s :=
    calc c + (s - t) < t + (s - t) := add_lt_add_left hct (s - t)
      _ = s := by rw [add_comm, sub_add_cancel]
  exact h_guard (c + (s - t)) h1 h2

theorem discrete_symm_bwd_valid :
    ⊨ ((Formula.snce (Formula.bot.imp (Formula.bot : Formula Atom)) Formula.bot).imp
      (Formula.untl (Formula.bot.imp Formula.bot) Formula.bot)) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro ⟨r, hrt, _h_top, h_guard⟩
  refine ⟨t + (t - r), lt_add_of_pos_right t (sub_pos.mpr hrt), fun h => h, fun c htc hcs => ?_⟩
  have h1 : r < c - (t - r) := by
    calc r = t - (t - r) := by rw [sub_sub_cancel]
      _ < c - (t - r) := sub_lt_sub_right htc _
  have h2 : c - (t - r) < t := by
    calc c - (t - r) < t + (t - r) - (t - r) := sub_lt_sub_right hcs _
      _ = t := by rw [add_sub_cancel_right]
  exact h_guard (c - (t - r)) h1 h2

theorem discrete_propagate_fwd_valid :
    ⊨ ((Formula.untl (Formula.bot.imp (Formula.bot : Formula Atom)) Formula.bot).imp
      (Formula.all_future (Formula.untl (Formula.bot.imp Formula.bot) Formula.bot))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro ⟨s, hts, _h_top, h_guard⟩ ⟨u, _htu, h_neg, _⟩
  apply h_neg
  refine ⟨u + (s - t), lt_add_of_pos_right u (sub_pos.mpr hts), fun h => h, fun c huc hcs => ?_⟩
  have h1 : t < c - (u - t) := by
    calc t = u - (u - t) := by rw [sub_sub_cancel]
      _ < c - (u - t) := sub_lt_sub_right huc _
  have h2 : c - (u - t) < s := by
    conv_rhs => rw [show s = u + (s - t) - (u - t) from by rw [add_sub_sub_cancel, sub_add_cancel]]
    exact sub_lt_sub_right hcs _
  exact h_guard (c - (u - t)) h1 h2

theorem discrete_propagate_bwd_valid :
    ⊨ ((Formula.untl (Formula.bot.imp (Formula.bot : Formula Atom)) Formula.bot).imp
      (Formula.all_past (Formula.untl (Formula.bot.imp Formula.bot) Formula.bot))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro ⟨s, hts, _h_top, h_guard⟩ ⟨u, _hut, h_neg, _⟩
  apply h_neg
  refine ⟨u + (s - t), lt_add_of_pos_right u (sub_pos.mpr hts), fun h => h, fun c huc hcs => ?_⟩
  have h1 : t < c - (u - t) := by
    calc t = u - (u - t) := by rw [sub_sub_cancel]
      _ < c - (u - t) := sub_lt_sub_right huc _
  have h2 : c - (u - t) < s := by
    conv_rhs => rw [show s = u + (s - t) - (u - t) from by rw [add_sub_sub_cancel, sub_add_cancel]]
    exact sub_lt_sub_right hcs _
  exact h_guard (c - (u - t)) h1 h2

theorem discrete_box_necessity_valid :
    ⊨ ((Formula.untl (Formula.bot.imp (Formula.bot : Formula Atom)) Formula.bot).imp
      (Formula.box (Formula.untl (Formula.bot.imp Formula.bot) Formula.bot))) := by
  intro D _ _ _ _ ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro ⟨s, hts, _h_top, h_guard⟩ σ _h_σ_mem
  exact ⟨s, hts, fun h => h, h_guard⟩

theorem prior_UZ_valid (φ : Formula Atom) : valid_discrete (φ.some_future.imp (Formula.untl φ φ.neg)) := by
  intro D _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact SoundnessLemmas.prior_UZ_is_valid φ ℱ M Omega h_sc τ h_mem t

theorem prior_SZ_valid (φ : Formula Atom) : valid_discrete (φ.some_past.imp (Formula.snce φ φ.neg)) := by
  intro D _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact SoundnessLemmas.prior_SZ_is_valid φ ℱ M Omega h_sc τ h_mem t

theorem z1_valid (φ : Formula Atom) : valid_discrete
    ((φ.all_future.imp φ).all_future.imp (φ.all_future.some_future.imp φ.all_future)) := by
  intro D _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
  exact SoundnessLemmas.z1_is_valid φ ℱ M Omega h_sc τ h_mem t

/-! ## Combined Axiom Validators -/

/-- All base TM axioms are universally valid. -/
theorem axiom_valid {φ : Formula Atom} (h : Axiom φ) (h_fc : h.minFrameClass ≤ FrameClass.Base) : ⊨ φ := by
  cases h with
  | imp_k φ ψ χ => exact prop_k_valid φ ψ χ
  | imp_s φ ψ => exact prop_s_valid φ ψ
  | modal_t ψ => exact modal_t_valid ψ
  | modal_4 ψ => exact modal_4_valid ψ
  | modal_b ψ => exact modal_b_valid ψ
  | modal_5_collapse ψ => exact modal_5_collapse_valid ψ
  | efq ψ => exact ex_falso_valid ψ
  | peirce φ ψ => exact peirce_valid φ ψ
  | modal_k_dist φ ψ => exact modal_k_dist_valid φ ψ
  | serial_future => exact serial_future_axiom_valid
  | serial_past => exact serial_past_axiom_valid
  | left_mono_until_G φ χ ψ => exact left_mono_until_G_valid φ χ ψ
  | left_mono_since_H φ χ ψ => exact left_mono_since_H_valid φ χ ψ
  | right_mono_until φ ψ χ => exact right_mono_until_valid φ ψ χ
  | right_mono_since φ ψ χ => exact right_mono_since_valid φ ψ χ
  | connect_future _ => exact connect_future_valid _
  | connect_past _ => exact connect_past_valid _
  | enrichment_until φ ψ p => exact enrichment_until_valid φ ψ p
  | enrichment_since φ ψ p => exact enrichment_since_valid φ ψ p
  | self_accum_until φ ψ => exact self_accum_until_valid φ ψ
  | self_accum_since φ ψ => exact self_accum_since_valid φ ψ
  | absorb_until φ ψ => exact absorb_until_valid φ ψ
  | absorb_since φ ψ => exact absorb_since_valid φ ψ
  | linear_until _ _ _ _ => exact linear_until_valid _ _ _ _
  | linear_since _ _ _ _ => exact linear_since_valid _ _ _ _
  | until_F φ ψ => exact until_F_valid φ ψ
  | since_P φ ψ => exact since_P_valid φ ψ
  | temp_linearity φ ψ => exact temp_linearity_valid φ ψ
  | temp_linearity_past φ ψ => exact temp_linearity_past_valid φ ψ
  | F_until_equiv φ => exact F_until_equiv_valid φ
  | P_since_equiv φ => exact P_since_equiv_valid φ
  | modal_future ψ => exact modal_future_valid ψ
  | discrete_symm_fwd => exact discrete_symm_fwd_valid
  | discrete_symm_bwd => exact discrete_symm_bwd_valid
  | discrete_propagate_fwd => exact discrete_propagate_fwd_valid
  | discrete_propagate_bwd => exact discrete_propagate_bwd_valid
  | discrete_box_necessity => exact discrete_box_necessity_valid
  | density _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | dense_indicator => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | prior_UZ _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | prior_SZ _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | z1 _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])

/-- All dense-compatible axioms are valid on dense frames. -/
theorem axiom_dense_valid {φ : Formula Atom} (h : Axiom φ) (h_fc : h.minFrameClass ≤ FrameClass.Dense) : valid_dense φ := by
  cases h with
  | imp_k φ ψ χ => exact Validity.valid_implies_valid_dense (prop_k_valid φ ψ χ)
  | imp_s φ ψ => exact Validity.valid_implies_valid_dense (prop_s_valid φ ψ)
  | modal_t ψ => exact Validity.valid_implies_valid_dense (modal_t_valid ψ)
  | modal_4 ψ => exact Validity.valid_implies_valid_dense (modal_4_valid ψ)
  | modal_b ψ => exact Validity.valid_implies_valid_dense (modal_b_valid ψ)
  | modal_5_collapse ψ => exact Validity.valid_implies_valid_dense (modal_5_collapse_valid ψ)
  | efq ψ => exact Validity.valid_implies_valid_dense (ex_falso_valid ψ)
  | peirce φ ψ => exact Validity.valid_implies_valid_dense (peirce_valid φ ψ)
  | modal_k_dist φ ψ => exact Validity.valid_implies_valid_dense (modal_k_dist_valid φ ψ)
  | serial_future => exact Validity.valid_implies_valid_dense serial_future_axiom_valid
  | serial_past => exact Validity.valid_implies_valid_dense serial_past_axiom_valid
  | left_mono_until_G φ χ ψ => exact Validity.valid_implies_valid_dense (left_mono_until_G_valid φ χ ψ)
  | left_mono_since_H φ χ ψ => exact Validity.valid_implies_valid_dense (left_mono_since_H_valid φ χ ψ)
  | right_mono_until φ ψ χ => exact Validity.valid_implies_valid_dense (right_mono_until_valid φ ψ χ)
  | right_mono_since φ ψ χ => exact Validity.valid_implies_valid_dense (right_mono_since_valid φ ψ χ)
  | connect_future _ => exact Validity.valid_implies_valid_dense (connect_future_valid _)
  | connect_past _ => exact Validity.valid_implies_valid_dense (connect_past_valid _)
  | enrichment_until φ ψ p => exact Validity.valid_implies_valid_dense (enrichment_until_valid φ ψ p)
  | enrichment_since φ ψ p => exact Validity.valid_implies_valid_dense (enrichment_since_valid φ ψ p)
  | self_accum_until φ ψ => exact Validity.valid_implies_valid_dense (self_accum_until_valid φ ψ)
  | self_accum_since φ ψ => exact Validity.valid_implies_valid_dense (self_accum_since_valid φ ψ)
  | absorb_until φ ψ => exact Validity.valid_implies_valid_dense (absorb_until_valid φ ψ)
  | absorb_since φ ψ => exact Validity.valid_implies_valid_dense (absorb_since_valid φ ψ)
  | linear_until _ _ _ _ => exact Validity.valid_implies_valid_dense (linear_until_valid _ _ _ _)
  | linear_since _ _ _ _ => exact Validity.valid_implies_valid_dense (linear_since_valid _ _ _ _)
  | until_F φ ψ => exact Validity.valid_implies_valid_dense (until_F_valid φ ψ)
  | since_P φ ψ => exact Validity.valid_implies_valid_dense (since_P_valid φ ψ)
  | temp_linearity φ ψ => exact Validity.valid_implies_valid_dense (temp_linearity_valid φ ψ)
  | temp_linearity_past φ ψ => exact Validity.valid_implies_valid_dense (temp_linearity_past_valid φ ψ)
  | F_until_equiv φ => exact Validity.valid_implies_valid_dense (F_until_equiv_valid φ)
  | P_since_equiv φ => exact Validity.valid_implies_valid_dense (P_since_equiv_valid φ)
  | modal_future ψ => exact Validity.valid_implies_valid_dense (modal_future_valid ψ)
  | discrete_symm_fwd => exact Validity.valid_implies_valid_dense discrete_symm_fwd_valid
  | discrete_symm_bwd => exact Validity.valid_implies_valid_dense discrete_symm_bwd_valid
  | discrete_propagate_fwd => exact Validity.valid_implies_valid_dense discrete_propagate_fwd_valid
  | discrete_propagate_bwd => exact Validity.valid_implies_valid_dense discrete_propagate_bwd_valid
  | discrete_box_necessity => exact Validity.valid_implies_valid_dense discrete_box_necessity_valid
  | density φ => exact density_valid φ
  | dense_indicator => exact dense_indicator_valid
  | prior_UZ _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | prior_SZ _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | z1 _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])

/-- All discrete-compatible axioms are valid on discrete frames. -/
theorem axiom_discrete_valid {φ : Formula Atom} (h : Axiom φ) (h_fc : h.minFrameClass ≤ FrameClass.Discrete) :
    valid_discrete φ := by
  cases h with
  | imp_k φ ψ χ => exact Validity.valid_implies_valid_discrete (prop_k_valid φ ψ χ)
  | imp_s φ ψ => exact Validity.valid_implies_valid_discrete (prop_s_valid φ ψ)
  | modal_t ψ => exact Validity.valid_implies_valid_discrete (modal_t_valid ψ)
  | modal_4 ψ => exact Validity.valid_implies_valid_discrete (modal_4_valid ψ)
  | modal_b ψ => exact Validity.valid_implies_valid_discrete (modal_b_valid ψ)
  | modal_5_collapse ψ => exact Validity.valid_implies_valid_discrete (modal_5_collapse_valid ψ)
  | efq ψ => exact Validity.valid_implies_valid_discrete (ex_falso_valid ψ)
  | peirce φ ψ => exact Validity.valid_implies_valid_discrete (peirce_valid φ ψ)
  | modal_k_dist φ ψ => exact Validity.valid_implies_valid_discrete (modal_k_dist_valid φ ψ)
  | serial_future => exact Validity.valid_implies_valid_discrete serial_future_axiom_valid
  | serial_past => exact Validity.valid_implies_valid_discrete serial_past_axiom_valid
  | left_mono_until_G φ χ ψ => exact Validity.valid_implies_valid_discrete (left_mono_until_G_valid φ χ ψ)
  | left_mono_since_H φ χ ψ => exact Validity.valid_implies_valid_discrete (left_mono_since_H_valid φ χ ψ)
  | right_mono_until φ ψ χ => exact Validity.valid_implies_valid_discrete (right_mono_until_valid φ ψ χ)
  | right_mono_since φ ψ χ => exact Validity.valid_implies_valid_discrete (right_mono_since_valid φ ψ χ)
  | connect_future _ => exact Validity.valid_implies_valid_discrete (connect_future_valid _)
  | connect_past _ => exact Validity.valid_implies_valid_discrete (connect_past_valid _)
  | enrichment_until φ ψ p => exact Validity.valid_implies_valid_discrete (enrichment_until_valid φ ψ p)
  | enrichment_since φ ψ p => exact Validity.valid_implies_valid_discrete (enrichment_since_valid φ ψ p)
  | self_accum_until φ ψ => exact Validity.valid_implies_valid_discrete (self_accum_until_valid φ ψ)
  | self_accum_since φ ψ => exact Validity.valid_implies_valid_discrete (self_accum_since_valid φ ψ)
  | absorb_until φ ψ => exact Validity.valid_implies_valid_discrete (absorb_until_valid φ ψ)
  | absorb_since φ ψ => exact Validity.valid_implies_valid_discrete (absorb_since_valid φ ψ)
  | linear_until _ _ _ _ => exact Validity.valid_implies_valid_discrete (linear_until_valid _ _ _ _)
  | linear_since _ _ _ _ => exact Validity.valid_implies_valid_discrete (linear_since_valid _ _ _ _)
  | until_F φ ψ => exact Validity.valid_implies_valid_discrete (until_F_valid φ ψ)
  | since_P φ ψ => exact Validity.valid_implies_valid_discrete (since_P_valid φ ψ)
  | temp_linearity φ ψ => exact Validity.valid_implies_valid_discrete (temp_linearity_valid φ ψ)
  | temp_linearity_past φ ψ => exact Validity.valid_implies_valid_discrete (temp_linearity_past_valid φ ψ)
  | F_until_equiv φ => exact Validity.valid_implies_valid_discrete (F_until_equiv_valid φ)
  | P_since_equiv φ => exact Validity.valid_implies_valid_discrete (P_since_equiv_valid φ)
  | modal_future ψ => exact Validity.valid_implies_valid_discrete (modal_future_valid ψ)
  | discrete_symm_fwd => exact Validity.valid_implies_valid_discrete discrete_symm_fwd_valid
  | discrete_symm_bwd => exact Validity.valid_implies_valid_discrete discrete_symm_bwd_valid
  | discrete_propagate_fwd => exact Validity.valid_implies_valid_discrete discrete_propagate_fwd_valid
  | discrete_propagate_bwd => exact Validity.valid_implies_valid_discrete discrete_propagate_bwd_valid
  | discrete_box_necessity => exact Validity.valid_implies_valid_discrete discrete_box_necessity_valid
  | density _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | dense_indicator => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | prior_UZ φ => exact prior_UZ_valid φ
  | prior_SZ φ => exact prior_SZ_valid φ
  | z1 φ => exact z1_valid φ

/-! ## Full Derivation Soundness -/

/-- Soundness Theorem (Base): Derivability in the base system implies semantic consequence. -/
theorem soundness (Γ : Context Atom) (φ : Formula Atom)
    (d : DerivationTree FrameClass.Base Γ φ)
    (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ)) (h_sc : ShiftClosed Omega)
    (τ : WorldHistory ℱ) (h_mem : τ ∈ Omega) (t : D)
    (h_ctx : ∀ ψ ∈ Γ, truth_at M Omega τ t ψ) :
    truth_at M Omega τ t φ := by
  induction d generalizing τ t with
  | «axiom» Γ' φ' h_ax h_fc => exact axiom_valid h_ax h_fc D ℱ M Omega h_sc τ h_mem t
  | assumption Γ' φ' h_in => exact h_ctx φ' h_in
  | modus_ponens Γ' φ' ψ' _ _ ih1 ih2 =>
    have h1 := ih1 τ h_mem t h_ctx
    have h2 := ih2 τ h_mem t h_ctx
    simp only [truth_at] at h1; exact h1 h2
  | necessitation φ' _ ih =>
    simp only [truth_at]
    intro σ h_σ_mem; exact ih σ h_σ_mem t (by simp)
  | temporal_necessitation φ' _ ih =>
    simp only [truth_at]
    intro ⟨s, _hts, h_neg, _⟩; exact h_neg (ih τ h_mem s (by simp))
  | temporal_duality φ' d' ih =>
    exact SoundnessLemmas.derivable_implies_swap_valid_general d' ℱ M Omega h_sc τ h_mem t
  | weakening Γ' Δ' φ' _ h_sub ih =>
    exact ih τ h_mem t (fun ψ h_in => h_ctx ψ (h_sub h_in))

/-- Soundness Dense Valid: Derivability from empty context implies dense validity. -/
theorem soundness_dense_valid {φ : Formula Atom}
    (d : DerivationTree FrameClass.Dense [] φ) : valid_dense φ := by
  match d with
  | .axiom _ _ h_ax h_fc => exact axiom_dense_valid h_ax h_fc
  | .assumption _ _ h_mem => exact absurd h_mem (Context.not_mem_nil _)
  | .modus_ponens _ ψ' _ d1 d2 =>
    have h1 := soundness_dense_valid d1
    have h2 := soundness_dense_valid d2
    intro D _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
    have h1' := h1 D ℱ M Omega h_sc τ h_mem t
    have h2' := h2 D ℱ M Omega h_sc τ h_mem t
    simp only [truth_at] at h1'; exact h1' h2'
  | .necessitation ψ' d' =>
    have h := soundness_dense_valid d'
    intro D _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
    simp only [truth_at]
    intro σ h_σ_mem; exact h D ℱ M Omega h_sc σ h_σ_mem t
  | .temporal_necessitation ψ' d' =>
    have h := soundness_dense_valid d'
    intro D _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
    simp only [truth_at]
    intro ⟨s, _hts, h_neg, _⟩; exact h_neg (h D ℱ M Omega h_sc τ h_mem s)
  | .temporal_duality ψ' d' =>
    intro D _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
    exact SoundnessLemmas.derivable_implies_swap_valid d' ℱ M Omega h_sc τ h_mem t
  | .weakening Γ' _ _ d' h_sub =>
    have h_eq : Γ' = [] := List.eq_nil_of_subset_nil h_sub
    have h_height_eq : (h_eq ▸ d').height = d'.height := by subst h_eq; rfl
    have h_term : (h_eq ▸ d').height < (DerivationTree.weakening Γ' [] _ d' h_sub).height := by
      simp only [h_height_eq, DerivationTree.height]; omega
    exact soundness_dense_valid (h_eq ▸ d')
termination_by d.height
decreasing_by
  all_goals first
    | exact DerivationTree.mp_height_gt_left _ _
    | exact DerivationTree.mp_height_gt_right _ _
    | simp only [DerivationTree.height]; omega

/-- Soundness for Dense Frames: Derivability implies semantic consequence on dense frames. -/
theorem soundness_dense (Γ : Context Atom) (φ : Formula Atom)
    (d : DerivationTree FrameClass.Dense Γ φ)
    (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [DenselyOrdered D] [Nontrivial D]
    (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ)) (h_sc : ShiftClosed Omega)
    (τ : WorldHistory ℱ) (h_mem : τ ∈ Omega) (t : D)
    (h_ctx : ∀ ψ ∈ Γ, truth_at M Omega τ t ψ) :
    truth_at M Omega τ t φ := by
  induction d generalizing τ t with
  | «axiom» Γ' φ' h_ax h_fc => exact axiom_dense_valid h_ax h_fc D ℱ M Omega h_sc τ h_mem t
  | assumption Γ' φ' h_in => exact h_ctx φ' h_in
  | modus_ponens Γ' φ' ψ' _ _ ih1 ih2 =>
    have h1 := ih1 τ h_mem t h_ctx
    have h2 := ih2 τ h_mem t h_ctx
    simp only [truth_at] at h1; exact h1 h2
  | necessitation φ' _ ih =>
    simp only [truth_at]
    intro σ h_σ_mem; exact ih σ h_σ_mem t (by simp)
  | temporal_necessitation φ' _ ih =>
    simp only [truth_at]
    intro ⟨s, _hts, h_neg, _⟩; exact h_neg (ih τ h_mem s (by simp))
  | temporal_duality φ' d' ih =>
    exact SoundnessLemmas.derivable_implies_swap_valid d' ℱ M Omega h_sc τ h_mem t
  | weakening Γ' Δ' φ' _ h_sub ih =>
    exact ih τ h_mem t (fun ψ h_in => h_ctx ψ (h_sub h_in))

/-! ## Discrete Frame Soundness -/

/-- Soundness Discrete Valid: Derivability from empty context implies discrete validity. -/
theorem soundness_discrete_valid {φ : Formula Atom}
    (d : DerivationTree FrameClass.Discrete [] φ) : valid_discrete φ := by
  match d with
  | .axiom _ _ h_ax h_fc => exact axiom_discrete_valid h_ax h_fc
  | .assumption _ _ h_mem => exact absurd h_mem (Context.not_mem_nil _)
  | .modus_ponens _ ψ' _ d1 d2 =>
    have h1 := soundness_discrete_valid d1
    have h2 := soundness_discrete_valid d2
    intro D _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
    have h1' := h1 D ℱ M Omega h_sc τ h_mem t
    have h2' := h2 D ℱ M Omega h_sc τ h_mem t
    simp only [truth_at] at h1'; exact h1' h2'
  | .necessitation ψ' d' =>
    have h := soundness_discrete_valid d'
    intro D _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
    simp only [truth_at]
    intro σ h_σ_mem; exact h D ℱ M Omega h_sc σ h_σ_mem t
  | .temporal_necessitation ψ' d' =>
    have h := soundness_discrete_valid d'
    intro D _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
    simp only [truth_at]
    intro ⟨s, _hts, h_neg, _⟩; exact h_neg (h D ℱ M Omega h_sc τ h_mem s)
  | .temporal_duality ψ' d' =>
    intro D _ _ _ _ _ _ _ _ ℱ M Omega h_sc τ h_mem t
    exact SoundnessLemmas.derivable_implies_swap_valid_discrete d' ℱ M Omega h_sc τ h_mem t
  | .weakening Γ' _ _ d' h_sub =>
    have h_eq : Γ' = [] := List.eq_nil_of_subset_nil h_sub
    have h_height_eq : (h_eq ▸ d').height = d'.height := by subst h_eq; rfl
    have h_term : (h_eq ▸ d').height < (DerivationTree.weakening Γ' [] _ d' h_sub).height := by
      simp only [h_height_eq, DerivationTree.height]; omega
    exact soundness_discrete_valid (h_eq ▸ d')
termination_by d.height
decreasing_by
  all_goals first
    | exact DerivationTree.mp_height_gt_left _ _
    | exact DerivationTree.mp_height_gt_right _ _
    | simp only [DerivationTree.height]; omega

/-- Soundness for Discrete Frames: Derivability implies semantic consequence on discrete frames. -/
theorem soundness_discrete (Γ : Context Atom) (φ : Formula Atom)
    (d : DerivationTree FrameClass.Discrete Γ φ)
    (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [SuccOrder D] [PredOrder D] [IsSuccArchimedean D] [IsPredArchimedean D] [Nontrivial D]
    (ℱ : TaskFrame D) (M : TaskModel Atom ℱ)
    (Omega : Set (WorldHistory ℱ)) (h_sc : ShiftClosed Omega)
    (τ : WorldHistory ℱ) (h_mem : τ ∈ Omega) (t : D)
    (h_ctx : ∀ ψ ∈ Γ, truth_at M Omega τ t ψ) :
    truth_at M Omega τ t φ := by
  induction d generalizing τ t with
  | «axiom» Γ' φ' h_ax h_fc => exact axiom_discrete_valid h_ax h_fc D ℱ M Omega h_sc τ h_mem t
  | assumption Γ' φ' h_in => exact h_ctx φ' h_in
  | modus_ponens Γ' φ' ψ' _ _ ih1 ih2 =>
    have h1 := ih1 τ h_mem t h_ctx
    have h2 := ih2 τ h_mem t h_ctx
    simp only [truth_at] at h1; exact h1 h2
  | necessitation φ' _ ih =>
    simp only [truth_at]
    intro σ h_σ_mem; exact ih σ h_σ_mem t (by simp)
  | temporal_necessitation φ' _ ih =>
    simp only [truth_at]
    intro ⟨s, _hts, h_neg, _⟩; exact h_neg (ih τ h_mem s (by simp))
  | temporal_duality φ' d' ih =>
    exact SoundnessLemmas.derivable_implies_swap_valid_discrete d' ℱ M Omega h_sc τ h_mem t
  | weakening Γ' Δ' φ' _ h_sub ih =>
    exact ih τ h_mem t (fun ψ h_in => h_ctx ψ (h_sub h_in))

end Cslib.Logic.Bimodal.Metalogic
