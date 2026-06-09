/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
import Cslib.Logics.Bimodal.Metalogic.Soundness.DenseValidity

/-!
# Soundness Lemmas for General and Discrete Frame Classes

General (Base) frame class and discrete frame class validity variants.
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.SoundnessLemmas

open Cslib.Logic.Bimodal

variable {Atom : Type*}
variable {D : Type} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

/-! ## General (Frame-Class-Free) Versions -/

/-- All base axiom swaps are valid without DenselyOrdered constraints. -/
theorem axiom_swap_valid_general (φ : Formula Atom) (h : Axiom φ) (h_fc : h.minFrameClass ≤ FrameClass.Base)
    [Nontrivial D] : is_valid D φ.swap_temporal := by
  -- Base axioms are a subset of dense axioms. Their proofs never use DenselyOrdered.
  -- We reproduce the proofs from axiom_swap_valid, excluding density/discrete cases.
  cases h with
  | imp_k ψ χ ρ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro h_abc h_ab h_a; exact h_abc h_a (h_ab h_a)
  | imp_s ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro h_a _; exact h_a
  | modal_t ψ => exact swap_axiom_mt_valid ψ
  | modal_4 ψ => exact swap_axiom_m4_valid ψ
  | modal_b ψ => exact swap_axiom_mb_valid ψ
  | modal_5_collapse ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.diamond, Formula.neg, truth_at]
    intro h_diamond_box σ h_σ_mem
    by_contra h_not; apply h_diamond_box
    intro ρ h_ρ_mem h_box; exact h_not (h_box σ h_σ_mem)
  | efq ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro h_bot; exfalso; exact h_bot
  | peirce ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro h_peirce
    by_cases h : truth_at M Omega τ t ψ.swap_temporal
    · exact h
    · exact h_peirce (fun h_psi => absurd h_psi h)
  | modal_k_dist ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro h_box_imp h_box σ h_σ_mem; exact h_box_imp σ h_σ_mem (h_box σ h_σ_mem)
  | serial_future =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro _; obtain ⟨s, hst⟩ := exists_lt t
    exact ⟨s, hst, fun h => h, fun _ _ _ hf => absurd hf not_false⟩
  | serial_past =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro _; obtain ⟨s, hts⟩ := exists_gt t
    exact ⟨s, hts, fun h => h, fun _ _ _ hf => absurd hf not_false⟩
  | left_mono_until_G φ χ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro h_H ⟨s, hst, h_ψs, h_guard⟩
    refine ⟨s, hst, h_ψs, fun r hsr hrt => ?_⟩
    have : truth_at M Omega τ r φ.swap_temporal → truth_at M Omega τ r χ.swap_temporal := by
      intro h_φr; by_contra h_neg
      apply h_H; exact ⟨r, hrt, fun h => h_neg (h h_φr), fun _ _ _ hf => absurd hf not_false⟩
    exact this (h_guard r hsr hrt)
  | left_mono_since_H φ χ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro h_G ⟨s, hts, h_ψs, h_guard⟩
    refine ⟨s, hts, h_ψs, fun r htr hrs => ?_⟩
    have : truth_at M Omega τ r φ.swap_temporal → truth_at M Omega τ r χ.swap_temporal := by
      intro h_φr; by_contra h_neg
      apply h_G; exact ⟨r, htr, fun h => h_neg (h h_φr), fun _ _ _ hf => absurd hf not_false⟩
    exact this (h_guard r htr hrs)
  | right_mono_until φ ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro h_H ⟨s, hst, h_φs, h_guard⟩
    have h_ψs : truth_at M Omega τ s ψ.swap_temporal := by
      by_contra h_neg; apply h_H
      exact ⟨s, hst, fun h => h_neg (h h_φs), fun _ _ _ hf => absurd hf not_false⟩
    exact ⟨s, hst, h_ψs, h_guard⟩
  | right_mono_since φ ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro h_G ⟨s, hts, h_φs, h_guard⟩
    have h_ψs : truth_at M Omega τ s ψ.swap_temporal := by
      by_contra h_neg; apply h_G
      exact ⟨s, hts, fun h => h_neg (h h_φs), fun _ _ _ hf => absurd hf not_false⟩
    exact ⟨s, hts, h_ψs, h_guard⟩
  | connect_future φ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro h_φt ⟨s, hst, h_neg, _⟩
    apply h_neg; exact ⟨t, hst, h_φt, fun _ _ _ hf => absurd hf not_false⟩
  | connect_past φ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro h_φt ⟨s, hts, h_neg, _⟩
    apply h_neg; exact ⟨t, hts, h_φt, fun _ _ _ hf => absurd hf not_false⟩
  | enrichment_until φ ψ p =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.and, Formula.neg, truth_at]
    intro h_conj
    have h_pt : truth_at M Omega τ t p.swap_temporal := by
      by_contra h_neg; exact h_conj (fun h_p _ => h_neg h_p)
    have h_since : ∃ s, s < t ∧ truth_at M Omega τ s ψ.swap_temporal ∧
        ∀ r, s < r → r < t → truth_at M Omega τ r φ.swap_temporal := by
      by_contra h_neg; exact h_conj (fun _ h_s => h_neg h_s)
    obtain ⟨s, hst, h_ψs, h_guard⟩ := h_since
    refine ⟨s, hst, ?_, h_guard⟩
    intro h_imp; exact h_imp h_ψs ⟨t, hst, h_pt, fun r hsr hrt => h_guard r hsr hrt⟩
  | enrichment_since φ ψ p =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.and, Formula.neg, truth_at]
    intro h_conj
    have h_pt : truth_at M Omega τ t p.swap_temporal := by
      by_contra h_neg; exact h_conj (fun h_p _ => h_neg h_p)
    have h_until : ∃ s, t < s ∧ truth_at M Omega τ s ψ.swap_temporal ∧
        ∀ r, t < r → r < s → truth_at M Omega τ r φ.swap_temporal := by
      by_contra h_neg; exact h_conj (fun _ h_u => h_neg h_u)
    obtain ⟨s, hts, h_ψs, h_guard⟩ := h_until
    refine ⟨s, hts, ?_, h_guard⟩
    intro h_imp; exact h_imp h_ψs ⟨t, hts, h_pt, fun r htr hrs => h_guard r htr hrs⟩
  | self_accum_until φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.and, Formula.neg, truth_at]
    intro ⟨s, hst, h_ψs, h_guard⟩
    refine ⟨s, hst, h_ψs, fun r hsr hrt h_imp => ?_⟩
    exact h_imp (h_guard r hsr hrt) ⟨s, hsr, h_ψs, fun q hsq hqr => h_guard q hsq (lt_trans hqr hrt)⟩
  | self_accum_since φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.and, Formula.neg, truth_at]
    intro ⟨s, hts, h_ψs, h_guard⟩
    refine ⟨s, hts, h_ψs, fun r htr hrs h_imp => ?_⟩
    exact h_imp (h_guard r htr hrs) ⟨s, hrs, h_ψs, fun q hrq hqs => h_guard q (lt_trans htr hrq) hqs⟩
  | absorb_until φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.and, Formula.neg, truth_at]
    intro ⟨s₁, hs₁t, h_conj, h_guard₁⟩
    have ⟨h_φs₁, s₂, hs₂s₁, h_ψs₂, h_guard₂⟩ :
        truth_at M Omega τ s₁ φ.swap_temporal ∧
        (∃ s₂, s₂ < s₁ ∧ truth_at M Omega τ s₂ ψ.swap_temporal ∧
          ∀ q, s₂ < q → q < s₁ → truth_at M Omega τ q φ.swap_temporal) := by
      exact ⟨by by_contra h; exact h_conj (fun h_φ _ => h h_φ),
             by by_contra h; exact h_conj (fun _ h_s => h h_s)⟩
    refine ⟨s₂, lt_trans hs₂s₁ hs₁t, h_ψs₂, fun q hs₂q hqt => ?_⟩
    rcases lt_trichotomy q s₁ with h_lt | h_eq | h_gt
    · exact h_guard₂ q hs₂q h_lt
    · exact h_eq ▸ h_φs₁
    · exact h_guard₁ q h_gt hqt
  | absorb_since φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.and, Formula.neg, truth_at]
    intro ⟨s₁, hts₁, h_conj, h_guard₁⟩
    have ⟨h_φs₁, s₂, hs₁s₂, h_ψs₂, h_guard₂⟩ :
        truth_at M Omega τ s₁ φ.swap_temporal ∧
        (∃ s₂, s₁ < s₂ ∧ truth_at M Omega τ s₂ ψ.swap_temporal ∧
          ∀ q, s₁ < q → q < s₂ → truth_at M Omega τ q φ.swap_temporal) := by
      exact ⟨by by_contra h; exact h_conj (fun h_φ _ => h h_φ),
             by by_contra h; exact h_conj (fun _ h_u => h h_u)⟩
    refine ⟨s₂, lt_trans hts₁ hs₁s₂, h_ψs₂, fun q htq hqs₂ => ?_⟩
    rcases lt_trichotomy q s₁ with h_lt | h_eq | h_gt
    · exact h_guard₁ q htq h_lt
    · exact h_eq ▸ h_φs₁
    · exact h_guard₂ q h_gt hqs₂
  | linear_until φ ψ χ θ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.and, Formula.or, Formula.neg, truth_at]
    intro h_conj
    have h_both : (∃ s, s < t ∧ truth_at M Omega τ s ψ.swap_temporal ∧
        ∀ r, s < r → r < t → truth_at M Omega τ r φ.swap_temporal) ∧
      (∃ s, s < t ∧ truth_at M Omega τ s θ.swap_temporal ∧
        ∀ r, s < r → r < t → truth_at M Omega τ r χ.swap_temporal) := by
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
  | linear_since φ ψ χ θ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.and, Formula.or, Formula.neg, truth_at]
    intro h_conj
    have h_both : (∃ s, t < s ∧ truth_at M Omega τ s ψ.swap_temporal ∧
        ∀ r, t < r → r < s → truth_at M Omega τ r φ.swap_temporal) ∧
      (∃ s, t < s ∧ truth_at M Omega τ s θ.swap_temporal ∧
        ∀ r, t < r → r < s → truth_at M Omega τ r χ.swap_temporal) := by
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
  | until_F φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro ⟨s, hst, h_ψs, _⟩
    exact ⟨s, hst, h_ψs, fun _ _ _ hf => absurd hf not_false⟩
  | since_P φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro ⟨s, hts, h_ψs, _⟩
    exact ⟨s, hts, h_ψs, fun _ _ _ hf => absurd hf not_false⟩
  | temp_linearity φ ψ =>
    -- swap of future linearity: use past linearity with swapped subformulas
    exact axiom_temp_linearity_past_valid φ.swap_temporal ψ.swap_temporal
  | temp_linearity_past φ ψ =>
    exact axiom_temp_linearity_valid φ.swap_temporal ψ.swap_temporal
  | F_until_equiv φ => exact axiom_P_since_equiv_valid φ.swap_temporal
  | P_since_equiv φ => exact axiom_F_until_equiv_valid φ.swap_temporal
  | modal_future ψ => exact swap_axiom_mf_valid ψ
  | discrete_symm_fwd =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro ⟨r, hrt, _h_top_r, h_guard⟩
    refine ⟨t + (t - r), lt_add_of_pos_right t (sub_pos.mpr hrt), fun h => h, fun c htc hcs => ?_⟩
    have h1 : r < c - (t - r) := by
      calc r = t - (t - r) := by rw [sub_sub_cancel]
        _ < c - (t - r) := sub_lt_sub_right htc _
    have h2 : c - (t - r) < t := by
      calc c - (t - r) < t + (t - r) - (t - r) := sub_lt_sub_right hcs _
        _ = t := by rw [add_sub_cancel_right]
    exact h_guard (c - (t - r)) h1 h2
  | discrete_symm_bwd =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro ⟨s, hts, _h_top_s, h_guard⟩
    refine ⟨t - (s - t), sub_lt_self t (sub_pos.mpr hts), fun h => h, fun c hrc hct => ?_⟩
    have h1 : t < c + (s - t) :=
      calc t = t - (s - t) + (s - t) := (sub_add_cancel t (s - t)).symm
        _ < c + (s - t) := add_lt_add_left hrc (s - t)
    have h2 : c + (s - t) < s :=
      calc c + (s - t) < t + (s - t) := add_lt_add_left hct (s - t)
        _ = s := by rw [add_comm, sub_add_cancel]
    exact h_guard (c + (s - t)) h1 h2
  | discrete_propagate_fwd =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro ⟨r, hrt, _h_top_r, h_guard⟩ ⟨u, _hut, h_neg, _⟩
    apply h_neg
    refine ⟨u - (t - r), sub_lt_self u (sub_pos.mpr hrt), fun h => h, fun c hrc hcu => ?_⟩
    have h1 : r < c + (t - u) := by
      conv_lhs => rw [show r = u - (t - r) + (t - u) from by rw [sub_add_sub_cancel', sub_sub_cancel]]
      exact add_lt_add_left hrc (t - u)
    have h2 : c + (t - u) < t := by
      conv_rhs => rw [show t = u + (t - u) from by rw [add_comm, sub_add_cancel]]
      exact add_lt_add_left hcu (t - u)
    exact h_guard (c + (t - u)) h1 h2
  | discrete_propagate_bwd =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro ⟨r, hrt, _h_top_r, h_guard⟩ ⟨u, _htu, h_neg, _⟩
    apply h_neg
    refine ⟨u - (t - r), sub_lt_self u (sub_pos.mpr hrt), fun h => h, fun c hrc hcu => ?_⟩
    have h1 : r < c + (t - u) := by
      conv_lhs => rw [show r = u - (t - r) + (t - u) from by rw [sub_add_sub_cancel', sub_sub_cancel]]
      exact add_lt_add_left hrc (t - u)
    have h2 : c + (t - u) < t := by
      conv_rhs => rw [show t = u + (t - u) from by rw [add_comm, sub_add_cancel]]
      exact add_lt_add_left hcu (t - u)
    exact h_guard (c + (t - u)) h1 h2
  | discrete_box_necessity =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro ⟨r, hrt, _h_top_r, h_guard⟩ σ _h_σ_mem
    exact ⟨r, hrt, fun h => h, h_guard⟩
  | density _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | dense_indicator => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | prior_UZ _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | prior_SZ _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | z1 _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])

/-- All base axioms are locally valid without DenselyOrdered constraints. -/
private theorem axiom_locally_valid_general [Nontrivial D] {φ : Formula Atom} (h : Axiom φ)
    (h_fc : h.minFrameClass ≤ FrameClass.Base) : is_valid D φ := by
  -- All base cases are identical to axiom_locally_valid in DenseValidity
  -- (which never uses DenselyOrdered for base axioms)
  cases h with
  | imp_k φ ψ χ => exact axiom_prop_k_valid φ ψ χ
  | imp_s φ ψ => exact axiom_prop_s_valid φ ψ
  | modal_t ψ => exact axiom_modal_t_valid ψ
  | modal_4 ψ => exact axiom_modal_4_valid ψ
  | modal_b ψ => exact axiom_modal_b_valid ψ
  | modal_5_collapse ψ => exact axiom_modal_5_collapse_valid ψ
  | efq ψ => exact axiom_ex_falso_valid ψ
  | peirce φ ψ => exact axiom_peirce_valid φ ψ
  | modal_k_dist φ ψ => exact axiom_modal_k_dist_valid φ ψ
  | serial_future =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [truth_at]
    intro _; obtain ⟨s, hts⟩ := exists_gt t
    exact ⟨s, hts, fun h => h, fun _ _ _ hf => absurd hf not_false⟩
  | serial_past =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [truth_at]
    intro _; obtain ⟨s, hst⟩ := exists_lt t
    exact ⟨s, hst, fun h => h, fun _ _ _ hf => absurd hf not_false⟩
  | left_mono_until_G φ χ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro h_G ⟨s, hts, h_ψs, h_guard⟩
    refine ⟨s, hts, h_ψs, fun r htr hrs => ?_⟩
    have : truth_at M Omega τ r φ → truth_at M Omega τ r χ := by
      intro h_φr; by_contra h_neg
      apply h_G; exact ⟨r, htr, fun h => h_neg (h h_φr), fun _ _ _ hf => absurd hf not_false⟩
    exact this (h_guard r htr hrs)
  | left_mono_since_H φ χ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro h_H ⟨s, hst, h_ψs, h_guard⟩
    refine ⟨s, hst, h_ψs, fun r hsr hrt => ?_⟩
    have : truth_at M Omega τ r φ → truth_at M Omega τ r χ := by
      intro h_φr; by_contra h_neg
      apply h_H; exact ⟨r, hrt, fun h => h_neg (h h_φr), fun _ _ _ hf => absurd hf not_false⟩
    exact this (h_guard r hsr hrt)
  | right_mono_until φ ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro h_G ⟨s, hts, h_φs, h_guard⟩
    have h_ψs : truth_at M Omega τ s ψ := by
      by_contra h_neg; apply h_G
      exact ⟨s, hts, fun h => h_neg (h h_φs), fun _ _ _ hf => absurd hf not_false⟩
    exact ⟨s, hts, h_ψs, h_guard⟩
  | right_mono_since φ ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro h_H ⟨s, hst, h_φs, h_guard⟩
    have h_ψs : truth_at M Omega τ s ψ := by
      by_contra h_neg; apply h_H
      exact ⟨s, hst, fun h => h_neg (h h_φs), fun _ _ _ hf => absurd hf not_false⟩
    exact ⟨s, hst, h_ψs, h_guard⟩
  | connect_future φ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro h_φt ⟨s, hts, h_neg, _⟩
    apply h_neg; exact ⟨t, hts, h_φt, fun _ _ _ hf => absurd hf not_false⟩
  | connect_past φ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro h_φt ⟨s, hst, h_neg, _⟩
    apply h_neg; exact ⟨t, hst, h_φt, fun _ _ _ hf => absurd hf not_false⟩
  | enrichment_until φ ψ p =>
    intro ℱ M Omega _h_sc τ _h_mem t
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
  | enrichment_since φ ψ p =>
    intro ℱ M Omega _h_sc τ _h_mem t
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
  | self_accum_until φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.and, Formula.neg, truth_at]
    intro ⟨s, hts, h_ψs, h_guard⟩
    refine ⟨s, hts, h_ψs, fun r htr hrs h_imp => ?_⟩
    exact h_imp (h_guard r htr hrs) ⟨s, hrs, h_ψs, fun q hrq hqs => h_guard q (lt_trans htr hrq) hqs⟩
  | self_accum_since φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.and, Formula.neg, truth_at]
    intro ⟨s, hst, h_ψs, h_guard⟩
    refine ⟨s, hst, h_ψs, fun r hsr hrt h_imp => ?_⟩
    exact h_imp (h_guard r hsr hrt) ⟨s, hsr, h_ψs, fun q hsq hqr => h_guard q hsq (lt_trans hqr hrt)⟩
  | absorb_until φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
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
  | absorb_since φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
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
  | linear_until φ ψ χ θ =>
    intro ℱ M Omega _h_sc τ _h_mem t
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
  | linear_since φ ψ χ θ =>
    intro ℱ M Omega _h_sc τ _h_mem t
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
  | until_F φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [truth_at]
    intro ⟨s, hts, h_ψs, _⟩
    exact ⟨s, hts, h_ψs, fun _ _ _ hf => absurd hf not_false⟩
  | since_P φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [truth_at]
    intro ⟨s, hst, h_ψs, _⟩
    exact ⟨s, hst, h_ψs, fun _ _ _ hf => absurd hf not_false⟩
  | temp_linearity φ ψ => exact axiom_temp_linearity_valid φ ψ
  | temp_linearity_past φ ψ => exact axiom_temp_linearity_past_valid φ ψ
  | F_until_equiv φ => exact axiom_F_until_equiv_valid φ
  | P_since_equiv φ => exact axiom_P_since_equiv_valid φ
  | modal_future ψ => exact axiom_modal_future_valid ψ
  | discrete_symm_fwd =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [truth_at]
    intro ⟨s, hts, _h_top_s, h_guard⟩
    refine ⟨t - (s - t), sub_lt_self t (sub_pos.mpr hts), fun h => h, fun c hrc hct => ?_⟩
    have h1 : t < c + (s - t) :=
      calc t = t - (s - t) + (s - t) := (sub_add_cancel t (s - t)).symm
        _ < c + (s - t) := add_lt_add_left hrc (s - t)
    have h2 : c + (s - t) < s :=
      calc c + (s - t) < t + (s - t) := add_lt_add_left hct (s - t)
        _ = s := by rw [add_comm, sub_add_cancel]
    exact h_guard (c + (s - t)) h1 h2
  | discrete_symm_bwd =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [truth_at]
    intro ⟨r, hrt, _h_top_r, h_guard⟩
    refine ⟨t + (t - r), lt_add_of_pos_right t (sub_pos.mpr hrt), fun h => h, fun c htc hcs => ?_⟩
    have h1 : r < c - (t - r) := by
      calc r = t - (t - r) := by rw [sub_sub_cancel]
        _ < c - (t - r) := sub_lt_sub_right htc _
    have h2 : c - (t - r) < t := by
      calc c - (t - r) < t + (t - r) - (t - r) := sub_lt_sub_right hcs _
        _ = t := by rw [add_sub_cancel_right]
    exact h_guard (c - (t - r)) h1 h2
  | discrete_propagate_fwd =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro ⟨s, hts, _h_top_s, h_guard⟩ ⟨u, _htu, h_neg, _⟩
    apply h_neg
    refine ⟨u + (s - t), lt_add_of_pos_right u (sub_pos.mpr hts), fun h => h, fun c huc hcs => ?_⟩
    have h1 : t < c - (u - t) := by
      calc t = u - (u - t) := by rw [sub_sub_cancel]
        _ < c - (u - t) := sub_lt_sub_right huc _
    have h2 : c - (u - t) < s := by
      conv_rhs => rw [show s = u + (s - t) - (u - t) from by rw [add_sub_sub_cancel, sub_add_cancel]]
      exact sub_lt_sub_right hcs _
    exact h_guard (c - (u - t)) h1 h2
  | discrete_propagate_bwd =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro ⟨s, hts, _h_top_s, h_guard⟩ ⟨u, _hut, h_neg, _⟩
    apply h_neg
    refine ⟨u + (s - t), lt_add_of_pos_right u (sub_pos.mpr hts), fun h => h, fun c huc hcs => ?_⟩
    have h1 : t < c - (u - t) := by
      calc t = u - (u - t) := by rw [sub_sub_cancel]
        _ < c - (u - t) := sub_lt_sub_right huc _
    have h2 : c - (u - t) < s := by
      conv_rhs => rw [show s = u + (s - t) - (u - t) from by rw [add_sub_sub_cancel, sub_add_cancel]]
      exact sub_lt_sub_right hcs _
    exact h_guard (c - (u - t)) h1 h2
  | discrete_box_necessity =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [truth_at]
    intro ⟨s, hts, _h_top_s, h_guard⟩ σ _h_σ_mem
    exact ⟨s, hts, fun h => h, h_guard⟩
  | density _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | dense_indicator => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | prior_UZ _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | prior_SZ _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | z1 _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])

-- TODO: Continue with remaining content (derivable_valid_and_swap_valid_general,
-- Prior-UZ/SZ/Z1 discrete proofs, discrete combined soundness).
-- See handoff document for porting patterns.

end Cslib.Logic.Bimodal.Metalogic.SoundnessLemmas
