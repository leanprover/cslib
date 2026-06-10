/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Soundness.DenseValidity
public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Soundness Lemmas for General and Discrete Frame Classes

General (Base) frame class and discrete frame class validity variants.
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.SoundnessLemmas

open Cslib.Logic.Bimodal

variable {Atom : Type*}
variable {D : Type} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

/-! ## General (Frame-Class-Free) Versions -/

/-- All base axiom swaps are valid without DenselyOrdered constraints. -/
theorem axiom_swap_valid_general (φ : Formula Atom) (h : Axiom φ) (h_fc : h.minFrameClass ≤ FrameClass.Base)
    [Nontrivial D] : is_valid D φ.swapTemporal := by
  -- Base axioms are a subset of dense axioms. Their proofs never use DenselyOrdered.
  -- We reproduce the proofs from axiom_swap_valid, excluding density/discrete cases.
  cases h with
  | imp_k ψ χ ρ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, truth_at]
    intro h_abc h_ab h_a; exact h_abc h_a (h_ab h_a)
  | imp_s ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, truth_at]
    intro h_a _; exact h_a
  | modal_t ψ => exact swap_axiom_mt_valid ψ
  | modal_4 ψ => exact swap_axiom_m4_valid ψ
  | modal_b ψ => exact swap_axiom_mb_valid ψ
  | modal_5_collapse ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, Formula.diamond, Formula.neg, truth_at]
    intro h_diamond_box σ h_σ_mem
    by_contra h_not; apply h_diamond_box
    intro ρ h_ρ_mem h_box; exact h_not (h_box σ h_σ_mem)
  | efq ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, truth_at]
    intro h_bot; exfalso; exact h_bot
  | peirce ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, truth_at]
    intro h_peirce
    by_cases h : truth_at M Omega τ t ψ.swapTemporal
    · exact h
    · exact h_peirce (fun h_psi => absurd h_psi h)
  | modal_k_dist ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, truth_at]
    intro h_box_imp h_box σ h_σ_mem; exact h_box_imp σ h_σ_mem (h_box σ h_σ_mem)
  | serial_future =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, truth_at]
    intro _; obtain ⟨s, hst⟩ := exists_lt t
    exact ⟨s, hst, fun h => h, fun _ _ _ hf => absurd hf not_false⟩
  | serial_past =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, truth_at]
    intro _; obtain ⟨s, hts⟩ := exists_gt t
    exact ⟨s, hts, fun h => h, fun _ _ _ hf => absurd hf not_false⟩
  | left_mono_until_G φ χ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swapTemporal truth_at
    intro h_H ⟨s, hst, h_ψs, h_guard⟩
    refine ⟨s, hst, h_ψs, fun r hsr hrt => ?_⟩
    have : truth_at M Omega τ r φ.swapTemporal → truth_at M Omega τ r χ.swapTemporal := by
      intro h_φr; by_contra h_neg
      apply h_H; exact ⟨r, hrt, fun h => h_neg (h h_φr), fun _ _ _ hf => absurd hf not_false⟩
    exact this (h_guard r hsr hrt)
  | left_mono_since_H φ χ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swapTemporal truth_at
    intro h_G ⟨s, hts, h_ψs, h_guard⟩
    refine ⟨s, hts, h_ψs, fun r htr hrs => ?_⟩
    have : truth_at M Omega τ r φ.swapTemporal → truth_at M Omega τ r χ.swapTemporal := by
      intro h_φr; by_contra h_neg
      apply h_G; exact ⟨r, htr, fun h => h_neg (h h_φr), fun _ _ _ hf => absurd hf not_false⟩
    exact this (h_guard r htr hrs)
  | right_mono_until φ ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swapTemporal truth_at
    intro h_H ⟨s, hst, h_φs, h_guard⟩
    have h_ψs : truth_at M Omega τ s ψ.swapTemporal := by
      by_contra h_neg; apply h_H
      exact ⟨s, hst, fun h => h_neg (h h_φs), fun _ _ _ hf => absurd hf not_false⟩
    exact ⟨s, hst, h_ψs, h_guard⟩
  | right_mono_since φ ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swapTemporal truth_at
    intro h_G ⟨s, hts, h_φs, h_guard⟩
    have h_ψs : truth_at M Omega τ s ψ.swapTemporal := by
      by_contra h_neg; apply h_G
      exact ⟨s, hts, fun h => h_neg (h h_φs), fun _ _ _ hf => absurd hf not_false⟩
    exact ⟨s, hts, h_ψs, h_guard⟩
  | connect_future φ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swapTemporal truth_at
    intro h_φt ⟨s, hst, h_neg, _⟩
    apply h_neg; exact ⟨t, hst, h_φt, fun _ _ _ hf => absurd hf not_false⟩
  | connect_past φ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swapTemporal truth_at
    intro h_φt ⟨s, hts, h_neg, _⟩
    apply h_neg; exact ⟨t, hts, h_φt, fun _ _ _ hf => absurd hf not_false⟩
  | enrichment_until φ ψ p =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, Formula.and, Formula.neg, truth_at]
    intro h_conj
    have h_pt : truth_at M Omega τ t p.swapTemporal := by
      by_contra h_neg; exact h_conj (fun h_p _ => h_neg h_p)
    have h_since : ∃ s, s < t ∧ truth_at M Omega τ s ψ.swapTemporal ∧
        ∀ r, s < r → r < t → truth_at M Omega τ r φ.swapTemporal := by
      by_contra h_neg; exact h_conj (fun _ h_s => h_neg h_s)
    obtain ⟨s, hst, h_ψs, h_guard⟩ := h_since
    refine ⟨s, hst, ?_, h_guard⟩
    intro h_imp; exact h_imp h_ψs ⟨t, hst, h_pt, fun r hsr hrt => h_guard r hsr hrt⟩
  | enrichment_since φ ψ p =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, Formula.and, Formula.neg, truth_at]
    intro h_conj
    have h_pt : truth_at M Omega τ t p.swapTemporal := by
      by_contra h_neg; exact h_conj (fun h_p _ => h_neg h_p)
    have h_until : ∃ s, t < s ∧ truth_at M Omega τ s ψ.swapTemporal ∧
        ∀ r, t < r → r < s → truth_at M Omega τ r φ.swapTemporal := by
      by_contra h_neg; exact h_conj (fun _ h_u => h_neg h_u)
    obtain ⟨s, hts, h_ψs, h_guard⟩ := h_until
    refine ⟨s, hts, ?_, h_guard⟩
    intro h_imp; exact h_imp h_ψs ⟨t, hts, h_pt, fun r htr hrs => h_guard r htr hrs⟩
  | self_accum_until φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, Formula.and, Formula.neg, truth_at]
    intro ⟨s, hst, h_ψs, h_guard⟩
    refine ⟨s, hst, h_ψs, fun r hsr hrt h_imp => ?_⟩
    exact h_imp (h_guard r hsr hrt) ⟨s, hsr, h_ψs, fun q hsq hqr => h_guard q hsq (lt_trans hqr hrt)⟩
  | self_accum_since φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, Formula.and, Formula.neg, truth_at]
    intro ⟨s, hts, h_ψs, h_guard⟩
    refine ⟨s, hts, h_ψs, fun r htr hrs h_imp => ?_⟩
    exact h_imp (h_guard r htr hrs) ⟨s, hrs, h_ψs, fun q hrq hqs => h_guard q (lt_trans htr hrq) hqs⟩
  | absorb_until φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, Formula.and, Formula.neg, truth_at]
    intro ⟨s₁, hs₁t, h_conj, h_guard₁⟩
    have ⟨h_φs₁, s₂, hs₂s₁, h_ψs₂, h_guard₂⟩ :
        truth_at M Omega τ s₁ φ.swapTemporal ∧
        (∃ s₂, s₂ < s₁ ∧ truth_at M Omega τ s₂ ψ.swapTemporal ∧
          ∀ q, s₂ < q → q < s₁ → truth_at M Omega τ q φ.swapTemporal) := by
      exact ⟨by by_contra h; exact h_conj (fun h_φ _ => h h_φ),
             by by_contra h; exact h_conj (fun _ h_s => h h_s)⟩
    refine ⟨s₂, lt_trans hs₂s₁ hs₁t, h_ψs₂, fun q hs₂q hqt => ?_⟩
    rcases lt_trichotomy q s₁ with h_lt | h_eq | h_gt
    · exact h_guard₂ q hs₂q h_lt
    · exact h_eq ▸ h_φs₁
    · exact h_guard₁ q h_gt hqt
  | absorb_since φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, Formula.and, Formula.neg, truth_at]
    intro ⟨s₁, hts₁, h_conj, h_guard₁⟩
    have ⟨h_φs₁, s₂, hs₁s₂, h_ψs₂, h_guard₂⟩ :
        truth_at M Omega τ s₁ φ.swapTemporal ∧
        (∃ s₂, s₁ < s₂ ∧ truth_at M Omega τ s₂ ψ.swapTemporal ∧
          ∀ q, s₁ < q → q < s₂ → truth_at M Omega τ q φ.swapTemporal) := by
      exact ⟨by by_contra h; exact h_conj (fun h_φ _ => h h_φ),
             by by_contra h; exact h_conj (fun _ h_u => h h_u)⟩
    refine ⟨s₂, lt_trans hts₁ hs₁s₂, h_ψs₂, fun q htq hqs₂ => ?_⟩
    rcases lt_trichotomy q s₁ with h_lt | h_eq | h_gt
    · exact h_guard₁ q htq h_lt
    · exact h_eq ▸ h_φs₁
    · exact h_guard₂ q h_gt hqs₂
  | linear_until φ ψ χ θ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, Formula.and, Formula.or, Formula.neg, truth_at]
    intro h_conj
    have h_both : (∃ s, s < t ∧ truth_at M Omega τ s ψ.swapTemporal ∧
        ∀ r, s < r → r < t → truth_at M Omega τ r φ.swapTemporal) ∧
      (∃ s, s < t ∧ truth_at M Omega τ s θ.swapTemporal ∧
        ∀ r, s < r → r < t → truth_at M Omega τ r χ.swapTemporal) := by
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
    simp only [Formula.swapTemporal, Formula.and, Formula.or, Formula.neg, truth_at]
    intro h_conj
    have h_both : (∃ s, t < s ∧ truth_at M Omega τ s ψ.swapTemporal ∧
        ∀ r, t < r → r < s → truth_at M Omega τ r φ.swapTemporal) ∧
      (∃ s, t < s ∧ truth_at M Omega τ s θ.swapTemporal ∧
        ∀ r, t < r → r < s → truth_at M Omega τ r χ.swapTemporal) := by
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
    simp only [Formula.swapTemporal, truth_at]
    intro ⟨s, hst, h_ψs, _⟩
    exact ⟨s, hst, h_ψs, fun _ _ _ hf => absurd hf not_false⟩
  | since_P φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, truth_at]
    intro ⟨s, hts, h_ψs, _⟩
    exact ⟨s, hts, h_ψs, fun _ _ _ hf => absurd hf not_false⟩
  | temp_linearity φ ψ =>
    -- swap of future linearity: use past linearity with swapped subformulas
    exact axiom_temp_linearity_past_valid φ.swapTemporal ψ.swapTemporal
  | temp_linearity_past φ ψ =>
    exact axiom_temp_linearity_valid φ.swapTemporal ψ.swapTemporal
  | F_until_equiv φ => exact axiom_P_since_equiv_valid φ.swapTemporal
  | P_since_equiv φ => exact axiom_F_until_equiv_valid φ.swapTemporal
  | modal_future ψ => exact swap_axiom_mf_valid ψ
  | discrete_symm_fwd =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swapTemporal, truth_at]
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
    simp only [Formula.swapTemporal, truth_at]
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
    unfold Formula.swapTemporal truth_at
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
    unfold Formula.swapTemporal truth_at
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
    simp only [Formula.swapTemporal, truth_at]
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

/-- Combined soundness for base derivations without frame-class constraints:
derivability implies both validity and swap-validity. Identical to
`derivable_valid_and_swap_valid` but without `[DenselyOrdered D] [Nontrivial D]`.

This is possible because the BX axiom system has no density or discreteness extension
axioms, so the proofs never actually use those constraints. -/
theorem derivable_valid_and_swap_valid_general [Nontrivial D]
    {φ : Formula Atom} (d : DerivationTree FrameClass.Base [] φ) :
    is_valid D φ ∧ is_valid D φ.swapTemporal := by
  match d with
  | .axiom _ _ h_ax h_fc =>
    exact ⟨axiom_locally_valid_general h_ax h_fc, axiom_swap_valid_general _ h_ax h_fc⟩
  | .assumption _ _ h_mem => exact absurd h_mem (Context.not_mem_nil _)
  | .modus_ponens _ ψ' _ d1 d2 =>
    obtain ⟨h1_valid, h1_swap⟩ := derivable_valid_and_swap_valid_general d1
    obtain ⟨h2_valid, h2_swap⟩ := derivable_valid_and_swap_valid_general d2
    exact ⟨mp_preserves_valid h1_valid h2_valid, mp_preserves_swap_valid ψ' _ h1_swap h2_swap⟩
  | .necessitation ψ' d' =>
    obtain ⟨h_valid, h_swap⟩ := derivable_valid_and_swap_valid_general d'
    exact ⟨necessitation_preserves_local_valid h_valid, modal_k_preserves_swap_valid ψ' h_swap⟩
  | .temporal_necessitation ψ' d' =>
    obtain ⟨h_valid, h_swap⟩ := derivable_valid_and_swap_valid_general d'
    exact ⟨temporal_necessitation_preserves_local_valid h_valid, temporal_k_preserves_swap_valid ψ' h_swap⟩
  | .temporal_duality ψ' d' =>
    obtain ⟨h_valid, h_swap⟩ := derivable_valid_and_swap_valid_general d'
    constructor
    · exact h_swap
    · simp only [Formula.swapTemporal_involution]; exact h_valid
  | .weakening Γ' _ _ d' h_sub =>
    have h_eq : Γ' = [] := List.eq_nil_of_subset_nil h_sub
    have h_height_eq : (h_eq ▸ d').height = d'.height := by subst h_eq; rfl
    have h_term : (h_eq ▸ d').height < (DerivationTree.weakening Γ' [] _ d' h_sub).height := by
      simp only [h_height_eq, DerivationTree.height]
      omega
    exact derivable_valid_and_swap_valid_general (h_eq ▸ d')
termination_by d.height
decreasing_by
  all_goals first
    | exact DerivationTree.mp_height_gt_left _ _
    | exact DerivationTree.mp_height_gt_right _ _
    | simp only [DerivationTree.height]; omega

/-- Derivability implies swap validity for base-compatible derivations.
This is the theorem needed for the temporal_duality case in base soundness. -/
theorem derivable_implies_swap_valid_general [Nontrivial D]
    {φ : Formula Atom} (d : DerivationTree FrameClass.Base [] φ) :
    is_valid D φ.swapTemporal :=
  (derivable_valid_and_swap_valid_general d).2

/-! ## Discrete Frame Versions

The following theorems provide validity and swap-validity for all axioms on discrete
frames. Prior-UZ/SZ have `minFrameClass = .Discrete` and are only valid on discrete orders,
so these theorems handle all axioms including Prior-UZ/SZ. The discrete frame class
constraint `h.minFrameClass ≤ .Discrete` structurally excludes the density axiom.
-/

/-- Prior-UZ is valid on discrete orders: F(φ) → U(φ, ¬φ).
The nearest future witness where φ holds satisfies Until with ¬φ as guard.
Uses Nat.find for well-founded descent on the succ chain. -/
theorem prior_UZ_is_valid
    [SuccOrder D] [PredOrder D] [IsSuccArchimedean D] [IsPredArchimedean D] [Nontrivial D]
    (φ : Formula Atom) : is_valid D (φ.someFuture.imp (Formula.untl φ φ.neg)) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.neg, truth_at]
  intro ⟨s, hts, hs, _⟩
  obtain ⟨n, hn⟩ := (Order.succ_le_of_lt hts).exists_succ_iterate
  have hn1 : Order.succ^[n + 1] t = s := by
    simp; exact hn
  classical
  have h_ex : ∃ k, truth_at M Omega τ (Order.succ^[k + 1] t) φ := ⟨n, hn1 ▸ hs⟩
  let k₀ := Nat.find h_ex
  have hk₀ : truth_at M Omega τ (Order.succ^[k₀ + 1] t) φ := Nat.find_spec h_ex
  have hk₀_min : ∀ m < k₀, ¬truth_at M Omega τ (Order.succ^[m + 1] t) φ :=
    fun m hm => Nat.find_min h_ex hm
  have h_iter_mono : Monotone (fun i => Order.succ^[i] t) :=
    Order.succ_mono.monotone_iterate_of_le_map (Order.le_succ t)
  have h_not_max : ¬IsMax t := hts.not_isMax
  refine ⟨Order.succ^[k₀ + 1] t, ?_, hk₀, ?_⟩
  · have h1 := h_iter_mono (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k₀))
    simp only at h1
    exact lt_of_lt_of_le (Order.lt_succ_of_not_isMax h_not_max) h1
  · intro r htr hrs
    obtain ⟨j, hj⟩ := (Order.succ_le_of_lt htr).exists_succ_iterate
    have hj1 : Order.succ^[j + 1] t = r := by
      simp; exact hj
    have hj_lt : j < k₀ := by
      by_contra h_ge
      push_neg at h_ge
      have h_le := h_iter_mono (show k₀ + 1 ≤ j + 1 by omega)
      simp only at h_le
      rw [hj1] at h_le
      exact absurd hrs (not_lt.mpr h_le)
    rw [← hj1]
    exact hk₀_min j hj_lt

/-- Prior-SZ is valid on discrete orders: P(φ) → S(φ, ¬φ).
Mirror of prior_UZ_is_valid using pred chain and IsPredArchimedean. -/
theorem prior_SZ_is_valid
    [SuccOrder D] [PredOrder D] [IsSuccArchimedean D] [IsPredArchimedean D] [Nontrivial D]
    (φ : Formula Atom) : is_valid D (φ.somePast.imp (Formula.snce φ φ.neg)) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.neg, truth_at]
  intro ⟨s, hst, hs, _⟩
  obtain ⟨n, hn⟩ := (Order.le_pred_of_lt hst).exists_pred_iterate
  have hn1 : Order.pred^[n + 1] t = s := by
    simp; exact hn
  classical
  have h_ex : ∃ k, truth_at M Omega τ (Order.pred^[k + 1] t) φ := ⟨n, hn1 ▸ hs⟩
  let k₀ := Nat.find h_ex
  have hk₀ : truth_at M Omega τ (Order.pred^[k₀ + 1] t) φ := Nat.find_spec h_ex
  have hk₀_min : ∀ m < k₀, ¬truth_at M Omega τ (Order.pred^[m + 1] t) φ :=
    fun m hm => Nat.find_min h_ex hm
  have h_iter_anti : Antitone (fun i => Order.pred^[i] t) :=
    Order.pred_mono.antitone_iterate_of_map_le (Order.pred_le t)
  have h_not_min : ¬IsMin t := hst.not_isMin
  refine ⟨Order.pred^[k₀ + 1] t, ?_, hk₀, ?_⟩
  · have h1 := h_iter_anti (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k₀))
    simp only at h1
    exact lt_of_le_of_lt h1 (Order.pred_lt_of_not_isMin h_not_min)
  · intro r hrs hrt
    obtain ⟨j, hj⟩ := (Order.le_pred_of_lt hrt).exists_pred_iterate
    have hj1 : Order.pred^[j + 1] t = r := by
      simp; exact hj
    have hj_lt : j < k₀ := by
      by_contra h_ge
      push_neg at h_ge
      have h_le := h_iter_anti (show k₀ + 1 ≤ j + 1 by omega)
      simp only at h_le
      rw [hj1] at h_le
      exact absurd hrs (not_lt.mpr h_le)
    rw [← hj1]
    exact hk₀_min j hj_lt

/-- Z1 is valid on discrete orders: G(Gφ→φ) → (FGφ→Gφ).
Backward induction from the Gφ witness using IsSuccArchimedean. -/
theorem z1_is_valid
    [SuccOrder D] [PredOrder D] [IsSuccArchimedean D] [IsPredArchimedean D] [Nontrivial D]
    (φ : Formula Atom) : is_valid D ((φ.allFuture.imp φ).allFuture.imp
        (φ.allFuture.someFuture.imp φ.allFuture)) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.neg, truth_at]
  intro h_GGpIp ⟨s₀, hts₀, hs₀, _⟩
  -- Extract: h_GGpIp encodes G(Gφ→φ), hs₀ encodes Gφ(s₀)
  -- h_GGpIp : (∃ s > t, ((Gφ(s) → φ(s)) → ⊥) ∧ guard) → ⊥
  -- hs₀ : (∃ s > s₀, (φ(s) → ⊥) ∧ guard) → ⊥
  -- Helper to extract Gφ→φ at any s > t from h_GGpIp
  have h_GGpIp_at : ∀ s, t < s →
      ((∃ r, s < r ∧ (truth_at M Omega τ r φ → False) ∧
        ∀ q, s < q → q < r → False → False) → False) →
      truth_at M Omega τ s φ := by
    intro s hts h_Gφs
    by_contra h_neg
    apply h_GGpIp
    exact ⟨s, hts, fun h_imp => h_neg (h_imp h_Gφs), fun _ _ _ hf => absurd hf not_false⟩
  obtain ⟨n₀, hn₀⟩ := (Order.succ_le_of_lt hts₀).exists_succ_iterate
  have hn₀_eq : Order.succ^[n₀ + 1] t = s₀ := by
    show Order.succ^[n₀] (Order.succ t) = s₀; exact hn₀
  have h_iter_mono : Monotone (fun i => Order.succ^[i] t) :=
    Order.succ_mono.monotone_iterate_of_le_map (Order.le_succ t)
  have h_not_max : ¬IsMax t := hts₀.not_isMax
  have h_above_s0 : ∀ s, s₀ ≤ s → truth_at M Omega τ s φ := by
    intro s hs
    rcases eq_or_lt_of_le hs with rfl | hlt
    · exact h_GGpIp_at s₀ hts₀ hs₀
    · exact by by_contra h_neg; apply hs₀; exact ⟨s, hlt, h_neg, fun _ _ _ hf => absurd hf not_false⟩
  have h_all_iterates : ∀ k, truth_at M Omega τ (Order.succ^[k + 1] t) φ := by
    suffices h_le : ∀ k, k ≤ n₀ → truth_at M Omega τ (Order.succ^[k + 1] t) φ by
      intro k
      by_cases hk : k ≤ n₀
      · exact h_le k hk
      · exact h_above_s0 _ (hn₀_eq ▸ h_iter_mono (by omega : n₀ + 1 ≤ k + 1))
    have : ∀ d, d ≤ n₀ → ∀ k, n₀ - k = d → k ≤ n₀ →
        truth_at M Omega τ (Order.succ^[k + 1] t) φ := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro hd k hk hkn
        have h_lt_t : t < Order.succ^[k + 1] t :=
          lt_of_lt_of_le (Order.lt_succ_of_not_isMax h_not_max)
            (h_iter_mono (by omega : 1 ≤ k + 1))
        apply h_GGpIp_at _ h_lt_t
        -- Need: Gφ at succ^[k+1](t), i.e. ¬∃ r > succ^[k+1](t), ¬φ(r)
        intro ⟨r, hr, h_neg_φr, _⟩
        obtain ⟨j, hj⟩ := (Order.succ_le_of_lt hr).exists_succ_iterate
        have hj_eq : Order.succ^[j + 1] (Order.succ^[k + 1] t) = r := by
          show Order.succ^[j] (Order.succ (Order.succ^[k + 1] t)) = r; exact hj
        rw [← hj_eq, ← Function.iterate_add_apply,
            show j + 1 + (k + 1) = (k + j + 1) + 1 from by omega] at h_neg_φr
        by_cases h_le : k + j + 1 ≤ n₀
        · exact h_neg_φr (ih (n₀ - (k + j + 1)) (by omega) (by omega) (k + j + 1) rfl h_le)
        · exact h_neg_φr (h_above_s0 _ (hn₀_eq ▸ h_iter_mono (by omega : n₀ + 1 ≤ (k + j + 1) + 1)))
    intro k hk
    exact this (n₀ - k) (by omega) k rfl hk
  intro ⟨s, hts, h_neg_φs, _⟩
  obtain ⟨m, hm⟩ := (Order.succ_le_of_lt hts).exists_succ_iterate
  have hm_eq : Order.succ^[m + 1] t = s := by change Order.succ^[m] (Order.succ t) = s; exact hm
  exact h_neg_φs (hm_eq ▸ h_all_iterates m)

/-- Z1 past dual is valid on discrete orders: H(Hφ→φ) → (PHφ→Hφ).
Backward induction using IsPredArchimedean. -/
theorem z1_past_is_valid
    [SuccOrder D] [PredOrder D] [IsSuccArchimedean D] [IsPredArchimedean D] [Nontrivial D]
    (φ : Formula Atom) : is_valid D ((φ.allPast.imp φ).allPast.imp
        (φ.allPast.somePast.imp φ.allPast)) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.neg, truth_at]
  intro h_HHpIp ⟨s₀, hs₀t, hs₀, _⟩
  -- h_HHpIp encodes H(Hφ→φ), hs₀ encodes Hφ(s₀)
  -- Helper to extract Hφ→φ at any s < t
  have h_HHpIp_at : ∀ s, s < t →
      ((∃ r, r < s ∧ (truth_at M Omega τ r φ → False) ∧
        ∀ q, r < q → q < s → False → False) → False) →
      truth_at M Omega τ s φ := by
    intro s hst h_Hφs
    by_contra h_neg
    apply h_HHpIp
    exact ⟨s, hst, fun h_imp => h_neg (h_imp h_Hφs), fun _ _ _ hf => absurd hf not_false⟩
  obtain ⟨n₀, hn₀⟩ := (Order.le_pred_of_lt hs₀t).exists_pred_iterate
  have hn₀_eq : Order.pred^[n₀ + 1] t = s₀ := by
    show Order.pred^[n₀] (Order.pred t) = s₀; exact hn₀
  have h_iter_anti : Antitone (fun i => Order.pred^[i] t) :=
    Order.pred_mono.antitone_iterate_of_map_le (Order.pred_le t)
  have h_not_min : ¬IsMin t := hs₀t.not_isMin
  have h_below_s0 : ∀ u, u ≤ s₀ → truth_at M Omega τ u φ := by
    intro u hu
    rcases eq_or_lt_of_le hu with rfl | hlt
    · exact h_HHpIp_at _ hs₀t hs₀
    · exact by by_contra h_neg; apply hs₀; exact ⟨u, hlt, h_neg, fun _ _ _ hf => absurd hf not_false⟩
  have h_all_iterates : ∀ k, truth_at M Omega τ (Order.pred^[k + 1] t) φ := by
    suffices h_le : ∀ k, k ≤ n₀ → truth_at M Omega τ (Order.pred^[k + 1] t) φ by
      intro k
      by_cases hk : k ≤ n₀
      · exact h_le k hk
      · exact h_below_s0 _ (hn₀_eq ▸ h_iter_anti (by omega : n₀ + 1 ≤ k + 1))
    have : ∀ d, d ≤ n₀ → ∀ k, n₀ - k = d → k ≤ n₀ →
        truth_at M Omega τ (Order.pred^[k + 1] t) φ := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro hd k hk hkn
        have h_lt_t : Order.pred^[k + 1] t < t :=
          lt_of_le_of_lt (h_iter_anti (by omega : 1 ≤ k + 1))
            (Order.pred_lt_of_not_isMin h_not_min)
        apply h_HHpIp_at _ h_lt_t
        -- Need: Hφ at pred^[k+1](t), i.e. ¬∃ r < pred^[k+1](t), ¬φ(r)
        intro ⟨r, hr, h_neg_φr, _⟩
        obtain ⟨j, hj⟩ := (Order.le_pred_of_lt hr).exists_pred_iterate
        have hj_eq : Order.pred^[j + 1] (Order.pred^[k + 1] t) = r := by
          show Order.pred^[j] (Order.pred (Order.pred^[k + 1] t)) = r; exact hj
        rw [← hj_eq, ← Function.iterate_add_apply,
            show j + 1 + (k + 1) = (k + j + 1) + 1 from by omega] at h_neg_φr
        by_cases h_le : k + j + 1 ≤ n₀
        · exact h_neg_φr (ih (n₀ - (k + j + 1)) (by omega) (by omega) (k + j + 1) rfl h_le)
        · exact h_neg_φr (h_below_s0 _ (hn₀_eq ▸ h_iter_anti (by omega : n₀ + 1 ≤ (k + j + 1) + 1)))
    intro k hk
    exact this (n₀ - k) (by omega) k rfl hk
  intro ⟨s, hst, h_neg_φs, _⟩
  obtain ⟨m, hm⟩ := (Order.le_pred_of_lt hst).exists_pred_iterate
  have hm_eq : Order.pred^[m + 1] t = s := by change Order.pred^[m] (Order.pred t) = s; exact hm
  exact h_neg_φs (hm_eq ▸ h_all_iterates m)

/-- All axiom swaps are valid on discrete orders. For base-compatible axioms,
delegates to `axiom_swap_valid_general`. For Prior-UZ/SZ, proves directly. -/
private theorem axiom_swap_valid_discrete
    [SuccOrder D] [PredOrder D] [IsSuccArchimedean D] [IsPredArchimedean D] [Nontrivial D]
    (φ : Formula Atom) (h : Axiom φ) (h_fc : h.minFrameClass ≤ FrameClass.Discrete) :
    is_valid D φ.swapTemporal := by
  by_cases hbase : h.minFrameClass ≤ FrameClass.Base
  · exact axiom_swap_valid_general _ h hbase
  · cases h with
    | prior_UZ φ =>
      change is_valid D (φ.swapTemporal.somePast.imp (φ.swapTemporal.snce φ.swapTemporal.neg))
      exact prior_SZ_is_valid φ.swapTemporal
    | prior_SZ φ =>
      change is_valid D (φ.swapTemporal.someFuture.imp (φ.swapTemporal.untl φ.swapTemporal.neg))
      exact prior_UZ_is_valid φ.swapTemporal
    | z1 φ =>
      change is_valid D ((φ.swapTemporal.allPast.imp φ.swapTemporal).allPast.imp
        (φ.swapTemporal.allPast.somePast.imp φ.swapTemporal.allPast))
      exact z1_past_is_valid φ.swapTemporal
    | density _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
    | dense_indicator => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
    | _ => exact absurd trivial hbase

/-- All discrete-compatible axioms are locally valid on discrete orders. For base axioms,
delegates to `axiom_locally_valid_general`. For others, proves directly. -/
private theorem axiom_locally_valid_discrete
    [SuccOrder D] [PredOrder D] [IsSuccArchimedean D] [IsPredArchimedean D] [Nontrivial D]
    {φ : Formula Atom} (h : Axiom φ) (h_fc : h.minFrameClass ≤ FrameClass.Discrete) :
    is_valid D φ := by
  by_cases hbase : h.minFrameClass ≤ FrameClass.Base
  · exact axiom_locally_valid_general h hbase
  · cases h with
    | prior_UZ φ => exact prior_UZ_is_valid φ
    | prior_SZ φ => exact prior_SZ_is_valid φ
    | z1 φ => exact z1_is_valid φ
    | density _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
    | dense_indicator => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
    | _ => exact absurd trivial hbase

/-- Combined soundness on discrete frames: derivability implies both validity
and swap-validity on discrete orders. -/
theorem derivable_valid_and_swap_valid_discrete
    [SuccOrder D] [PredOrder D] [IsSuccArchimedean D] [IsPredArchimedean D] [Nontrivial D]
    {φ : Formula Atom} (d : DerivationTree FrameClass.Discrete [] φ) :
    is_valid D φ ∧ is_valid D φ.swapTemporal := by
  match d with
  | .axiom _ _ h_ax h_fc =>
    exact ⟨axiom_locally_valid_discrete h_ax h_fc, axiom_swap_valid_discrete _ h_ax h_fc⟩
  | .assumption _ _ h_mem => exact absurd h_mem (Context.not_mem_nil _)
  | .modus_ponens _ ψ' _ d1 d2 =>
    obtain ⟨h1_valid, h1_swap⟩ := derivable_valid_and_swap_valid_discrete d1
    obtain ⟨h2_valid, h2_swap⟩ := derivable_valid_and_swap_valid_discrete d2
    exact ⟨mp_preserves_valid h1_valid h2_valid, mp_preserves_swap_valid ψ' _ h1_swap h2_swap⟩
  | .necessitation ψ' d' =>
    obtain ⟨h_valid, h_swap⟩ := derivable_valid_and_swap_valid_discrete d'
    exact ⟨necessitation_preserves_local_valid h_valid, modal_k_preserves_swap_valid ψ' h_swap⟩
  | .temporal_necessitation ψ' d' =>
    obtain ⟨h_valid, h_swap⟩ := derivable_valid_and_swap_valid_discrete d'
    exact ⟨temporal_necessitation_preserves_local_valid h_valid, temporal_k_preserves_swap_valid ψ' h_swap⟩
  | .temporal_duality ψ' d' =>
    obtain ⟨h_valid, h_swap⟩ := derivable_valid_and_swap_valid_discrete d'
    constructor
    · exact h_swap
    · simp only [Formula.swapTemporal_involution]; exact h_valid
  | .weakening Γ' _ _ d' h_sub =>
    have h_eq : Γ' = [] := List.eq_nil_of_subset_nil h_sub
    have h_height_eq : (h_eq ▸ d').height = d'.height := by subst h_eq; rfl
    have h_term : (h_eq ▸ d').height < (DerivationTree.weakening Γ' [] _ d' h_sub).height := by
      simp only [h_height_eq, DerivationTree.height]
      omega
    exact derivable_valid_and_swap_valid_discrete (h_eq ▸ d')
termination_by d.height
decreasing_by
  all_goals first
    | exact DerivationTree.mp_height_gt_left _ _
    | exact DerivationTree.mp_height_gt_right _ _
    | simp only [DerivationTree.height]; omega

/-- Derivability implies swap validity on discrete frames.
Used in soundness_discrete_valid and soundness_discrete temporal_duality cases. -/
theorem derivable_implies_swap_valid_discrete
    [SuccOrder D] [PredOrder D] [IsSuccArchimedean D] [IsPredArchimedean D] [Nontrivial D]
    {φ : Formula Atom} (d : DerivationTree FrameClass.Discrete [] φ) :
    is_valid D φ.swapTemporal :=
  (derivable_valid_and_swap_valid_discrete d).2

end Cslib.Logic.Bimodal.Metalogic.SoundnessLemmas
