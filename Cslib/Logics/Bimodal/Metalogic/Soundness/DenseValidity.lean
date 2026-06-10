/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/
import Cslib.Logics.Bimodal.Metalogic.Soundness.Core

/-!
# Axiom and Rule Validity for the Dense Frame Class

Swap validity, local validity, and combined soundness theorems for the dense frame
class. Proves that all TM axioms remain valid after temporal swap, and that derivability
implies both local validity and swap validity.
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace Cslib.Logic.Bimodal.Metalogic.SoundnessLemmas

open Cslib.Logic.Bimodal

variable {Atom : Type*}
variable {D : Type} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

/-! ## Axiom Swap Validity

This section proves validity of swapped axioms to enable temporal duality soundness
via derivation induction instead of formula induction.
-/

/-- Modal T axiom (MT) swap validity. -/
theorem swap_axiom_mt_valid (φ : Formula Atom) :
    is_valid D ((Formula.box φ).imp φ).swap_temporal := by
  intro ℱ M Omega _h_sc τ h_mem t
  simp only [Formula.swap_temporal, truth_at]
  intro h_box_swap_φ
  exact h_box_swap_φ τ h_mem

/-- Modal 4 axiom (M4) swap validity. -/
theorem swap_axiom_m4_valid (φ : Formula Atom) :
    is_valid D ((Formula.box φ).imp (Formula.box (Formula.box φ))).swap_temporal := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.swap_temporal, truth_at]
  intro h_box_swap_φ σ h_σ_mem ρ h_ρ_mem
  exact h_box_swap_φ ρ h_ρ_mem

/-- Modal B axiom (MB) swap validity. -/
theorem swap_axiom_mb_valid (φ : Formula Atom) :
    is_valid D (φ.imp (Formula.box φ.diamond)).swap_temporal := by
  intro ℱ M Omega _h_sc τ h_mem t
  simp only [Formula.swap_temporal, Formula.diamond, Formula.neg]
  simp only [truth_at]
  intro h_swap_φ σ _h_σ_mem h_all_not
  exact h_all_not τ h_mem h_swap_φ

/-- Temporal 4 axiom (T4) swap validity: `Gφ → GGφ` swaps to `Hφ' → HHφ'`. -/
theorem swap_axiom_t4_valid (φ : Formula Atom) :
    is_valid D
      ((Formula.all_future φ).imp
       (Formula.all_future (Formula.all_future φ))).swap_temporal := by
  intro ℱ M Omega _h_sc τ _h_mem t
  unfold Formula.swap_temporal truth_at
  intro h_Hφ ⟨s, hst, h_neg_Hφ_s, _⟩
  apply h_neg_Hφ_s
  intro ⟨u, hus, h_neg_φ_u, _⟩
  apply h_Hφ
  exact ⟨u, lt_trans hus hst, h_neg_φ_u, fun _ _ _ h => h⟩

/-- Temporal A axiom (TA) swap validity: `φ → G(Pφ)` swaps to `φ' → H(Fφ')`. -/
theorem swap_axiom_ta_valid (φ : Formula Atom) :
    is_valid D (φ.imp (Formula.all_future φ.some_past)).swap_temporal := by
  intro ℱ M Omega _h_sc τ _h_mem t
  unfold Formula.swap_temporal truth_at
  intro h_swap_φ ⟨s, hst, h_neg, _⟩
  apply h_neg
  exact ⟨t, hst, h_swap_φ, fun _ _ _ h => h⟩

/-- Temporal L axiom (TL) swap validity: `always φ → G(Hφ)` swaps to valid form. -/
theorem swap_axiom_tl_valid (φ : Formula Atom) :
    is_valid D (φ.always.imp (Formula.all_future (Formula.all_past φ))).swap_temporal := by
  intro ℱ M Omega _h_sc τ _h_mem t
  unfold Formula.swap_temporal truth_at
  simp only [Formula.always, Formula.and, Formula.swap_temporal, Formula.neg, truth_at]
  intro h_always ⟨s, hst, h_neg_Gφ_s, _⟩
  -- Extract the three components from h_always (double-negation encoding)
  -- h_always : ((Gφ' → (φ'(t) → Hφ' → ⊥) → ⊥) → ⊥)
  -- In unfolded form: Gφ' = (∃ s > t, ¬φ'(s) ∧ ...) → ⊥, etc.
  have h_future : ∀ r, t < r → truth_at M Omega τ r φ.swap_temporal := by
    by_contra h_not; push_neg at h_not
    obtain ⟨r, htr, h_neg⟩ := h_not
    exact h_always fun h_G _ => h_G ⟨r, htr, h_neg, fun _ _ _ hf => absurd hf not_false⟩
  have h_present : truth_at M Omega τ t φ.swap_temporal := by
    by_contra h_not
    exact h_always fun _ h_inner => h_inner (fun h_pres _ => h_not h_pres)
  have h_past : ∀ r, r < t → truth_at M Omega τ r φ.swap_temporal := by
    by_contra h_not; push_neg at h_not
    obtain ⟨r, hrt, h_neg⟩ := h_not
    exact h_always fun _ h_inner => h_inner (fun _ h_H => h_H ⟨r, hrt, h_neg, fun _ _ _ hf => absurd hf not_false⟩)
  apply h_neg_Gφ_s
  intro ⟨u, hus, h_neg_φ_u, _⟩
  rcases lt_trichotomy u t with h_lt | h_eq | h_gt
  · exact h_neg_φ_u (h_past u h_lt)
  · exact h_neg_φ_u (h_eq ▸ h_present)
  · exact h_neg_φ_u (h_future u h_gt)

/-- Swap of F_until_equiv: `F(φ) → ⊤ U φ` swaps to `P(φ') → ⊤ S φ'`. -/
theorem swap_axiom_F_until_equiv_valid (φ : Formula Atom) :
    is_valid D ((Formula.some_future φ).imp
      (Formula.untl φ (Formula.bot.imp Formula.bot))).swap_temporal := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.swap_temporal, truth_at, Formula.some_past, Formula.some_future,
    Formula.neg, Formula.imp, Formula.untl, Formula.snce]
  intro ⟨s, hst, h_φs, _⟩
  exact ⟨s, hst, h_φs, fun _ _ _ hf => absurd hf not_false⟩

/-- Swap of P_since_equiv: `P(φ) → ⊤ S φ` swaps to `F(φ') → ⊤ U φ'`. -/
theorem swap_axiom_P_since_equiv_valid (φ : Formula Atom) :
    is_valid D ((Formula.some_past φ).imp
      (Formula.snce φ (Formula.bot.imp Formula.bot))).swap_temporal := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.swap_temporal, truth_at, Formula.some_past, Formula.some_future,
    Formula.neg, Formula.imp, Formula.untl, Formula.snce]
  intro ⟨s, hts, h_φs, _⟩
  exact ⟨s, hts, h_φs, fun _ _ _ hf => absurd hf not_false⟩

/-- Modal-Future axiom (MF) swap validity: `□φ → □Gφ` swaps to `□φ' → □Hφ'`. -/
theorem swap_axiom_mf_valid (φ : Formula Atom) :
    is_valid D ((Formula.box φ).imp (Formula.box (Formula.all_future φ))).swap_temporal := by
  intro ℱ M Omega h_sc τ _h_mem t
  unfold Formula.swap_temporal truth_at
  intro h_box_swap σ h_σ_mem ⟨s, hst, h_neg_φ_s, _⟩
  have h_at_shifted := h_box_swap (WorldHistory.time_shift σ (s - t)) (h_sc σ h_σ_mem (s - t))
  exact h_neg_φ_s ((TimeShift.time_shift_preserves_truth M Omega h_sc σ t s φ.swap_temporal).mp h_at_shifted)

/-! ## Rule Preservation -/

/-- Modus ponens preserves swap validity. -/
theorem mp_preserves_swap_valid (φ ψ : Formula Atom)
    (h_imp : is_valid D (φ.imp ψ).swap_temporal)
    (h_phi : is_valid D φ.swap_temporal) :
    is_valid D ψ.swap_temporal := by
  intro ℱ M Omega h_sc τ h_mem t
  simp only [Formula.swap_temporal] at h_imp h_phi ⊢
  exact h_imp ℱ M Omega h_sc τ h_mem t (h_phi ℱ M Omega h_sc τ h_mem t)

/-- Modal K rule preserves swap validity. -/
theorem modal_k_preserves_swap_valid (φ : Formula Atom)
    (h : is_valid D φ.swap_temporal) :
    is_valid D (Formula.box φ).swap_temporal := by
  intro ℱ M Omega h_sc τ _h_mem t
  simp only [Formula.swap_temporal, truth_at]
  intro σ h_σ_mem
  exact h ℱ M Omega h_sc σ h_σ_mem t

/-- Temporal K rule preserves swap validity: `Gφ.swap = Hφ.swap`. -/
theorem temporal_k_preserves_swap_valid (φ : Formula Atom)
    (h : is_valid D φ.swap_temporal) :
    is_valid D (Formula.all_future φ).swap_temporal := by
  intro ℱ M Omega h_sc τ h_mem t
  unfold Formula.swap_temporal truth_at
  intro ⟨s, hst, h_neg, _⟩
  exact h_neg (h ℱ M Omega h_sc τ h_mem s)

/-- Helper: extract conjunction from double-negation-of-implication encoding. -/
private theorem and_extract {p q : Prop} (h : (p → q → False) → False) : p ∧ q :=
  ⟨Classical.byContradiction (fun hp => h (fun a _ => hp a)),
   Classical.byContradiction (fun hq => h (fun _ b => hq b))⟩

/-! ## Axiom Swap Validity Master Theorem

Combines all individual axiom swap validity lemmas.
-/

theorem axiom_swap_valid (φ : Formula Atom) (h : Axiom φ) [DenselyOrdered D] [Nontrivial D]
    (h_fc : h.minFrameClass ≤ FrameClass.Dense) : is_valid D φ.swap_temporal := by
  cases h with
  | imp_k ψ χ ρ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro h_abc h_ab h_a
    exact h_abc h_a (h_ab h_a)
  | imp_s ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro h_a _
    exact h_a
  | modal_t ψ => exact swap_axiom_mt_valid ψ
  | modal_4 ψ => exact swap_axiom_m4_valid ψ
  | modal_b ψ => exact swap_axiom_mb_valid ψ
  | modal_5_collapse ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.diamond, Formula.neg]
    simp only [truth_at]
    intro h_diamond_box σ h_σ_mem
    by_contra h_not_psi
    apply h_diamond_box
    intro ρ h_ρ_mem h_box_at_rho
    have h_psi_at_sigma := h_box_at_rho σ h_σ_mem
    exact h_not_psi h_psi_at_sigma
  | efq ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro h_bot
    exfalso
    exact h_bot
  | peirce ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro h_peirce
    by_cases h : truth_at M Omega τ t ψ.swap_temporal
    · exact h
    · have h_imp : truth_at M Omega τ t (ψ.swap_temporal.imp χ.swap_temporal) := by
        unfold truth_at
        intro h_psi
        exfalso
        exact h h_psi
      exact h_peirce h_imp
  | modal_k_dist ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro h_box_imp h_box_psi σ h_σ_mem
    exact h_box_imp σ h_σ_mem (h_box_psi σ h_σ_mem)
  | serial_future =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro _
    obtain ⟨s, hst⟩ := exists_lt t
    exact ⟨s, hst, fun h => h, fun _ _ _ hf => absurd hf not_false⟩
  | serial_past =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro _
    obtain ⟨s, hts⟩ := exists_gt t
    exact ⟨s, hts, fun h => h, fun _ _ _ hf => absurd hf not_false⟩
  | left_mono_until_G φ χ ψ =>
    -- Swap: H(φ'→χ') → snce(φ',ψ') → snce(χ',ψ')
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro h_H ⟨s, hst, h_ψs, h_guard⟩
    refine ⟨s, hst, h_ψs, fun r hsr hrt => ?_⟩
    -- Need to apply H at r (which is between s and t)
    have h_imp_r : truth_at M Omega τ r φ.swap_temporal → truth_at M Omega τ r χ.swap_temporal := by
      intro h_φr
      by_contra h_neg
      apply h_H
      exact ⟨r, hrt, fun h_imp => h_neg (h_imp h_φr), fun _ _ _ hf => absurd hf not_false⟩
    exact h_imp_r (h_guard r hsr hrt)
  | left_mono_since_H φ χ ψ =>
    -- Swap: G(φ'→χ') → untl(φ',ψ') → untl(χ',ψ')
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro h_G ⟨s, hts, h_ψs, h_guard⟩
    refine ⟨s, hts, h_ψs, fun r htr hrs => ?_⟩
    have h_imp_r : truth_at M Omega τ r φ.swap_temporal → truth_at M Omega τ r χ.swap_temporal := by
      intro h_φr
      by_contra h_neg
      apply h_G
      exact ⟨r, htr, fun h_imp => h_neg (h_imp h_φr), fun _ _ _ hf => absurd hf not_false⟩
    exact h_imp_r (h_guard r htr hrs)
  | right_mono_until φ ψ χ =>
    -- swap: H(φ'→ψ') → (φ' S χ') → (ψ' S χ')
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro h_H ⟨s, hst, h_φs, h_guard⟩
    have h_ψs : truth_at M Omega τ s ψ.swap_temporal := by
      by_contra h_neg
      apply h_H
      exact ⟨s, hst, fun h_imp => h_neg (h_imp h_φs), fun _ _ _ hf => absurd hf not_false⟩
    exact ⟨s, hst, h_ψs, h_guard⟩
  | right_mono_since φ ψ χ =>
    -- swap: G(φ'→ψ') → (φ' U χ') → (ψ' U χ')
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro h_G ⟨s, hts, h_φs, h_guard⟩
    have h_ψs : truth_at M Omega τ s ψ.swap_temporal := by
      by_contra h_neg
      apply h_G
      exact ⟨s, hts, fun h_imp => h_neg (h_imp h_φs), fun _ _ _ hf => absurd hf not_false⟩
    exact ⟨s, hts, h_ψs, h_guard⟩
  | connect_future φ =>
    -- Swap: φ → G(Pφ) swaps to φ' → H(Fφ')
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro h_φt ⟨s, hst, h_neg, _⟩
    apply h_neg
    exact ⟨t, hst, h_φt, fun _ _ _ hf => absurd hf not_false⟩
  | connect_past φ =>
    -- Swap: φ → H(Fφ) swaps to φ' → G(Pφ')
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro h_φt ⟨s, hts, h_neg, _⟩
    apply h_neg
    exact ⟨t, hts, h_φt, fun _ _ _ hf => absurd hf not_false⟩
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
    intro h_imp
    exact h_imp h_ψs ⟨t, hst, h_pt, fun r hsr hrt => h_guard r hsr hrt⟩
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
    intro h_imp
    exact h_imp h_ψs ⟨t, hts, h_pt, fun r htr hrs => h_guard r htr hrs⟩
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
    have h_φs₁_and_since : truth_at M Omega τ s₁ φ.swap_temporal ∧
        (∃ s₂, s₂ < s₁ ∧ truth_at M Omega τ s₂ ψ.swap_temporal ∧
          ∀ q, s₂ < q → q < s₁ → truth_at M Omega τ q φ.swap_temporal) := by
      constructor
      · by_contra h_neg; exact h_conj (fun h_φ _ => h_neg h_φ)
      · by_contra h_neg; exact h_conj (fun _ h_since => h_neg h_since)
    obtain ⟨h_φs₁, s₂, hs₂s₁, h_ψs₂, h_guard₂⟩ := h_φs₁_and_since
    refine ⟨s₂, lt_trans hs₂s₁ hs₁t, h_ψs₂, fun q hs₂q hqt => ?_⟩
    rcases lt_trichotomy q s₁ with h_lt | h_eq | h_gt
    · exact h_guard₂ q hs₂q h_lt
    · exact h_eq ▸ h_φs₁
    · exact h_guard₁ q h_gt hqt
  | absorb_since φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.and, Formula.neg, truth_at]
    intro ⟨s₁, hts₁, h_conj, h_guard₁⟩
    have h_φs₁_and_until : truth_at M Omega τ s₁ φ.swap_temporal ∧
        (∃ s₂, s₁ < s₂ ∧ truth_at M Omega τ s₂ ψ.swap_temporal ∧
          ∀ q, s₁ < q → q < s₂ → truth_at M Omega τ q φ.swap_temporal) := by
      constructor
      · by_contra h_neg; exact h_conj (fun h_φ _ => h_neg h_φ)
      · by_contra h_neg; exact h_conj (fun _ h_until => h_neg h_until)
    obtain ⟨h_φs₁, s₂, hs₁s₂, h_ψs₂, h_guard₂⟩ := h_φs₁_and_until
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
    · -- s₁ < s₂ < t: third disjunct
      intro _
      refine ⟨s₂, hs₂t, ?_, fun r hs₂r hrt h_imp => ?_⟩
      · intro h_neg; exact h_neg (h_guard₁ s₂ h_lt hs₂t) h_θs₂
      · exact h_imp (h_guard₁ r (lt_trans h_lt hs₂r) hrt) (h_guard₂ r hs₂r hrt)
    · -- s₁ = s₂: first disjunct
      intro h_outer; exfalso; apply h_outer; intro h_inner; exfalso; apply h_inner
      refine ⟨s₁, hs₁t, ?_, fun r hs₁r hrt h_imp => ?_⟩
      · intro h_neg; exact h_neg h_ψs₁ (h_eq ▸ h_θs₂)
      · exact h_imp (h_guard₁ r hs₁r hrt) (h_guard₂ r (h_eq ▸ hs₁r) hrt)
    · -- s₂ < s₁ < t: second disjunct
      intro h_neg; exfalso; apply h_neg; intro _
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
    · -- s₁ < s₂: second disjunct
      intro h_neg; exfalso; apply h_neg; intro _
      refine ⟨s₁, hts₁, ?_, fun r htr hrs h_imp => ?_⟩
      · intro h_neg; exact h_neg h_ψs₁ (h_guard₂ s₁ hts₁ h_lt)
      · exact h_imp (h_guard₁ r htr hrs) (h_guard₂ r htr (lt_trans hrs h_lt))
    · -- s₁ = s₂: first disjunct
      intro h_outer; exfalso; apply h_outer; intro h_inner; exfalso; apply h_inner
      refine ⟨s₁, hts₁, ?_, fun r htr hrs h_imp => ?_⟩
      · intro h_neg; exact h_neg h_ψs₁ (h_eq ▸ h_θs₂)
      · exact h_imp (h_guard₁ r htr hrs) (h_guard₂ r htr (h_eq ▸ hrs))
    · -- s₂ < s₁: third disjunct
      intro _
      refine ⟨s₂, hts₂, ?_, fun r htr hrs h_imp => ?_⟩
      · intro h_neg; exact h_neg (h_guard₁ s₂ hts₂ h_gt) h_θs₂
      · exact h_imp (h_guard₁ r htr (lt_trans hrs h_gt)) (h_guard₂ r htr hrs)
  | until_F φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro ⟨s, hst, h_ψs, _h_guard⟩
    exact ⟨s, hst, h_ψs, fun _ _ _ hf => absurd hf not_false⟩
  | since_P φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro ⟨s, hts, h_ψs, _h_guard⟩
    exact ⟨s, hts, h_ψs, fun _ _ _ hf => absurd hf not_false⟩
  | temp_linearity φ ψ =>
    -- swap of future linearity is past linearity with swapped subformulas
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.and, Formula.or, Formula.neg, truth_at]
    intro h_conj
    have ⟨s1, hs1t, h_φs1⟩ : ∃ s, s < t ∧ truth_at M Omega τ s φ.swap_temporal := by
      by_contra h_no; push_neg at h_no
      exact h_conj (fun ⟨s, hst, h_phi, _⟩ _ => absurd h_phi (h_no s hst))
    have ⟨s2, hs2t, h_ψs2⟩ : ∃ s, s < t ∧ truth_at M Omega τ s ψ.swap_temporal := by
      by_contra h_no; push_neg at h_no
      exact h_conj (fun _ ⟨s, hst, h_psi, _⟩ => absurd h_psi (h_no s hst))
    rcases lt_trichotomy s1 s2 with h_lt | h_eq | h_gt
    · -- s1 < s2: P(P(φ') ∧ ψ')
      intro _; intro _
      exact ⟨s2, hs2t, fun h_imp => h_imp ⟨s1, h_lt, h_φs1, fun _ _ _ hf => absurd hf not_false⟩ h_ψs2, fun _ _ _ hf => absurd hf not_false⟩
    · -- s1 = s2: P(φ' ∧ ψ')
      subst h_eq
      intro h_neg_first; exfalso; apply h_neg_first
      exact ⟨s1, hs1t, fun h_imp => h_imp h_φs1 h_ψs2, fun _ _ _ hf => absurd hf not_false⟩
    · -- s2 < s1: P(φ' ∧ P(ψ'))
      intro _; intro h_neg_second; exfalso; apply h_neg_second
      exact ⟨s1, hs1t, fun h_imp => h_imp h_φs1 ⟨s2, h_gt, h_ψs2, fun _ _ _ hf => absurd hf not_false⟩, fun _ _ _ hf => absurd hf not_false⟩
  | temp_linearity_past φ ψ =>
    -- swap of past linearity is future linearity with swapped subformulas
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.and, Formula.or, Formula.neg, truth_at]
    intro h_conj
    have ⟨s1, hts1, h_φs1⟩ : ∃ s, t < s ∧ truth_at M Omega τ s φ.swap_temporal := by
      by_contra h_no; push_neg at h_no
      exact h_conj (fun ⟨s, hts, h_phi, _⟩ _ => absurd h_phi (h_no s hts))
    have ⟨s2, hts2, h_ψs2⟩ : ∃ s, t < s ∧ truth_at M Omega τ s ψ.swap_temporal := by
      by_contra h_no; push_neg at h_no
      exact h_conj (fun _ ⟨s, hts, h_psi, _⟩ => absurd h_psi (h_no s hts))
    rcases lt_trichotomy s1 s2 with h_lt | h_eq | h_gt
    · -- s1 < s2: F(φ' ∧ F(ψ'))
      intro _; intro h_neg_second; exfalso; apply h_neg_second
      exact ⟨s1, hts1, fun h_imp => h_imp h_φs1 ⟨s2, h_lt, h_ψs2, fun _ _ _ hf => absurd hf not_false⟩, fun _ _ _ hf => absurd hf not_false⟩
    · -- s1 = s2: F(φ' ∧ ψ')
      subst h_eq
      intro h_neg_first; exfalso; apply h_neg_first
      exact ⟨s1, hts1, fun h_imp => h_imp h_φs1 h_ψs2, fun _ _ _ hf => absurd hf not_false⟩
    · -- s2 < s1: F(F(φ') ∧ ψ')
      intro _; intro _
      exact ⟨s2, hts2, fun h_imp => h_imp ⟨s1, h_gt, h_φs1, fun _ _ _ hf => absurd hf not_false⟩ h_ψs2, fun _ _ _ hf => absurd hf not_false⟩
  | F_until_equiv φ => exact swap_axiom_F_until_equiv_valid φ
  | P_since_equiv φ => exact swap_axiom_P_since_equiv_valid φ
  | modal_future ψ => exact swap_axiom_mf_valid ψ
  | discrete_symm_fwd =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, truth_at]
    intro ⟨r, hrt, _h_top_r, h_guard⟩
    refine ⟨t + (t - r), lt_add_of_pos_right t (sub_pos.mpr hrt), fun h => h, fun c htc hcs => ?_⟩
    have h1 : r < c - (t - r) := by
      conv_lhs => rw [(sub_sub_cancel t r).symm]
      exact sub_lt_sub_right htc _
    have h2 : c - (t - r) < t := by
      conv_rhs => rw [(add_sub_cancel_right t (t - r)).symm]
      exact sub_lt_sub_right hcs _
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
  | prior_UZ _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | prior_SZ _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | z1 _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | dense_indicator =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.swap_temporal, Formula.neg, truth_at]
    intro ⟨s, hst, _h_top, h_guard⟩
    obtain ⟨r, hsr, hrt⟩ := exists_between hst
    exact h_guard r hsr hrt
  | density _ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold Formula.swap_temporal truth_at
    intro h_HH ⟨s, hst, h_neg_phi_s, h_guard_s⟩
    apply h_HH
    obtain ⟨r, hrs, hrt⟩ := exists_between hst
    refine ⟨r, hrt, ?_, ?_⟩
    · intro h_Hphi_r
      exact h_Hphi_r ⟨s, hrs, h_neg_phi_s, fun q hq1 hq2 => h_guard_s q hq1 (lt_trans hq2 hrt)⟩
    · intro q hq1 hq2
      exact h_guard_s q (lt_trans hrs hq1) hq2

/-! ## Axiom Local Validity -/

/-- Propositional K axiom is locally valid. -/
theorem axiom_prop_k_valid (φ ψ χ : Formula Atom) :
    is_valid D ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h1 h2 h_phi
  exact h1 h_phi (h2 h_phi)

/-- Propositional S axiom is locally valid. -/
theorem axiom_prop_s_valid (φ ψ : Formula Atom) :
    is_valid D (φ.imp (ψ.imp φ)) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_phi _
  exact h_phi

/-- Modal T axiom is locally valid. -/
theorem axiom_modal_t_valid (φ : Formula Atom) :
    is_valid D (φ.box.imp φ) := by
  intro ℱ M Omega _h_sc τ h_mem t
  simp only [truth_at]
  intro h_box
  exact h_box τ h_mem

/-- Modal 4 axiom is locally valid. -/
theorem axiom_modal_4_valid (φ : Formula Atom) :
    is_valid D ((φ.box).imp (φ.box.box)) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_box σ _h_σ_mem ρ h_ρ_mem
  exact h_box ρ h_ρ_mem

/-- Modal B axiom is locally valid. -/
theorem axiom_modal_b_valid (φ : Formula Atom) :
    is_valid D (φ.imp (φ.diamond.box)) := by
  intro ℱ M Omega _h_sc τ h_mem t
  simp only [Formula.diamond, Formula.neg]
  simp only [truth_at]
  intro h_phi σ _h_σ_mem h_box_neg
  exact h_box_neg τ h_mem h_phi

/-- Modal 5 collapse axiom is locally valid. -/
theorem axiom_modal_5_collapse_valid (φ : Formula Atom) :
    is_valid D (φ.box.diamond.imp φ.box) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [Formula.diamond, Formula.neg]
  simp only [truth_at]
  intro h_diamond_box ρ h_ρ_mem
  by_contra h_not_phi
  apply h_diamond_box
  intro σ h_σ_mem h_box_at_sigma
  exact h_not_phi (h_box_at_sigma ρ h_ρ_mem)

/-- Ex falso axiom is locally valid. -/
theorem axiom_ex_falso_valid (φ : Formula Atom) :
    is_valid D (Formula.bot.imp φ) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_bot
  exfalso
  exact h_bot

/-- Peirce's law is locally valid. -/
theorem axiom_peirce_valid (φ ψ : Formula Atom) :
    is_valid D (((φ.imp ψ).imp φ).imp φ) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_peirce
  by_cases h : truth_at M Omega τ t φ
  · exact h
  · have h_imp : truth_at M Omega τ t (φ.imp ψ) := by
      simp only [truth_at]
      intro h_phi
      exfalso
      exact h h_phi
    exact h_peirce h_imp

/-- Modal K distribution axiom is locally valid. -/
theorem axiom_modal_k_dist_valid (φ ψ : Formula Atom) :
    is_valid D ((φ.imp ψ).box.imp (φ.box.imp ψ.box)) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_box_imp h_box_phi σ h_σ_mem
  exact h_box_imp σ h_σ_mem (h_box_phi σ h_σ_mem)

/-- Temporal linearity axiom is locally valid. -/
theorem axiom_temp_linearity_valid (φ ψ : Formula Atom) :
    is_valid D (Formula.and (Formula.some_future φ) (Formula.some_future ψ) |>.imp
      (Formula.or (Formula.some_future (Formula.and φ ψ))
        (Formula.or (Formula.some_future (Formula.and φ (Formula.some_future ψ)))
          (Formula.some_future (Formula.and (Formula.some_future φ) ψ))))) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_conj
  -- Extract Fφ and Fψ witnesses from the conjunction encoding
  -- Guard conversion: h_conj has guard (False → False), goal has (False → False) → False
  have h_Fφ : ∃ s, t < s ∧ truth_at M Omega τ s φ := by
    by_contra h_no; push_neg at h_no
    exact h_conj (fun ⟨s, hts, h_φ, _⟩ _ => absurd h_φ (h_no s hts))
  have h_Fψ : ∃ s, t < s ∧ truth_at M Omega τ s ψ := by
    by_contra h_no; push_neg at h_no
    exact h_conj (fun _ ⟨s, hts, h_ψ, _⟩ => absurd h_ψ (h_no s hts))
  obtain ⟨s1, hts1, h_φs1⟩ := h_Fφ
  obtain ⟨s2, hts2, h_ψs2⟩ := h_Fψ
  rcases lt_trichotomy s1 s2 with h_lt | h_eq | h_gt
  · -- s1 < s2: F(φ ∧ F(ψ))
    intro _; intro h_neg_second; exfalso; apply h_neg_second
    exact ⟨s1, hts1, fun h_imp => h_imp h_φs1 ⟨s2, h_lt, h_ψs2, fun _ _ _ hf => absurd hf not_false⟩, fun _ _ _ hf => absurd hf not_false⟩
  · -- s1 = s2: F(φ ∧ ψ)
    subst h_eq
    intro h_neg_first; exfalso; apply h_neg_first
    exact ⟨s1, hts1, fun h_imp => h_imp h_φs1 h_ψs2, fun _ _ _ hf => absurd hf not_false⟩
  · -- s2 < s1: F(F(φ) ∧ ψ)
    intro _; intro _
    exact ⟨s2, hts2, fun h_imp => h_imp ⟨s1, h_gt, h_φs1, fun _ _ _ hf => absurd hf not_false⟩ h_ψs2, fun _ _ _ hf => absurd hf not_false⟩

/-- Past temporal linearity axiom is locally valid. -/
theorem axiom_temp_linearity_past_valid (φ ψ : Formula Atom) :
    is_valid D (Formula.and (Formula.some_past φ) (Formula.some_past ψ) |>.imp
      (Formula.or (Formula.some_past (Formula.and φ ψ))
        (Formula.or (Formula.some_past (Formula.and φ (Formula.some_past ψ)))
          (Formula.some_past (Formula.and (Formula.some_past φ) ψ))))) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro h_conj
  have h_Pφ : ∃ s, s < t ∧ truth_at M Omega τ s φ := by
    by_contra h_no; push_neg at h_no
    exact h_conj (fun ⟨s, hst, h_φ, _⟩ _ => absurd h_φ (h_no s hst))
  have h_Pψ : ∃ s, s < t ∧ truth_at M Omega τ s ψ := by
    by_contra h_no; push_neg at h_no
    exact h_conj (fun _ ⟨s, hst, h_ψ, _⟩ => absurd h_ψ (h_no s hst))
  obtain ⟨s1, hs1t, h_φs1⟩ := h_Pφ
  obtain ⟨s2, hs2t, h_ψs2⟩ := h_Pψ
  rcases lt_trichotomy s1 s2 with h_lt | h_eq | h_gt
  · -- s1 < s2: P(P(φ) ∧ ψ)
    intro _; intro _
    exact ⟨s2, hs2t, fun h_imp => h_imp ⟨s1, h_lt, h_φs1, fun _ _ _ hf => absurd hf not_false⟩ h_ψs2, fun _ _ _ hf => absurd hf not_false⟩
  · -- s1 = s2: P(φ ∧ ψ)
    subst h_eq
    intro h_neg_first; exfalso; apply h_neg_first
    exact ⟨s1, hs1t, fun h_imp => h_imp h_φs1 h_ψs2, fun _ _ _ hf => absurd hf not_false⟩
  · -- s1 > s2: P(φ ∧ P(ψ))
    intro _; intro h_neg_second; exfalso; apply h_neg_second
    exact ⟨s1, hs1t, fun h_imp => h_imp h_φs1 ⟨s2, h_gt, h_ψs2, fun _ _ _ hf => absurd hf not_false⟩, fun _ _ _ hf => absurd hf not_false⟩

/-- F-Until equivalence axiom validity (BX12). -/
theorem axiom_F_until_equiv_valid (φ : Formula Atom) :
    is_valid D ((Formula.some_future φ).imp
      (Formula.untl φ (Formula.bot.imp Formula.bot))) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro ⟨s, hts, h_φs, _⟩
  exact ⟨s, hts, h_φs, fun _ _ _ hf => absurd hf not_false⟩

/-- P-Since equivalence axiom validity (BX12'). -/
theorem axiom_P_since_equiv_valid (φ : Formula Atom) :
    is_valid D ((Formula.some_past φ).imp
      (Formula.snce φ (Formula.bot.imp Formula.bot))) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  simp only [truth_at]
  intro ⟨s, hst, h_φs, _⟩
  exact ⟨s, hst, h_φs, fun _ _ _ hf => absurd hf not_false⟩

/-- Density axiom (DN) is locally valid on dense orders. -/
theorem axiom_density_valid [DenselyOrdered D] (φ : Formula Atom) :
    is_valid D (φ.all_future.all_future.imp φ.all_future) := by
  intro ℱ M Omega _h_sc τ _h_mem t
  unfold truth_at
  intro h_GG ⟨s, hts, h_neg_φ_s, _h_guard⟩
  apply h_GG
  obtain ⟨r, htr, hrs⟩ := exists_between hts
  exact ⟨r, htr, fun h_Gφ_r => h_Gφ_r ⟨s, hrs, h_neg_φ_s, fun _ _ _ hf => absurd hf not_false⟩, fun _ _ _ hf => absurd hf not_false⟩

/-- Modal-Future axiom is locally valid. -/
theorem axiom_modal_future_valid (φ : Formula Atom) :
    is_valid D ((φ.box).imp ((φ.all_future).box)) := by
  intro ℱ M Omega h_sc τ _h_mem t
  unfold truth_at
  intro h_box_phi σ h_σ_mem ⟨s, hts, h_neg_φ_s, _⟩
  have h_phi_at_shifted := h_box_phi (WorldHistory.time_shift σ (s - t)) (h_sc σ h_σ_mem (s - t))
  exact h_neg_φ_s ((TimeShift.time_shift_preserves_truth M Omega h_sc σ t s φ).mp h_phi_at_shifted)

/-- All dense-compatible axioms are locally valid on dense orders. -/
private theorem axiom_locally_valid [DenselyOrdered D] [Nontrivial D] {φ : Formula Atom} (h : Axiom φ)
    (h_fc : h.minFrameClass ≤ FrameClass.Dense) : is_valid D φ := by
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
    intro _
    obtain ⟨s, hts⟩ := exists_gt t
    exact ⟨s, hts, fun h => h, fun _ _ _ hf => absurd hf not_false⟩
  | serial_past =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [truth_at]
    intro _
    obtain ⟨s, hst⟩ := exists_lt t
    exact ⟨s, hst, fun h => h, fun _ _ _ hf => absurd hf not_false⟩
  | left_mono_until_G φ χ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro h_G ⟨s, hts, h_ψs, h_guard⟩
    refine ⟨s, hts, h_ψs, fun r htr hrs => ?_⟩
    have h_imp_r : truth_at M Omega τ r φ → truth_at M Omega τ r χ := by
      intro h_φr
      by_contra h_neg
      apply h_G
      exact ⟨r, htr, fun h => h_neg (h h_φr), fun _ _ _ hf => absurd hf not_false⟩
    exact h_imp_r (h_guard r htr hrs)
  | left_mono_since_H φ χ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro h_H ⟨s, hst, h_ψs, h_guard⟩
    refine ⟨s, hst, h_ψs, fun r hsr hrt => ?_⟩
    have h_imp_r : truth_at M Omega τ r φ → truth_at M Omega τ r χ := by
      intro h_φr
      by_contra h_neg
      apply h_H
      exact ⟨r, hrt, fun h => h_neg (h h_φr), fun _ _ _ hf => absurd hf not_false⟩
    exact h_imp_r (h_guard r hsr hrt)
  | right_mono_until φ ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro h_G ⟨s, hts, h_φs, h_guard⟩
    have h_ψs : truth_at M Omega τ s ψ := by
      by_contra h_neg
      apply h_G
      exact ⟨s, hts, fun h => h_neg (h h_φs), fun _ _ _ hf => absurd hf not_false⟩
    exact ⟨s, hts, h_ψs, h_guard⟩
  | right_mono_since φ ψ χ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro h_H ⟨s, hst, h_φs, h_guard⟩
    have h_ψs : truth_at M Omega τ s ψ := by
      by_contra h_neg
      apply h_H
      exact ⟨s, hst, fun h => h_neg (h h_φs), fun _ _ _ hf => absurd hf not_false⟩
    exact ⟨s, hst, h_ψs, h_guard⟩
  | connect_future φ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro h_φt ⟨s, hts, h_neg, _⟩
    apply h_neg
    exact ⟨t, hts, h_φt, fun _ _ _ hf => absurd hf not_false⟩
  | connect_past φ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro h_φt ⟨s, hst, h_neg, _⟩
    apply h_neg
    exact ⟨t, hst, h_φt, fun _ _ _ hf => absurd hf not_false⟩
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
    intro h_imp
    exact h_imp h_ψs ⟨t, hts, h_pt, fun r htr hrs => h_guard r htr hrs⟩
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
    intro h_imp
    exact h_imp h_ψs ⟨t, hst, h_pt, fun r hsr hrt => h_guard r hsr hrt⟩
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
    have h_φs₁_and_until : truth_at M Omega τ s₁ φ ∧
        (∃ s₂, s₁ < s₂ ∧ truth_at M Omega τ s₂ ψ ∧
          ∀ q, s₁ < q → q < s₂ → truth_at M Omega τ q φ) := by
      constructor
      · by_contra h_neg; exact h_conj (fun h_φ _ => h_neg h_φ)
      · by_contra h_neg; exact h_conj (fun _ h_until => h_neg h_until)
    obtain ⟨h_φs₁, s₂, hs₁s₂, h_ψs₂, h_guard₂⟩ := h_φs₁_and_until
    refine ⟨s₂, lt_trans hts₁ hs₁s₂, h_ψs₂, fun q htq hqs₂ => ?_⟩
    rcases lt_trichotomy q s₁ with h_lt | h_eq | h_gt
    · exact h_guard₁ q htq h_lt
    · exact h_eq ▸ h_φs₁
    · exact h_guard₂ q h_gt hqs₂
  | absorb_since φ ψ =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.and, Formula.neg, truth_at]
    intro ⟨s₁, hs₁t, h_conj, h_guard₁⟩
    have h_φs₁_and_since : truth_at M Omega τ s₁ φ ∧
        (∃ s₂, s₂ < s₁ ∧ truth_at M Omega τ s₂ ψ ∧
          ∀ q, s₂ < q → q < s₁ → truth_at M Omega τ q φ) := by
      constructor
      · by_contra h_neg; exact h_conj (fun h_φ _ => h_neg h_φ)
      · by_contra h_neg; exact h_conj (fun _ h_since => h_neg h_since)
    obtain ⟨h_φs₁, s₂, hs₂s₁, h_ψs₂, h_guard₂⟩ := h_φs₁_and_since
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
      conv_lhs => rw [(sub_sub_cancel t r).symm]
      exact sub_lt_sub_right htc _
    have h2 : c - (t - r) < t := by
      conv_rhs => rw [(add_sub_cancel_right t (t - r)).symm]
      exact sub_lt_sub_right hcs _
    exact h_guard (c - (t - r)) h1 h2
  | discrete_propagate_fwd =>
    intro ℱ M Omega _h_sc τ _h_mem t
    unfold truth_at
    intro ⟨s, hts, _h_top_s, h_guard⟩ ⟨u, _htu, h_neg, _⟩
    apply h_neg
    refine ⟨u + (s - t), lt_add_of_pos_right u (sub_pos.mpr hts), fun h => h, fun c huc hcs => ?_⟩
    have h1 : t < c - (u - t) := by
      conv_lhs => rw [(sub_sub_cancel u t).symm]
      exact sub_lt_sub_right huc _
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
      conv_lhs => rw [(sub_sub_cancel u t).symm]
      exact sub_lt_sub_right huc _
    have h2 : c - (u - t) < s := by
      conv_rhs => rw [show s = u + (s - t) - (u - t) from by rw [add_sub_sub_cancel, sub_add_cancel]]
      exact sub_lt_sub_right hcs _
    exact h_guard (c - (u - t)) h1 h2
  | discrete_box_necessity =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [truth_at]
    intro ⟨s, hts, _h_top_s, h_guard⟩ σ _h_σ_mem
    exact ⟨s, hts, fun h => h, h_guard⟩
  | density φ => exact axiom_density_valid φ
  | dense_indicator =>
    intro ℱ M Omega _h_sc τ _h_mem t
    simp only [Formula.neg, truth_at]
    intro ⟨s, hts, _h_top, h_guard⟩
    obtain ⟨r, htr, hrs⟩ := exists_between hts
    exact h_guard r htr hrs
  | prior_UZ _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | prior_SZ _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])
  | z1 _ => exact absurd h_fc (by simp [Axiom.minFrameClass, LE.le])

/-! ## Rule Preservation for Local Validity -/

/-- Modus ponens preserves local validity. -/
theorem mp_preserves_valid {φ ψ : Formula Atom}
    (h_imp : is_valid D (φ.imp ψ))
    (h_phi : is_valid D φ) :
    is_valid D ψ := by
  intro ℱ M Omega h_sc τ h_mem t
  exact h_imp ℱ M Omega h_sc τ h_mem t (h_phi ℱ M Omega h_sc τ h_mem t)

/-- Modal necessitation preserves local validity. -/
theorem necessitation_preserves_local_valid {φ : Formula Atom}
    (h : is_valid D φ) :
    is_valid D (Formula.box φ) := by
  intro ℱ M Omega h_sc τ _h_mem t
  simp only [truth_at]
  intro σ h_σ_mem
  exact h ℱ M Omega h_sc σ h_σ_mem t

/-- Temporal necessitation preserves local validity. -/
theorem temporal_necessitation_preserves_local_valid {φ : Formula Atom}
    (h : is_valid D φ) :
    is_valid D (Formula.all_future φ) := by
  intro ℱ M Omega h_sc τ h_mem t
  unfold truth_at
  intro ⟨s, hts, h_neg, _⟩
  exact h_neg (h ℱ M Omega h_sc τ h_mem s)

/-! ## Combined Soundness and Swap-Soundness -/

/--
Combined soundness: derivability implies both validity and swap-validity.
Uses well-founded induction on derivation height.
-/
theorem derivable_valid_and_swap_valid [DenselyOrdered D] [Nontrivial D]
    {φ : Formula Atom} (d : DerivationTree FrameClass.Dense [] φ) :
    is_valid D φ ∧ is_valid D φ.swap_temporal := by
  match d with
  | .axiom _ _ h_ax h_fc => exact ⟨axiom_locally_valid h_ax h_fc, axiom_swap_valid _ h_ax h_fc⟩
  | .assumption _ _ h_mem => exact absurd h_mem (Context.not_mem_nil _)
  | .modus_ponens _ ψ' _ d1 d2 =>
    obtain ⟨h1_valid, h1_swap⟩ := derivable_valid_and_swap_valid d1
    obtain ⟨h2_valid, h2_swap⟩ := derivable_valid_and_swap_valid d2
    exact ⟨mp_preserves_valid h1_valid h2_valid, mp_preserves_swap_valid ψ' _ h1_swap h2_swap⟩
  | .necessitation ψ' d' =>
    obtain ⟨h_valid, h_swap⟩ := derivable_valid_and_swap_valid d'
    exact ⟨necessitation_preserves_local_valid h_valid, modal_k_preserves_swap_valid ψ' h_swap⟩
  | .temporal_necessitation ψ' d' =>
    obtain ⟨h_valid, h_swap⟩ := derivable_valid_and_swap_valid d'
    exact ⟨temporal_necessitation_preserves_local_valid h_valid, temporal_k_preserves_swap_valid ψ' h_swap⟩
  | .temporal_duality ψ' d' =>
    obtain ⟨h_valid, h_swap⟩ := derivable_valid_and_swap_valid d'
    constructor
    · exact h_swap
    · simp only [Formula.swap_temporal_involution]; exact h_valid
  | .weakening Γ' _ _ d' h_sub =>
    have h_eq : Γ' = [] := List.eq_nil_of_subset_nil h_sub
    have h_height_eq : (h_eq ▸ d').height = d'.height := by subst h_eq; rfl
    have h_term : (h_eq ▸ d').height < (DerivationTree.weakening Γ' [] _ d' h_sub).height := by
      simp only [h_height_eq, DerivationTree.height]
      omega
    exact derivable_valid_and_swap_valid (h_eq ▸ d')
termination_by d.height
decreasing_by
  all_goals first
    | exact DerivationTree.mp_height_gt_left _ _
    | exact DerivationTree.mp_height_gt_right _ _
    | simp only [DerivationTree.height]; omega

/-! ## Extracted Theorems -/

/-- Derivability implies local validity. -/
theorem derivable_locally_valid [DenselyOrdered D] [Nontrivial D]
    {φ : Formula Atom} (d : DerivationTree FrameClass.Dense [] φ) :
    is_valid D φ :=
  (derivable_valid_and_swap_valid d).1

/-- Derivability implies swap validity. -/
theorem derivable_implies_swap_valid [DenselyOrdered D] [Nontrivial D]
    {φ : Formula Atom} (d : DerivationTree FrameClass.Dense [] φ) :
    is_valid D φ.swap_temporal :=
  (derivable_valid_and_swap_valid d).2

end Cslib.Logic.Bimodal.Metalogic.SoundnessLemmas
