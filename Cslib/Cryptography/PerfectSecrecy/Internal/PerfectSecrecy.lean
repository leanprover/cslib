/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Cryptography.PerfectSecrecy.PerfectSecrecy.Defs
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-!
# Perfect Secrecy: Internal proofs

Auxiliary lemmas for perfect secrecy:
- Equivalence of the conditional-probability and independence formulations
- Both directions of the ciphertext indistinguishability characterization
  ([KatzLindell2021], Lemma 2.5)
- Shannon's key-space bound ([KatzLindell2021], Theorem 2.12)
-/

namespace Cslib.Cryptography.PerfectSecrecy

open PMF ENNReal

universe u
variable {M K C : Type u}

/-- The joint distribution at `(m, c)` equals `msgDist m * ciphertextDist m c`. -/
theorem jointDist_eq (scheme : EncScheme M K C) (msgDist : PMF M)
    (m : M) (c : C) :
    scheme.jointDist msgDist (m, c) = msgDist m * scheme.ciphertextDist m c := by
  change PMF.bind msgDist (fun m' =>
    PMF.bind (scheme.ciphertextDist m') (fun c' => PMF.pure (m', c'))) (m, c) = _
  rw [PMF.bind_apply]
  rw [tsum_eq_single m]
  · rw [PMF.bind_apply]
    congr 1
    rw [tsum_eq_single c]
    · simp [PMF.pure_apply]
    · intro c' hc'; simp [PMF.pure_apply, hc'.symm]
  · intro m' hm'
    rw [PMF.bind_apply]
    simp [PMF.pure_apply, hm'.symm]

/-- Summing the joint distribution over messages gives the marginal ciphertext distribution. -/
theorem jointDist_tsum_fst (scheme : EncScheme M K C) (msgDist : PMF M) (c : C) :
    ∑' m, scheme.jointDist msgDist (m, c) = scheme.marginalCiphertextDist msgDist c := by
  simp_rw [jointDist_eq]
  change ∑' m, msgDist m * scheme.ciphertextDist m c =
    PMF.bind msgDist (fun m => scheme.ciphertextDist m) c
  rw [PMF.bind_apply]

/-- Perfect secrecy is equivalent to message-ciphertext independence. -/
theorem perfectlySecret_iff_indep (scheme : EncScheme M K C) :
    scheme.PerfectlySecret ↔
    ∀ (msgDist : PMF M) (m : M) (c : C),
      scheme.jointDist msgDist (m, c) =
        msgDist m * scheme.marginalCiphertextDist msgDist c := by
  constructor
  · intro h msgDist m c
    classical
    by_cases hc : c ∈ (scheme.marginalCiphertextDist msgDist).support
    · have hne : (scheme.marginalCiphertextDist msgDist) c ≠ 0 :=
        (PMF.mem_support_iff _ _).mp hc
      have hne_top : (scheme.marginalCiphertextDist msgDist) c ≠ ⊤ :=
        ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one _ c)
      have := h msgDist m c hc
      simp only [EncScheme.posteriorMsgProb] at this
      rw [← this]
      exact (ENNReal.div_mul_cancel hne hne_top).symm
    · simp only [PMF.mem_support_iff, not_not] at hc
      have hj : scheme.jointDist msgDist (m, c) = 0 := by
        have htsum := jointDist_tsum_fst scheme msgDist c
        rw [hc] at htsum
        exact (ENNReal.tsum_eq_zero.mp htsum) m
      rw [hj, hc, mul_zero]
  · intro h msgDist m c hc
    have hne : (scheme.marginalCiphertextDist msgDist) c ≠ 0 :=
      (PMF.mem_support_iff _ _).mp hc
    have hne_top : (scheme.marginalCiphertextDist msgDist) c ≠ ⊤ :=
      ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one _ c)
    simp only [EncScheme.posteriorMsgProb]
    rw [h msgDist m c, ENNReal.mul_div_cancel_right hne hne_top]

/-- Ciphertext indistinguishability implies message-ciphertext independence. -/
theorem indep_of_ciphertextIndist (scheme : EncScheme M K C)
    (h : ∀ m₀ m₁ : M, scheme.ciphertextDist m₀ = scheme.ciphertextDist m₁)
    (msgDist : PMF M) (m : M) (c : C) :
    scheme.jointDist msgDist (m, c) =
      msgDist m * scheme.marginalCiphertextDist msgDist c := by
  rw [jointDist_eq]
  congr 1
  change scheme.ciphertextDist m c =
    PMF.bind msgDist (fun m' => scheme.ciphertextDist m') c
  rw [PMF.bind_apply]
  have hd : ∀ m', scheme.ciphertextDist m' = scheme.ciphertextDist m :=
    fun m' => h m' m
  conv_rhs => arg 1; ext m'; rw [hd m']
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Ciphertext indistinguishability implies perfect secrecy. -/
theorem backward (scheme : EncScheme M K C)
    (h : ∀ m₀ m₁ : M, scheme.ciphertextDist m₀ = scheme.ciphertextDist m₁) :
    scheme.PerfectlySecret :=
  (perfectlySecret_iff_indep scheme).mpr (fun msgDist m c =>
    indep_of_ciphertextIndist scheme h msgDist m c)

/-- Perfect secrecy implies ciphertext indistinguishability. -/
theorem forward (scheme : EncScheme M K C)
    (h : scheme.PerfectlySecret) :
    ∀ m₀ m₁ : M, scheme.ciphertextDist m₀ = scheme.ciphertextDist m₁ := by
  classical
  rw [perfectlySecret_iff_indep] at h
  intro m₀ m₁
  ext c
  set s : Finset M := {m₀, m₁}
  have hs : s.Nonempty := ⟨m₀, Finset.mem_insert_self m₀ {m₁}⟩
  set μ := PMF.uniformOfFinset s hs
  have key : ∀ m, μ m * scheme.ciphertextDist m c =
      μ m * scheme.marginalCiphertextDist μ c := by
    intro m
    have := h μ m c
    rw [jointDist_eq] at this
    exact this
  have hm₀ : μ m₀ ≠ 0 :=
    (PMF.mem_support_uniformOfFinset_iff hs m₀).mpr (Finset.mem_insert_self m₀ {m₁})
  have hm₁ : μ m₁ ≠ 0 :=
    (PMF.mem_support_uniformOfFinset_iff hs m₁).mpr
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self m₁))
  have hm₀_top : μ m₀ ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one μ m₀)
  have hm₁_top : μ m₁ ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one μ m₁)
  have h₀ : scheme.ciphertextDist m₀ c = scheme.marginalCiphertextDist μ c := by
    have := key m₀; rw [mul_comm, mul_comm (μ m₀)] at this
    exact (ENNReal.mul_left_inj hm₀ hm₀_top).mp this
  have h₁ : scheme.ciphertextDist m₁ c = scheme.marginalCiphertextDist μ c := by
    have := key m₁; rw [mul_comm, mul_comm (μ m₁)] at this
    exact (ENNReal.mul_left_inj hm₁ hm₁_top).mp this
  exact h₀.trans h₁.symm

/-- Perfect secrecy requires `|K| ≥ |M|` (Shannon's theorem). -/
theorem shannonKeySpace [Fintype M] [Fintype K]
    (scheme : EncScheme M K C) (h : scheme.PerfectlySecret) :
    Fintype.card K ≥ Fintype.card M := by
  classical
  have hci := forward scheme h
  by_cases hM : IsEmpty M
  · simp [Fintype.card_eq_zero]
  · rw [not_isEmpty_iff] at hM
    obtain ⟨m₀⟩ := hM
    obtain ⟨c₀, hc₀⟩ := (scheme.ciphertextDist m₀).support_nonempty
    have key_exists : ∀ m, ∃ k ∈ scheme.gen.support, c₀ ∈ (scheme.enc k m).support := by
      intro m
      have : c₀ ∈ (scheme.ciphertextDist m).support := by rw [hci m m₀]; exact hc₀
      exact (PMF.mem_support_bind_iff _ _ _).mp this
    choose f hf_mem hf_enc using key_exists
    exact Fintype.card_le_of_injective f fun m₁ m₂ heq => by
      have h₁ := scheme.correct _ (hf_mem m₁) m₁ c₀ (hf_enc m₁)
      have h₂ := scheme.correct _ (hf_mem m₂) m₂ c₀ (hf_enc m₂)
      rw [heq] at h₁; exact h₁.symm.trans h₂

end Cslib.Cryptography.PerfectSecrecy
