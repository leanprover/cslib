/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.PerfectSecrecy.Defs
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-!
# Perfect Secrecy: Internal proofs

Auxiliary lemmas for perfect secrecy:
- Equivalence of the conditional-probability and independence formulations
- Both directions of the ciphertext indistinguishability characterization
  ([KatzLindell2020], Lemma 2.5)
- Shannon's key-space bound ([KatzLindell2020], Theorem 2.12)
-/

namespace Cslib.Crypto.PerfectSecrecy

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

/-- The posterior message probabilities sum to 1 when the ciphertext
has positive probability. -/
theorem posteriorMsgProb_hasSum (scheme : EncScheme M K C)
    (msgDist : PMF M) (c : C)
    (hc : c ∈ (scheme.marginalCiphertextDist msgDist).support) :
    HasSum (fun m => scheme.posteriorMsgProb msgDist c m) 1 := by
  have hne := (PMF.mem_support_iff _ _).mp hc
  have hne_top := ne_top_of_le_ne_top one_ne_top
    (PMF.coe_le_one (scheme.marginalCiphertextDist msgDist) c)
  have : ∑' m, scheme.posteriorMsgProb msgDist c m = 1 := by
    simp only [EncScheme.posteriorMsgProb, div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, jointDist_tsum_fst]
    exact ENNReal.mul_inv_cancel hne hne_top
  exact this ▸ ENNReal.summable.hasSum

namespace EncScheme

/-- The posterior message distribution `Pr[M | C = c]` as a probability
distribution, given a message prior and a ciphertext in the support of
the marginal distribution. -/
noncomputable def posteriorMsgDist (scheme : EncScheme M K C)
    (msgDist : PMF M) (c : C)
    (hc : c ∈ (scheme.marginalCiphertextDist msgDist).support) : PMF M :=
  ⟨fun m => scheme.posteriorMsgProb msgDist c m,
   posteriorMsgProb_hasSum scheme msgDist c hc⟩

@[simp]
theorem posteriorMsgDist_apply (scheme : EncScheme M K C)
    (msgDist : PMF M) (c : C)
    (hc : c ∈ (scheme.marginalCiphertextDist msgDist).support) (m : M) :
    scheme.posteriorMsgDist msgDist c hc m =
      scheme.posteriorMsgProb msgDist c m :=
  rfl

/-- Perfect secrecy: the posterior message distribution equals the prior. -/
theorem perfectlySecret_iff_posteriorEq (scheme : EncScheme M K C) :
    scheme.PerfectlySecret ↔
    ∀ (msgDist : PMF M) (c : C)
      (hc : c ∈ (scheme.marginalCiphertextDist msgDist).support),
      scheme.posteriorMsgDist msgDist c hc = msgDist := by
  constructor
  · intro h msgDist c hc
    ext m
    simp [h msgDist m c hc]
  · intro h msgDist m c hc
    simpa using DFunLike.congr_fun (h msgDist c hc) m

end EncScheme

/-- Perfect secrecy is equivalent to message-ciphertext independence.
The two formulations are related by multiplying/dividing by `marginal(c)`. -/
theorem perfectlySecret_iff_indep (scheme : EncScheme M K C) :
    scheme.PerfectlySecret ↔
    ∀ (msgDist : PMF M) (m : M) (c : C),
      scheme.jointDist msgDist (m, c) =
        msgDist m * scheme.marginalCiphertextDist msgDist c := by
  constructor
  · intro h msgDist m c
    classical
    by_cases hc : (scheme.marginalCiphertextDist msgDist) c = 0
    · have := ENNReal.tsum_eq_zero.mp
        ((jointDist_tsum_fst scheme msgDist c).trans hc) m
      rw [this, hc, mul_zero]
    · have hne_top := ne_top_of_le_ne_top one_ne_top
        (PMF.coe_le_one (scheme.marginalCiphertextDist msgDist) c)
      have := h msgDist m c ((PMF.mem_support_iff _ _).mpr hc)
      simp only [EncScheme.posteriorMsgProb] at this
      rw [← this, ENNReal.div_mul_cancel hc hne_top]
  · intro h msgDist m c hc
    have hne := (PMF.mem_support_iff _ _).mp hc
    have hne_top := ne_top_of_le_ne_top one_ne_top
      (PMF.coe_le_one (scheme.marginalCiphertextDist msgDist) c)
    simp only [EncScheme.posteriorMsgProb]
    rw [h msgDist m c, ENNReal.mul_div_cancel_right hne hne_top]

/-- Ciphertext indistinguishability implies message-ciphertext independence. -/
theorem indep_of_ciphertextIndist (scheme : EncScheme M K C)
    (h : scheme.CiphertextIndist)
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
theorem perfectlySecret_of_ciphertextIndist (scheme : EncScheme M K C)
    (h : scheme.CiphertextIndist) :
    scheme.PerfectlySecret :=
  (perfectlySecret_iff_indep scheme).mpr (fun msgDist m c =>
    indep_of_ciphertextIndist scheme h msgDist m c)

/-- Perfect secrecy implies ciphertext indistinguishability. -/
theorem ciphertextIndist_of_perfectlySecret (scheme : EncScheme M K C)
    (h : scheme.PerfectlySecret) :
    scheme.CiphertextIndist := by
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

/-- If each message maps to a key that encrypts it to a common ciphertext,
then the key assignment is injective (by correctness of decryption). -/
lemma encrypt_key_injective (scheme : EncScheme M K C)
    (f : M → K) (c₀ : C)
    (hf_mem : ∀ m, f m ∈ scheme.gen.support)
    (hf_enc : ∀ m, c₀ ∈ (scheme.enc (f m) m).support) :
    Function.Injective f :=
  fun m₁ m₂ heq => by
    have h₁ := scheme.correct _ (hf_mem m₁) m₁ c₀ (hf_enc m₁)
    have h₂ := scheme.correct _ (hf_mem m₂) m₂ c₀ (hf_enc m₂)
    rw [heq] at h₁; exact h₁.symm.trans h₂

/-- Perfect secrecy requires `|K| ≥ |M|` (Shannon's theorem). -/
theorem shannonKeySpace [Finite K]
    (scheme : EncScheme M K C) (h : scheme.PerfectlySecret) :
    Nat.card K ≥ Nat.card M := by
  classical
  have hci := ciphertextIndist_of_perfectlySecret scheme h
  by_cases hM : IsEmpty M
  · simp
  · rw [not_isEmpty_iff] at hM
    obtain ⟨m₀⟩ := hM
    obtain ⟨c₀, hc₀⟩ := (scheme.ciphertextDist m₀).support_nonempty
    have key_exists : ∀ m, ∃ k ∈ scheme.gen.support, c₀ ∈ (scheme.enc k m).support := by
      intro m
      have : c₀ ∈ (scheme.ciphertextDist m).support := by rw [hci m m₀]; exact hc₀
      exact (PMF.mem_support_bind_iff _ _ _).mp this
    choose f hf_mem hf_enc using key_exists
    exact Nat.card_le_card_of_injective f
      (encrypt_key_injective scheme f c₀ hf_mem hf_enc)

end Cslib.Crypto.PerfectSecrecy
