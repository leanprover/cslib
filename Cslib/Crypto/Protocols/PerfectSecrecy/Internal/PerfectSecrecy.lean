/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.Defs
public import Mathlib.Probability.Distributions.Uniform

/-!
# Perfect Secrecy: Internal proofs

Auxiliary lemmas for perfect secrecy:
- Equivalence of the conditional-probability and independence formulations
- Both directions of the ciphertext indistinguishability characterization
  ([KatzLindell2020], Lemma 2.5)
- Shannon's key-space bound ([KatzLindell2020], Theorem 2.12)
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.PerfectSecrecy

open PMF ENNReal

universe u
variable {M K C : Type u}

/-- The joint distribution at `(m, c)` equals `msgDist m * ciphertextDist m c`. -/
theorem jointDist_eq (scheme : EncScheme M K C) (msgDist : PMF M)
    (m : M) (c : C) :
    scheme.jointDist msgDist (m, c) = msgDist m * scheme.ciphertextDist m c :=
  Cslib.Probability.PMF.bind_pair_apply msgDist scheme.ciphertextDist m c

/-- Summing the joint distribution over messages gives the marginal ciphertext distribution. -/
theorem jointDist_tsum_fst (scheme : EncScheme M K C) (msgDist : PMF M) (c : C) :
    ∑' m, scheme.jointDist msgDist (m, c) = scheme.marginalCiphertextDist msgDist c :=
  Cslib.Probability.PMF.bind_pair_tsum_fst msgDist scheme.ciphertextDist c

/-- Perfect secrecy is equivalent to message-ciphertext independence.
The two formulations are related by multiplying/dividing by `marginal(c)`. -/
theorem perfectlySecret_iff_indep (scheme : EncScheme M K C) :
    scheme.PerfectlySecret ↔
    ∀ (msgDist : PMF M) (m : M) (c : C),
      scheme.jointDist msgDist (m, c) =
        msgDist m * scheme.marginalCiphertextDist msgDist c := by
  constructor
  · intro h msgDist m c
    by_cases hc : (scheme.marginalCiphertextDist msgDist) c = 0
    · have := ENNReal.tsum_eq_zero.mp
        ((jointDist_tsum_fst scheme msgDist c).trans hc) m
      rw [this, hc, mul_zero]
    · have hne_top := ne_top_of_le_ne_top one_ne_top
        (PMF.coe_le_one (scheme.marginalCiphertextDist msgDist) c)
      have := DFunLike.congr_fun (h msgDist c ((PMF.mem_support_iff _ _).mpr hc)) m
      simp only [EncScheme.posteriorMsgDist_apply] at this
      rw [← this, ENNReal.div_mul_cancel hc hne_top]
  · intro h msgDist c hc; ext m
    simp only [EncScheme.posteriorMsgDist_apply]
    rw [h msgDist m c, ENNReal.mul_div_cancel_right
      ((PMF.mem_support_iff _ _).mp hc)
      (ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one _ c))]

/-- Ciphertext indistinguishability implies message-ciphertext independence. -/
theorem indep_of_ciphertextIndist (scheme : EncScheme M K C)
    (h : scheme.CiphertextIndist)
    (msgDist : PMF M) (m : M) (c : C) :
    scheme.jointDist msgDist (m, c) =
      msgDist m * scheme.marginalCiphertextDist msgDist c := by
  rw [jointDist_eq]; congr 1
  change scheme.ciphertextDist m c =
    PMF.bind msgDist (fun m' => scheme.ciphertextDist m') c
  rw [PMF.bind_apply]
  conv_rhs => arg 1; ext m'; rw [h m' m]
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
  intro m₀ m₁; ext c
  have hs : ({m₀, m₁} : Finset M).Nonempty := ⟨m₀, Finset.mem_insert_self ..⟩
  set μ := PMF.uniformOfFinset _ hs
  suffices key : ∀ m ∈ ({m₀, m₁} : Finset M),
      scheme.ciphertextDist m c = scheme.marginalCiphertextDist μ c by
    exact (key m₀ (by simp)).trans (key m₁ (by simp)).symm
  intro m hm
  have hne := (PMF.mem_support_uniformOfFinset_iff hs m).mpr hm
  have hne_top := ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one μ m)
  exact (ENNReal.mul_right_inj hne hne_top).mp (by rw [← jointDist_eq]; exact h μ m c)

/-- If each message maps to a key that encrypts it to a common ciphertext,
then the key assignment is injective (by correctness of decryption). -/
lemma encrypt_key_injective (scheme : EncScheme M K C)
    (f : M → K) (c₀ : C)
    (hf_mem : ∀ m, f m ∈ scheme.gen.support)
    (hf_enc : ∀ m, c₀ ∈ (scheme.enc (f m) m).support) :
    Function.Injective f :=
  fun m₁ m₂ heq =>
    (scheme.correct _ (hf_mem m₁) m₁ c₀ (hf_enc m₁)).symm.trans
      (heq ▸ scheme.correct _ (hf_mem m₂) m₂ c₀ (hf_enc m₂))

/-- Perfect secrecy requires `|K| ≥ |M|` (Shannon's theorem). -/
theorem shannonKeySpace [Finite K]
    (scheme : EncScheme M K C) (h : scheme.PerfectlySecret) :
    Nat.card K ≥ Nat.card M := by
  classical
  have hci := ciphertextIndist_of_perfectlySecret scheme h
  by_cases hM : IsEmpty M; · simp
  obtain ⟨m₀⟩ := not_isEmpty_iff.mp hM
  obtain ⟨c₀, hc₀⟩ := (scheme.ciphertextDist m₀).support_nonempty
  have key_exists : ∀ m, ∃ k ∈ scheme.gen.support, c₀ ∈ (scheme.enc k m).support := by
    intro m
    exact (PMF.mem_support_bind_iff _ _ _).mp
      (show c₀ ∈ (scheme.ciphertextDist m).support by rw [hci m m₀]; exact hc₀)
  choose f hf_mem hf_enc using key_exists
  exact Nat.card_le_card_of_injective f
    (encrypt_key_injective scheme f c₀ hf_mem hf_enc)

end Cslib.Crypto.Protocols.PerfectSecrecy
