/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.Defs

/-!
# Perfect Secrecy

Characterisation theorems for perfect secrecy following
[KatzLindell2020], Chapter 2: the equivalence with message-ciphertext
independence, the ciphertext indistinguishability characterization, and
Shannon's key-space bound.

## Main results

- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_iff_indep`:
  perfect secrecy is exactly message-ciphertext independence
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_iff_ciphertextIndist`:
  ciphertext indistinguishability characterization ([KatzLindell2020], Lemma 2.5)
- `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.perfectlySecret_keySpace_ge`:
  Shannon's theorem, `|K| ≥ |M|` ([KatzLindell2020], Theorem 2.12)

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme

open MeasureTheory ProbabilityTheory Cslib.Probability.Measure

variable {M K C : Type*} [MeasurableSpace M] [MeasurableSpace K] [MeasurableSpace C]

/-- The joint measure on a rectangle is obtained by integrating the encryption channel. -/
theorem jointDist_apply_prod (scheme : EncScheme M K C) (msgDist : Measure M) [SFinite msgDist]
    {messages : Set M} {ciphertexts : Set C}
    (hm : MeasurableSet messages) (hc : MeasurableSet ciphertexts) :
    scheme.jointDist msgDist (messages ×ˢ ciphertexts) =
      ∫⁻ m in messages, scheme.ciphertextDist m ciphertexts ∂msgDist :=
  Measure.compProd_apply_prod hm hc

/-- The second marginal of the joint distribution is the ciphertext distribution. -/
theorem jointDist_snd (scheme : EncScheme M K C) (msgDist : Measure M) [SFinite msgDist] :
    (scheme.jointDist msgDist).snd = scheme.marginalCiphertextDist msgDist :=
  Measure.snd_compProd _ _

/-- Perfect secrecy is equivalent to independence on all measurable events. -/
theorem perfectlySecret_iff_indep (scheme : EncScheme M K C) :
    scheme.PerfectlySecret ↔
      ∀ (msgDist : Measure M) [IsProbabilityMeasure msgDist]
        (messages : Set M) (ciphertexts : Set C),
        MeasurableSet messages → MeasurableSet ciphertexts →
        scheme.jointDist msgDist (messages ×ˢ ciphertexts) =
          msgDist messages * scheme.marginalCiphertextDist msgDist ciphertexts := by
  constructor
  · intro h μ _ messages ciphertexts _ _
    rw [h μ, Measure.prod_prod]
  · intro h μ _
    exact Measure.ext_prod fun hm hc => (h μ _ _ hm hc).trans (Measure.prod_prod _ _).symm

/-- A scheme is perfectly secret iff its ciphertext law is independent of the message
([KatzLindell2020], Lemma 2.5). Only the message singletons need to be measurable. -/
theorem perfectlySecret_iff_ciphertextIndist [MeasurableSingletonClass M]
    (scheme : EncScheme M K C) : scheme.PerfectlySecret ↔ scheme.CiphertextIndist := by
  classical
  refine ⟨fun h m₀ m₁ => ?_, fun h μ _ => compProd_eq_prod_of_outputIndist μ _ h⟩
  let messages : Finset M := {m₀, m₁}
  let μ := uniformOn (messages : Set M)
  have : IsProbabilityMeasure μ :=
    isProbabilityMeasure_uniformOn messages.finite_toSet (by simp [messages])
  have key : ∀ m ∈ messages, scheme.ciphertextDist m = scheme.marginalCiphertextDist μ := by
    intro m hm
    apply Measure.ext
    intro ciphertexts hc
    have he := (perfectlySecret_iff_indep scheme).mp h μ {m} ciphertexts
      (measurableSet_singleton m) hc
    rw [jointDist_apply_prod _ _ (measurableSet_singleton m) hc, lintegral_singleton,
      mul_comm] at he
    have hmass : μ {m} ≠ 0 := by
      change uniformOn (messages : Set M) {m} ≠ 0
      intro hz
      have he := (uniformOn_eq_zero_iff messages.finite_toSet).mp hz
      have hm' : m ∈ (messages : Set M) ∩ {m} := ⟨hm, rfl⟩
      simp only [he, Set.mem_empty_iff_false] at hm'
    exact (ENNReal.mul_right_inj hmass (measure_ne_top μ {m})).mp he
  exact (key m₀ (by simp [messages])).trans (key m₁ (by simp [messages])).symm

/-- Ciphertext indistinguishability implies message-ciphertext independence. -/
theorem indep_of_ciphertextIndist (scheme : EncScheme M K C)
    (h : scheme.CiphertextIndist) (msgDist : Measure M) [IsProbabilityMeasure msgDist] :
    scheme.jointDist msgDist = msgDist.prod (scheme.marginalCiphertextDist msgDist) :=
  compProd_eq_prod_of_outputIndist msgDist _ h

/-- Under perfect secrecy, Mathlib's posterior equals the prior almost surely. -/
theorem posteriorMsgDist_eq_prior [StandardBorelSpace M] [Nonempty M]
    (scheme : EncScheme M K C) (h : scheme.PerfectlySecret)
    (msgDist : Measure M) [IsProbabilityMeasure msgDist] :
    scheme.posteriorMsgDist msgDist =ᵐ[scheme.marginalCiphertextDist msgDist]
      fun _ => msgDist :=
  posterior_eq_prior_of_compProd_eq_prod msgDist _ (h msgDist)

/-- Perfect secrecy requires `|K| ≥ |M|` — Shannon's theorem.
Ciphertexts may have a continuous distribution; correctness is used almost surely
([KatzLindell2020], Theorem 2.12). -/
theorem perfectlySecret_keySpace_ge [Finite K] [MeasurableSingletonClass M]
    (scheme : EncScheme M K C) (h : scheme.PerfectlySecret) :
    Nat.card M ≤ Nat.card K := by
  classical
  cases finite_or_infinite M with
  | inr hM => simp [Nat.card_eq_zero_of_infinite]
  | inl hM =>
    have hci := (perfectlySecret_iff_ciphertextIndist scheme).mp h
    by_cases hM : IsEmpty M
    · simp
    obtain ⟨m₀⟩ := not_isEmpty_iff.mp hM
    have key_exists (m : M) : ∀ᵐ c ∂scheme.ciphertextDist m₀, ∃ k, scheme.dec k c = m := by
      rw [← hci m m₀, ciphertextDist_eq_comp]
      apply Measure.ae_comp_of_ae_ae
      · have hk (k : K) : Measurable (scheme.dec k) :=
          scheme.dec_measurable.comp measurable_prodMk_left
        simpa only [Set.ofPred_exists, Set.preimage, Set.mem_singleton_iff] using
          MeasurableSet.iUnion (fun k => hk k (measurableSet_singleton m))
      · filter_upwards [scheme.correct] with k hk
        exact (hk m).mono fun c hc => ⟨k, hc⟩
    obtain ⟨c, hc⟩ := (ae_all_iff.mpr key_exists).exists
    choose f hf using hc
    exact Nat.card_le_card_of_injective f fun m₁ m₂ heq =>
      (hf m₁).symm.trans (heq ▸ hf m₂)

end Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme
