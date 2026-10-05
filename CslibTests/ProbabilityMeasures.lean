/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Crypto.Primitives.PRG.Basic
import Cslib.Crypto.Protocols.PerfectSecrecy.OneTimePad
import Cslib.Crypto.Protocols.SecretSharing.Defs
import Cslib.Crypto.Protocols.SecretSharing.Shamir
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open MeasureTheory ProbabilityTheory Cslib.Probability.Measure
open scoped ENNReal
open Cslib.Crypto.Protocols.PerfectSecrecy Cslib.Crypto.PRG

namespace CslibTests.ProbabilityMeasures

-- An independently specified old-style fair bit gives exactly the same output laws.
private noncomputable def fairBit : PMF Bool :=
  PMF.ofFintype (fun _ => 1 / 2) (by
    norm_num [Fintype.sum_bool]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

example (f : Bool → Bool × Bool) :
    (Generator.mk f).outputDist = (fairBit.map f).toMeasure := by
  have h : (uniformOfFintype Bool : Measure Bool) = fairBit.toMeasure := by
    apply Measure.ext_of_singleton
    intro b
    change uniformOn (Set.univ : Set Bool) {b} = fairBit.toMeasure {b}
    rw [uniformOn_univ, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [fairBit, PMF.ofFintype_apply]
  change (uniformOfFintype Bool : Measure Bool).map f = _
  rw [h, PMF.toMeasure_map f fairBit (measurable_of_countable f)]

-- The expected ciphertext probability is unchanged by the migration.
example (l : ℕ) (m c : BitVec l) :
    (otp l).ciphertextDist m {c} = (2 ^ l : ℝ≥0∞)⁻¹ := by
  simp [otp_ciphertextDist_eq_uniform, uniformOfFintype, uniformOn_univ,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

-- Almost-sure posterior equality recovers the former positive-mass discrete statement.
example (l : ℕ) (μ : Measure (BitVec l)) [IsProbabilityMeasure μ] (c : BitVec l)
    (hc : (otp l).marginalCiphertextDist μ {c} ≠ 0) :
    (otp l).posteriorMsgDist μ c = μ :=
  ae_iff_of_countable.mp ((otp l).posteriorMsgDist_eq_prior (otp_perfectlySecret l) μ) c hc

-- Continuous keys and ciphertexts are accepted by the public encryption interface.
private noncomputable def gaussianMask : EncScheme ℝ ℝ ℝ :=
  .ofPure (gaussianReal 0 1) (fun key message => key + message)
    (fun key ciphertext => ciphertext - key) (by fun_prop) (by fun_prop)
    (fun _ _ => by ring)

example : IsProbabilityMeasure (gaussianMask.ciphertextDist 3) := inferInstance

-- The common set of good keys also covers a message chosen using the sampled key.
example : ∀ᵐ key ∂gaussianMask.gen, ∀ᵐ c ∂gaussianMask.enc (key, key),
    gaussianMask.dec key c = key := by
  filter_upwards [gaussianMask.correct] with key hk
  exact hk key

-- Independence and conditioning also work with a non-atomic prior and observation law.
example : posterior (Kernel.const ℝ (gaussianReal 1 2)) (gaussianReal 0 1)
    =ᵐ[gaussianReal 1 2] fun _ => gaussianReal 0 1 := by
  simpa using posterior_eq_prior_of_compProd_eq_prod (gaussianReal 0 1)
    (Kernel.const ℝ (gaussianReal 1 2)) (by simp)

open Cslib.Crypto.Protocols.SecretSharing

-- Shamir's canonical sampler remains normalized, with privacy for unauthorized coalitions.
example {F Party : Type*} [Field F] [Fintype F] [Fintype Party]
    [MeasurableSpace F] [MeasurableSingletonClass F] (params : Shamir.Params F Party) :
    (Shamir.scheme params).PerfectlyPrivate := (Shamir.scheme params).perfectlyPrivate

example {Secret Randomness Party Share : Type*}
    [MeasurableSpace Secret] [MeasurableSpace Randomness] [MeasurableSpace Share]
    (scheme : Scheme Secret Randomness Party Share) (s : Finset Party) (secret : Secret) :
    IsProbabilityMeasure (scheme.viewDist s secret) := inferInstance

end CslibTests.ProbabilityMeasures
