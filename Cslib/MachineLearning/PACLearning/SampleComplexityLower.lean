/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.MachineLearning.PACLearning.SampleComplexityLower.EHKVProof

@[expose] public section

/-! # Sample Complexity Lower Bound

We use the prefix `ehkv` for Ehrenfeucht–Haussler–Kearns–Valiant throughout.

This module formalizes the main result of [EHKV1989]: a lower bound on the
number of examples required for distribution-free PAC learning of a concept
class, in terms of its Vapnik-Chervonenkis dimension.

**Theorem 1** [EHKV1989, Theorem 1]: Assume `0 < ε ≤ 1/8`,
`0 < δ < 1/14`, and `VCdim(C) ≥ 2`. Then any `(ε, δ)`-learning
algorithm for `C` must use sample size at least `(VCdim(C) - 1) / (32ε)`.

The proof constructs an adversarial distribution `P` on `d + 1` points
(where `d = VCdim(C) - 1`). Via a Markov/Bernoulli bound (Lemma 3),
"bad" samples — those which do not reveal enough of the shattered
set — occur with probability `> 1/2` when the sample size is too
small. An involution pairing argument (Lemma 2) shows that for each
bad sample, at least half of the `2^d` concepts obtained from
shattering force large error, and a counting/contradiction argument
then produces a single concept whose failure probability exceeds `δ`.

## Proof structure (submodules)

- `SampleComplexityLower.Helpers`: generic lemmas (Bernoulli inequality,
  product measure support, `seenElements`, integration bound)
- `SampleComplexityLower.AdversarialMeasure`: construction of the
  adversarial probability distribution on `d + 1` points
- `SampleComplexityLower.InvolutionPairing`: the involution/pairing
  argument and complementary-error contradiction
- `SampleComplexityLower.EHKVProof`: Markov bound on bad samples,
  half-fraction sum lower bound, and the assembled contradiction

## Main statements

- `sample_complexity_lower_bound_randomized`: **Theorem 1** of [EHKV1989] for
  randomized learners — the full strength of the result.
- `sample_complexity_lower_bound`: deterministic corollary via
  `IsPACLearner.toIsRPACLearner`.
- `sample_complexity_lower_bound_vcDim`: the bound stated in terms of `vcDim`.
- `sampleComplexity_lower_bound_vcDim`: lower bound on `sampleComplexity` via `vcDim`.
- `rsampleComplexity_lower_bound_vcDim`: lower bound on `rsampleComplexity` via `vcDim`.

## References

* [A. Ehrenfeucht, D. Haussler, M. Kearns, L. Valiant,
  *A General Lower Bound on the Number of Examples Needed
  for Learning*][EHKV1989]
-/

open MeasureTheory Set Finset
open scoped ENNReal

noncomputable section

namespace Cslib.MachineLearning

/-- **Theorem 1 (randomized)** [EHKV1989]: The sample-complexity lower bound
`(VCdim(C) - 1) / (32 * ε) ≤ m` holds for *randomized* `(ε, δ)`-PAC
learners. This is the full strength of the EHKV result. -/
theorem sample_complexity_lower_bound_randomized
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {C : ConceptClass α}
    {W : Finset α} (hW : SetShatters C (↑W))
    {m : ℕ} {ε δ : ℝ≥0∞}
    (hε_pos : 0 < ε) (hε_le : ε ≤ ENNReal.ofReal (1 / 8))
    (hδ_lt : δ < ENNReal.ofReal (1 / 14))
    (hW_card : 2 ≤ W.card)
    (hlearn : IsRPACLearner m ε δ C) :
    (W.card - 1 : ℝ) / (32 * ε.toReal) ≤ m := by
  by_contra h
  push Not at h
  have hε_ne_top : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hε_le
  have hε'_pos : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε_pos) hε_ne_top
  have h32ε_pos : (0 : ℝ) < 32 * ε.toReal := by positivity
  have hW_sub : (0 : ℝ) < (W.card : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hW_card
    linarith
  have hm_ennreal : (↑m : ℝ≥0∞) < ENNReal.ofReal
      ((W.card - 1 : ℝ) / (32 * ε.toReal)) := by
    rw [show (↑m : ℝ≥0∞) = ENNReal.ofReal (m : ℝ) from by rw [ENNReal.ofReal_natCast]]
    exact ENNReal.ofReal_lt_ofReal_iff (div_pos hW_sub h32ε_pos) |>.mpr h
  obtain ⟨Ω, mΩ, Q, hQ, A, hA⟩ := hlearn
  have hA_aem : ∀ (P : Measure α) [IsProbabilityMeasure P], ∀ c ∈ C,
      AEMeasurable (fun ω => (Measure.pi (fun _ : Fin m => P))
        {xs : Fin m → α | hypothesisError P ((A ω) (sampleOf c xs)) c > ε}) Q :=
    fun P _ c hc => (hA P c hc).1
  obtain ⟨P, hP, c, hc, hbad⟩ :=
    exists_bad_distribution_and_concept_randomized hW hW_card
      hε_pos hε_le hδ_lt hm_ennreal Q A hA_aem
  haveI := hP
  exact absurd ((hA P c hc).2) (not_le_of_gt hbad)

/-- **Theorem 1** [EHKV1989]: Assume `0 < ε ≤ 1/8`, `0 < δ < 1/14`,
and `VCdim(C) ≥ 2`. Then any deterministic `(ε, δ)`-learning algorithm
for `C` must use sample size `m` satisfying `(VCdim(C) - 1) / (32 * ε) ≤ m`.

This is a corollary of the stronger `sample_complexity_lower_bound_randomized`
via `IsPACLearner.toIsRPACLearner`. -/
theorem sample_complexity_lower_bound
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {C : ConceptClass α}
    {W : Finset α} (hW : SetShatters C (↑W))
    {m : ℕ} {ε δ : ℝ≥0∞}
    (hε_pos : 0 < ε) (hε_le : ε ≤ ENNReal.ofReal (1 / 8))
    (hδ_lt : δ < ENNReal.ofReal (1 / 14))
    (hW_card : 2 ≤ W.card)
    (hlearn : IsPACLearner m ε δ C) :
    (W.card - 1 : ℝ) / (32 * ε.toReal) ≤ m := by
  exact sample_complexity_lower_bound_randomized hW hε_pos hε_le hδ_lt hW_card
    (IsPACLearner.toIsRPACLearner.{_, 0} hlearn)

/-- **Corollary**: The EHKV sample-complexity lower bound stated in terms of `vcDim`.

If the VC dimension of `C` is at least `2` (and is finite, i.e., the defining set is bounded
above), then any randomized `(ε, δ)`-PAC learner for `C` must use at least
`(vcDim C - 1) / (32ε)` samples.

This wraps `sample_complexity_lower_bound_randomized` by extracting a shattered witness from
`vcDim`. -/
theorem sample_complexity_lower_bound_vcDim
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {C : ConceptClass α}
    {m : ℕ} {ε δ : ℝ≥0∞}
    (hε_pos : 0 < ε) (hε_le : ε ≤ ENNReal.ofReal (1 / 8))
    (hδ_lt : δ < ENNReal.ofReal (1 / 14))
    (hvc : 2 ≤ vcDim C)
    (hbdd : BddAbove {n : ℕ | ∃ W : Finset α, W.card = n ∧ SetShatters C (↑W)})
    (hlearn : IsRPACLearner m ε δ C) :
    (vcDim C - 1 : ℝ) / (32 * ε.toReal) ≤ m := by
  set S := {n : ℕ | ∃ W : Finset α, W.card = n ∧ SetShatters C (↑W)}
  have hne : S.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have : (2 : ℕ) ≤ sSup (∅ : Set ℕ) := hempty ▸ hvc
    simp at this
  obtain ⟨W, hWcard, hW⟩ := Nat.sSup_mem hne hbdd
  have hW_card : 2 ≤ W.card := hWcard ▸ hvc
  have hvc_eq : vcDim C = W.card := hWcard.symm
  rw [show (vcDim C : ℝ) = (W.card : ℝ) from by exact_mod_cast hvc_eq]
  exact sample_complexity_lower_bound_randomized hW hε_pos hε_le hδ_lt hW_card hlearn

/-- Lower bound on deterministic sample complexity in terms of `vcDim`.

If the VC dimension is at least `2` and finite, then
`(vcDim C - 1) / (32ε) ≤ sampleComplexity C ε δ`,
provided the concept class is learnable (some deterministic PAC learner exists). -/
theorem sampleComplexity_lower_bound_vcDim
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {C : ConceptClass α}
    {ε δ : ℝ≥0∞}
    (hε_pos : 0 < ε) (hε_le : ε ≤ ENNReal.ofReal (1 / 8))
    (hδ_lt : δ < ENNReal.ofReal (1 / 14))
    (hvc : 2 ≤ vcDim C)
    (hbdd : BddAbove {n : ℕ | ∃ W : Finset α, W.card = n ∧ SetShatters C (↑W)})
    (hlearnable : {m : ℕ | IsPACLearner m ε δ C}.Nonempty) :
    (vcDim C - 1 : ℝ) / (32 * ε.toReal) ≤ sampleComplexity C ε δ := by
  have hmem := Nat.sInf_mem hlearnable
  exact sample_complexity_lower_bound_vcDim hε_pos hε_le hδ_lt hvc hbdd
    (IsPACLearner.toIsRPACLearner.{_, 0} hmem)

/-- Lower bound on randomized sample complexity in terms of `vcDim`.

If the VC dimension is at least `2` and finite, then
`(vcDim C - 1) / (32ε) ≤ rsampleComplexity C ε δ`,
provided the concept class is learnable by a randomized learner. -/
theorem rsampleComplexity_lower_bound_vcDim
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {C : ConceptClass α}
    {ε δ : ℝ≥0∞}
    (hε_pos : 0 < ε) (hε_le : ε ≤ ENNReal.ofReal (1 / 8))
    (hδ_lt : δ < ENNReal.ofReal (1 / 14))
    (hvc : 2 ≤ vcDim C)
    (hbdd : BddAbove {n : ℕ | ∃ W : Finset α, W.card = n ∧ SetShatters C (↑W)})
    (hlearnable : {m : ℕ | IsRPACLearner.{_, 0} m ε δ C}.Nonempty) :
    (vcDim C - 1 : ℝ) / (32 * ε.toReal) ≤ rsampleComplexity C ε δ := by
  have hmem := Nat.sInf_mem hlearnable
  exact sample_complexity_lower_bound_vcDim hε_pos hε_le hδ_lt hvc hbdd hmem

end Cslib.MachineLearning
