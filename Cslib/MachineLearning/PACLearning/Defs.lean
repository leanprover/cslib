/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Order.SymmDiff

@[expose] public section

/-! # PAC Learning

This file defines the Probably Approximately Correct (PAC) learning model
introduced by Valiant [Valiant1984]. A concept class `C` over a domain `α` is a
collection of subsets of `α`. A learning algorithm receives a labeled sample
drawn i.i.d. from an unknown distribution and must produce a hypothesis that,
with high probability, has low error with respect to the true concept.

## Main definitions

- `ConceptClass`: a concept class over domain `α`, i.e., a set of subsets.
- `LabeledSample`: a finite sequence of (point, label) pairs.
- `sampleOf`: constructs a labeled sample from a sequence of points and a concept.
- `hypothesisError`: the error of a hypothesis with respect to a concept under a
  distribution, defined as the measure of the symmetric difference.
- `Learner`: a function from labeled samples to hypotheses.
- `IsPACLearner`: the property that a deterministic learner produces a hypothesis
  with error at most `ε` with probability at least `1 - δ`, for every distribution
  and concept from the class.
- `IsRPACLearner`: the randomized variant, where the learner draws internal
  randomness from a probability space `(Ω, Q)`.
- `sampleComplexity`: the smallest sample size admitting a deterministic PAC learner.
- `rsampleComplexity`: the smallest sample size admitting a randomized PAC learner.

## Main statements

- `IsPACLearner.toIsRPACLearner`: every deterministic PAC learner is in particular
  a randomized PAC learner (with the trivial randomness space `PUnit`).

## References

* [L. G. Valiant, *A Theory of the Learnable*][Valiant1984]
* [A. Ehrenfeucht, D. Haussler, M. Kearns, L. Valiant,
  *A General Lower Bound on the Number of Examples Needed for Learning*][EHKV1989]
-/

open MeasureTheory Set
open scoped ENNReal

namespace Cslib.MachineLearning

/-- A *concept class* over domain `α` is a collection of subsets of `α`. Each subset represents
a concept (i.e., a binary classifier). -/
abbrev ConceptClass (α : Type*) := Set (Set α)

/-- A *labeled sample* of size `m` over domain `α` is a sequence of `(point, label)` pairs. -/
abbrev LabeledSample (α : Type*) (m : ℕ) := Fin m → (α × Bool)

open Classical in
/-- Construct a labeled sample from a sequence of points `xs` and a concept `c`.
Each point is labeled `true` if it belongs to the concept and `false` otherwise. -/
noncomputable def sampleOf {α : Type*} {m : ℕ} (c : Set α) (xs : Fin m → α) :
    LabeledSample α m :=
  fun i => (xs i, decide (xs i ∈ c))

/-- The *error* of a hypothesis `h` with respect to a target concept `c` under distribution `P`,
defined as the measure of their symmetric difference `h ∆ c`. -/
noncomputable def hypothesisError {α : Type*} [MeasurableSpace α] (P : Measure α)
    (h c : Set α) : ℝ≥0∞ :=
  P (symmDiff h c)

/-- A learner using `m` samples is a function that takes a labeled sample of size `m` and produces
a hypothesis (a subset of the domain). -/
abbrev Learner (α : Type*) (m : ℕ) := LabeledSample α m → Set α

variable {α : Type*} [MeasurableSpace α]

/-- `IsPACLearner m ε δ C` asserts that there exists a learner using `m` samples that is
`(ε, δ)`-correct for the concept class `C`: for every probability measure `P` on `α` and every
target concept `c ∈ C`, the probability (over i.i.d. samples from `P`) that the learner's
hypothesis has error greater than `ε` is at most `δ`.

More precisely, we require that the set of sample-vectors whose induced hypothesis has error
exceeding `ε` has `P^m`-measure at most `δ`. -/
def IsPACLearner (m : ℕ) (ε δ : ℝ≥0∞) (C : ConceptClass α) : Prop :=
  ∃ A : Learner α m,
    ∀ (P : Measure α) [IsProbabilityMeasure P],
    ∀ c ∈ C,
      (Measure.pi (fun _ : Fin m => P))
        {xs : Fin m → α | hypothesisError P (A (sampleOf c xs)) c > ε} ≤ δ

/-- `IsRPACLearner m ε δ C` asserts that there exists a *randomized* learner using `m` samples
that is `(ε, δ)`-correct for the concept class `C`. A randomized learner draws internal
randomness `ω` from a probability space `(Ω, Q)` and then acts as the deterministic learner
`A(ω)`.

For every probability measure `P` on `α` and every target concept `c ∈ C`, the failure
probability function `ω ↦ P^m{xs | error(A(ω)(xs), c) > ε}` must be `Q`-a.e. measurable,
and its expectation over `ω` must be at most `δ`.

A deterministic PAC learner (`IsPACLearner`) is the special case `Ω = PUnit`;
see `IsPACLearner.toIsRPACLearner`. -/
def IsRPACLearner (m : ℕ) (ε δ : ℝ≥0∞) (C : ConceptClass α) : Prop :=
  ∃ (Ω : Type*) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
    (A : Ω → Learner α m),
    ∀ (P : Measure α) [IsProbabilityMeasure P],
    ∀ c ∈ C,
      AEMeasurable (fun ω => (Measure.pi (fun _ : Fin m => P))
        {xs : Fin m → α | hypothesisError P ((A ω) (sampleOf c xs)) c > ε}) Q ∧
      ∫⁻ ω, (Measure.pi (fun _ : Fin m => P))
        {xs : Fin m → α | hypothesisError P ((A ω) (sampleOf c xs)) c > ε} ∂Q ≤ δ

/-- Every deterministic PAC learner is in particular a randomized PAC learner
(with the trivial one-point randomness space `PUnit`). -/
theorem IsPACLearner.toIsRPACLearner {m : ℕ} {ε δ : ℝ≥0∞} {C : ConceptClass α}
    (h : IsPACLearner m ε δ C) : IsRPACLearner m ε δ C := by
  obtain ⟨A, hA⟩ := h
  refine ⟨PUnit, inferInstance, Measure.dirac PUnit.unit, inferInstance, fun _ => A, ?_⟩
  intro P _ c hc
  exact ⟨measurable_const.aemeasurable, by
    simp only [gt_iff_lt, lintegral_const, measure_univ, mul_one]; exact hA P c hc⟩

/-- The *deterministic sample complexity* of a concept class `C` at accuracy `ε` and confidence `δ`
is the smallest sample size `m` such that a deterministic `(ε, δ)`-PAC learner for `C` exists
using `m` samples. See also `rsampleComplexity` for the randomized variant.

**Caveat**: because `sInf` on `ℕ` returns `0` for the empty set, this definition returns `0` when
no deterministic learner exists (e.g., when `C` has infinite VC dimension). It is only meaningful
when the defining set `{m | IsPACLearner m ε δ C}` is nonempty. -/
noncomputable def sampleComplexity (C : ConceptClass α) (ε δ : ℝ≥0∞) : ℕ :=
  sInf {m : ℕ | IsPACLearner m ε δ C}

/-- The *randomized sample complexity* of a concept class `C` at accuracy `ε` and confidence `δ`
is the smallest sample size `m` such that a randomized `(ε, δ)`-PAC learner for `C` exists
using `m` samples. This is at most `sampleComplexity C ε δ` since every deterministic learner
is also a randomized learner (see `IsPACLearner.toIsRPACLearner`).

The universe of the randomness space `Ω` is pinned to `Type 0` (via `.{_, 0}`) so that the
`sInf` is taken over a definite set; without the pin the existential quantifier over `Ω : Type*`
would range over all universe levels, making the set ill-defined.

**Caveat**: because `sInf` on `ℕ` returns `0` for the empty set, this definition returns `0` when
no randomized learner exists. It is only meaningful when the defining set is nonempty. -/
noncomputable def rsampleComplexity (C : ConceptClass α) (ε δ : ℝ≥0∞) : ℕ :=
  sInf {m : ℕ | IsRPACLearner.{_, 0} m ε δ C}

end Cslib.MachineLearning
