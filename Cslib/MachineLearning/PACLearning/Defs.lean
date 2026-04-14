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
introduced by Valiant [Valiant1984], generalized to an arbitrary label type `β`
and parameterized by a family of distributions `𝒟` on `α × β`.

A concept class `C` over domain `α` with labels in `β` is a collection of
functions `α → β`. A learning algorithm receives a labeled sample drawn i.i.d.
from an unknown joint distribution `D` on `α × β` and must produce a hypothesis
whose 0-1 error is within `ε` of the best concept in `C`, with probability at
least `1 - δ`.

The single definition `IsPACLearnerFor` captures the realizable, agnostic, and
noise-tolerant settings by varying the distribution family `𝒟`:

- **Agnostic** [Haussler1992]: `𝒟 = Set.univ` — the learner must work for all distributions.
- **Realizable**: `𝒟` consists of pushforwards of arbitrary probability measures
  `P` on `α` along the graph `x ↦ (x, c x)` of some concept `c ∈ C`, so that
  `optimalError D C = 0`.
- **Noise-tolerant** [AngluinLaird1988]: `𝒟` consists of noisy versions of realizable
  distributions, where each label is corrupted independently with some probability `η`.

The accuracy and confidence parameters `ε` and `δ` are elements of the subtype
`Set.Ioo (0 : ℝ≥0) 1`, which bundles the value together with the proof that it
lies in the open interval `(0, 1)`, ensuring the learning condition is non-vacuous.

## Main definitions

- `ConceptClass`: a set of functions `α → β` (classifiers).
- `LabeledSample`: a finite sequence of `(point, label)` pairs.
- `Learner`: a function from labeled samples to hypotheses.
- `error`: the 0-1 error of a hypothesis under a joint distribution.
- `optimalError`: the infimum of `error` over a concept class.
- `IsPACLearnerFor`: deterministic `(ε, δ)`-PAC learner over a distribution family.
- `IsRPACLearnerFor`: randomized variant of `IsPACLearnerFor`.
- `IsPACLearnable`: a concept class is PAC learnable if `IsPACLearnerFor` holds for
  all `ε, δ : Set.Ioo (0 : ℝ≥0) 1` with some sample size `m`.
- `IsRPACLearnable`: randomized variant of `IsPACLearnable`.
- `sampleComplexity`, `rsampleComplexity`: deterministic/randomized sample complexity.

## Binary classification

When `β = Bool`, concepts correspond to subsets of `α`. The section
*Binary Classification* provides:

- `hypothesisError`: the symmetric-difference error `P(h ∆ c)`.
- `falsePositiveError`, `falseNegativeError`: its decomposition.
- `hypothesisError_eq_add`: the decomposition theorem.
- `error_map_eq_hypothesisError`: bridge between the general `error` and
  the binary `hypothesisError` under a realizable distribution.

## Main statements

- `IsPACLearnerFor.toIsRPACLearnerFor`: every deterministic PAC learner is a
  randomized one (via the trivial randomness space `PUnit`).
- `IsPACLearnerFor.mono`: monotonicity in the distribution family `𝒟` — a learner
  that works for `𝒟'` also works for any `𝒟 ⊆ 𝒟'`.
- `IsPACLearnable.toIsRPACLearnable`: deterministic learnability implies randomized.
- `hypothesisError_eq_add`: total error = false positive + false negative.

## References

* [L. G. Valiant, *A Theory of the Learnable*][Valiant1984]
* [A. Ehrenfeucht, D. Haussler, M. Kearns, L. Valiant,
  *A General Lower Bound on the Number of Examples Needed for Learning*][EHKV1989]
* [M. J. Kearns, U. V. Vazirani,
  *An Introduction to Computational Learning Theory*][KearnsVazirani1994]
* [D. Haussler, *Decision Theoretic Generalizations of the PAC Model for Neural Net
  and Other Learning Applications*][Haussler1992]
* [D. Angluin, P. Laird, *Learning from Noisy Examples*][AngluinLaird1988]
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning

/-! ### Core Definitions -/

/-- A *concept class* over domain `α` with label type `β` is a set of functions `α → β`.
For binary classification (`β = Bool`), this is equivalent to a collection of subsets of `α`
via the characteristic function. -/
abbrev ConceptClass (α β : Type*) := Set (α → β)

/-- A *labeled sample* of size `m` over domain `α` with label type `β` is a finite sequence
of `(point, label)` pairs. -/
abbrev LabeledSample (α β : Type*) (m : ℕ) := Fin m → (α × β)

/-- A *learner* using `m` samples is a function that takes a labeled sample and produces
a hypothesis (a function from the domain to the label type). -/
abbrev Learner (α β : Type*) (m : ℕ) := LabeledSample α β m → (α → β)

/-- The *prediction error* (0-1 loss) of a hypothesis `h` under a joint distribution `D`
on `α × β`, defined as the probability that the prediction disagrees with the label:
`D({(x, y) | h(x) ≠ y})`. -/
noncomputable def error {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (D : Measure (α × β)) (h : α → β) : ℝ≥0∞ :=
  D {p : α × β | h p.1 ≠ p.2}

/-- The *optimal error* of a concept class `C` under a joint distribution `D`, defined as the
infimum of `error D c` over all concepts `c ∈ C`. When `C` is empty this is `⊤`, making the
PAC learning condition vacuously true. -/
noncomputable def optimalError {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (D : Measure (α × β)) (C : ConceptClass α β) : ℝ≥0∞ :=
  ⨅ c ∈ C, error D c

variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### PAC Learners -/

/-- `IsPACLearnerFor m ε δ C 𝒟` asserts that there exists a learner using `m` samples
that is `(ε, δ)`-correct for the concept class `C` over the distribution family `𝒟`: for every
probability measure `D ∈ 𝒟` on `α × β`, the probability (over i.i.d. samples from `D`) that
the learner's hypothesis has error exceeding `opt_C(D) + ε` is at most `δ`.

The parameters `ε` and `δ` are elements of `Set.Ioo (0 : ℝ≥0) 1`, bundling the value with
the proof that it lies in `(0, 1)`. This ensures the condition is non-vacuous:
`ε < 1` prevents the error threshold from exceeding the maximum possible error under a
probability measure, and `δ < 1` prevents the confidence bound from being trivially
satisfied. -/
def IsPACLearnerFor (m : ℕ) (ε δ : Set.Ioo (0 : ℝ≥0) 1)
    (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∃ A : Learner α β m,
    ∀ (D : Measure (α × β)) [IsProbabilityMeasure D], D ∈ 𝒟 →
      (Measure.pi (fun _ : Fin m => D))
        {S : LabeledSample α β m |
          error D (A S) > optimalError D C + ↑ε.val} ≤ ↑δ.val

/-- `IsRPACLearnerFor m ε δ C 𝒟` asserts that there exists a *randomized* learner using
`m` samples that is `(ε, δ)`-correct for the concept class `C` over the distribution family
`𝒟`. A randomized learner draws internal randomness `ω` from a probability space `(Ω, Q)` and
acts as the deterministic learner `A(ω)`.

For every probability measure `D ∈ 𝒟`, the failure probability function
`ω ↦ D^m{S | error(A(ω)(S)) > opt_C(D) + ε}` must be `Q`-a.e. measurable, and its
expectation over `ω` must be at most `δ`.

The parameters `ε` and `δ` are elements of `Set.Ioo (0 : ℝ≥0) 1`.

A deterministic learner (`IsPACLearnerFor`) is the special case `Ω = PUnit`;
see `IsPACLearnerFor.toIsRPACLearnerFor`. -/
def IsRPACLearnerFor (m : ℕ) (ε δ : Set.Ioo (0 : ℝ≥0) 1)
    (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∃ (Ω : Type*) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
    (A : Ω → Learner α β m),
    ∀ (D : Measure (α × β)) [IsProbabilityMeasure D], D ∈ 𝒟 →
      AEMeasurable (fun ω => (Measure.pi (fun _ : Fin m => D))
        {S : LabeledSample α β m |
          error D ((A ω) S) > optimalError D C + ↑ε.val}) Q ∧
      ∫⁻ ω, (Measure.pi (fun _ : Fin m => D))
        {S : LabeledSample α β m |
          error D ((A ω) S) > optimalError D C + ↑ε.val} ∂Q ≤ ↑δ.val

/-- Every deterministic PAC learner is in particular a randomized PAC learner
(with the trivial one-point randomness space `PUnit`). -/
theorem IsPACLearnerFor.toIsRPACLearnerFor {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : IsPACLearnerFor m ε δ C 𝒟) :
    IsRPACLearnerFor m ε δ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  refine ⟨PUnit, inferInstance, Measure.dirac PUnit.unit, inferInstance, fun _ => A, ?_⟩
  intro D _ hD
  exact ⟨measurable_const.aemeasurable, by
    simp only [gt_iff_lt, lintegral_const, measure_univ, mul_one]; exact hA D hD⟩

/-- A PAC learner for a larger distribution family `𝒟'` is also a PAC learner for any
subfamily `𝒟 ⊆ 𝒟'`. -/
theorem IsPACLearnerFor.mono {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass α β} {𝒟 𝒟' : Set (Measure (α × β))}
    (h𝒟 : 𝒟 ⊆ 𝒟') (h : IsPACLearnerFor m ε δ C 𝒟') :
    IsPACLearnerFor m ε δ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, fun D inst hD => @hA D inst (h𝒟 hD)⟩

/-! ### PAC Learnability -/

/-- A concept class `C` is *PAC learnable* over the distribution family `𝒟` if for every
accuracy `ε ∈ (0, 1)` and confidence `δ ∈ (0, 1)`, there exists a sample size `m` admitting
a deterministic `(ε, δ)`-PAC learner for `C`. Here `ε` and `δ` are elements of the subtype
`Set.Ioo (0 : ℝ≥0) 1`. -/
def IsPACLearnable (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∀ (ε δ : Set.Ioo (0 : ℝ≥0) 1),
    ∃ m, IsPACLearnerFor m ε δ C 𝒟

/-- A concept class `C` is *randomized PAC learnable* over the distribution family `𝒟` if for
every accuracy `ε ∈ (0, 1)` and confidence `δ ∈ (0, 1)`, there exists a sample size `m`
admitting a randomized `(ε, δ)`-PAC learner for `C`. Here `ε` and `δ` are elements of the
subtype `Set.Ioo (0 : ℝ≥0) 1`. -/
def IsRPACLearnable (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∀ (ε δ : Set.Ioo (0 : ℝ≥0) 1),
    ∃ m, IsRPACLearnerFor.{_, _, 0} m ε δ C 𝒟

/-- Deterministic PAC learnability implies randomized PAC learnability. -/
theorem IsPACLearnable.toIsRPACLearnable {C : ConceptClass α β}
    {𝒟 : Set (Measure (α × β))} (h : IsPACLearnable C 𝒟) :
    IsRPACLearnable C 𝒟 := by
  intro ε δ
  obtain ⟨m, hm⟩ := h ε δ
  exact ⟨m, hm.toIsRPACLearnerFor⟩

/-! ### Sample Complexity -/

/-- The *deterministic sample complexity* of a concept class `C` at accuracy `ε ∈ (0, 1)` and
confidence `δ ∈ (0, 1)` over distribution family `𝒟` is the smallest sample size `m` admitting
a deterministic `(ε, δ)`-PAC learner for `C`. Here `ε` and `δ` are elements of the subtype
`Set.Ioo (0 : ℝ≥0) 1`.

**Caveat**: because `sInf` on `ℕ` returns `0` for the empty set, this definition returns `0`
when no deterministic learner exists (e.g., when `C` has infinite VC dimension). It is only
meaningful when the defining set `{m | IsPACLearnerFor m ε δ C 𝒟}` is nonempty. -/
noncomputable def sampleComplexity (C : ConceptClass α β) (ε δ : Set.Ioo (0 : ℝ≥0) 1)
    (𝒟 : Set (Measure (α × β))) : ℕ :=
  sInf {m : ℕ | IsPACLearnerFor m ε δ C 𝒟}

/-- The *randomized sample complexity* of a concept class `C` at accuracy `ε ∈ (0, 1)` and
confidence `δ ∈ (0, 1)` over distribution family `𝒟` is the smallest sample size `m` admitting
a randomized `(ε, δ)`-PAC learner for `C`. Here `ε` and `δ` are elements of the subtype
`Set.Ioo (0 : ℝ≥0) 1`.

The universe of the randomness space `Ω` is pinned to `Type 0` (via `.{_, _, 0}`) so that the
`sInf` is taken over a definite set; without the pin the existential quantifier over `Ω : Type*`
would range over all universe levels, making the set ill-defined.

**Caveat**: because `sInf` on `ℕ` returns `0` for the empty set, this definition returns `0`
when no randomized learner exists. It is only meaningful when the defining set is nonempty. -/
noncomputable def rsampleComplexity (C : ConceptClass α β) (ε δ : Set.Ioo (0 : ℝ≥0) 1)
    (𝒟 : Set (Measure (α × β))) : ℕ :=
  sInf {m : ℕ | IsRPACLearnerFor.{_, _, 0} m ε δ C 𝒟}

/-! ### Binary Classification

When `β = Bool`, concepts correspond to subsets of `α` via the characteristic function.
The symmetric-difference error `P(h ∆ c)` is the natural error metric, and it decomposes
into false positive and false negative components.

The bridge lemma `error_map_eq_hypothesisError` connects the general `error` on `α × Bool`
to the binary `hypothesisError` on `α`, showing they coincide for realizable distributions. -/

/-- The *symmetric-difference error* of a hypothesis `h` with respect to a target concept `c`
(both viewed as subsets of `α`) under distribution `P`, defined as `P(h ∆ c)`. -/
noncomputable def hypothesisError {α : Type*} [MeasurableSpace α] (P : Measure α)
    (h c : Set α) : ℝ≥0∞ :=
  P (symmDiff h c)

/-- The *false positive error* `P(h \ c)` — points classified positive but not in the
concept. -/
noncomputable def falsePositiveError {α : Type*} [MeasurableSpace α] (P : Measure α)
    (h c : Set α) : ℝ≥0∞ :=
  P (h \ c)

/-- The *false negative error* `P(c \ h)` — points in the concept but classified negative. -/
noncomputable def falseNegativeError {α : Type*} [MeasurableSpace α] (P : Measure α)
    (h c : Set α) : ℝ≥0∞ :=
  P (c \ h)

/-- The total hypothesis error decomposes as the sum of false positive and false negative
errors, since `h ∆ c = (h \ c) ∪ (c \ h)` is a disjoint union. -/
theorem hypothesisError_eq_add {α : Type*} [MeasurableSpace α] {P : Measure α}
    {h c : Set α} (hh : MeasurableSet h) (hc : MeasurableSet c) :
    hypothesisError P h c = falsePositiveError P h c + falseNegativeError P h c := by
  simp only [hypothesisError, falsePositiveError, falseNegativeError, symmDiff_def, sup_eq_union]
  exact measure_union disjoint_sdiff_sdiff (hc.diff hh)

open Classical in
/-- Under a realizable distribution `P.map (x ↦ (x, c(x)))`, the general 0-1 `error`
coincides with the binary `hypothesisError P h c`, where `h` and `c` are viewed as subsets
of `α` via the characteristic function `decide (· ∈ ·)`. -/
theorem error_map_eq_hypothesisError {α : Type*} [MeasurableSpace α] (P : Measure α)
    (h c : Set α) (hh : MeasurableSet h) (hc : MeasurableSet c) :
    error (P.map (fun x => (x, decide (x ∈ c)))) (fun x => decide (x ∈ h)) =
    hypothesisError P h c := by
  simp only [error, hypothesisError]
  have hf : Measurable (fun x => (x, decide (x ∈ c))) :=
    Measurable.prodMk measurable_id
      (measurable_to_bool (by convert hc using 1; ext x; simp [decide_eq_true_eq]))
  rw [Measure.map_apply_of_aemeasurable hf.aemeasurable]
  · congr 1; ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, symmDiff_def, sup_eq_union,
      Set.mem_union, Set.mem_diff]
    by_cases hx : x ∈ h <;> by_cases hcx : x ∈ c <;> simp_all
  · convert (hh.prod (measurableSet_singleton false)).union
      (hh.compl.prod (measurableSet_singleton true)) using 1
    ext ⟨x, b⟩; cases b <;> simp

end Cslib.MachineLearning
