/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Measures supported on finite sets

A measure that vanishes off a finite set behaves like a discrete measure:
every set is null-measurable, and this transfers to finite products. These
facts let sample-complexity arguments in learning theory measure failure
events of *arbitrary* (non-measurable) learners under finitely supported
adversarial distributions.

## Main statements

- `MeasureTheory.NullMeasurableSet.of_finite_compl_null`: every set is
  null-measurable for a measure vanishing off a finite set.
- `MeasureTheory.Measure.pi_compl_univ_pi_null`: a product measure vanishes
  off the product of supports.
- `MeasureTheory.NullMeasurableSet.pi_of_finite_compl_null`: every set is
  null-measurable for a product of measures with finite supports.
- `MeasureTheory.measurableSet_setOf_mem_range`: the set of tuples hitting a
  given point is measurable.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

section Base

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure α}

/-- If `μ` vanishes off a finite set `s`, then every set is null-measurable
for `μ`: it splits as a finite (hence measurable) part inside `s` and a null
part outside. -/
theorem NullMeasurableSet.of_finite_compl_null {s : Set α} (hs : s.Finite)
    (hμ : μ sᶜ = 0) (t : Set α) : NullMeasurableSet t μ := by
  rw [← inter_union_sdiff t s]
  exact (hs.subset inter_subset_right).measurableSet.nullMeasurableSet.union
    (.of_null (measure_mono_null (fun _ hx => hx.2) hμ))

end Base

section Pi

variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]

/-- If each factor `μ i` vanishes off `s i`, the product measure vanishes off
`Set.pi univ s`. -/
theorem Measure.pi_compl_univ_pi_null {s : ∀ i, Set (X i)} (hs : ∀ i, μ i (s i)ᶜ = 0) :
    Measure.pi μ (univ.pi s)ᶜ = 0 := by
  refine measure_mono_null ?_
    (measure_iUnion_null fun i => Measure.pi_eval_preimage_null (μ := μ) (hs i))
  intro f hf
  simp only [mem_compl_iff, mem_univ_pi, not_forall] at hf
  simpa using hf

/-- If each factor `μ i` vanishes off a finite set `s i`, then every set is
null-measurable for the product measure. -/
theorem NullMeasurableSet.pi_of_finite_compl_null [∀ i, MeasurableSingletonClass (X i)]
    {s : ∀ i, Set (X i)} (hs : ∀ i, (s i).Finite) (hμ : ∀ i, μ i (s i)ᶜ = 0)
    (t : Set (∀ i, X i)) : NullMeasurableSet t (Measure.pi μ) :=
  .of_finite_compl_null (Finite.pi hs) (Measure.pi_compl_univ_pi_null μ hμ) t

end Pi

/-- The set of tuples `f : ι → β` taking the value `b` somewhere is
measurable, being a countable union of coordinate preimages. -/
theorem measurableSet_setOf_mem_range {ι β : Type*} [Countable ι] [MeasurableSpace β]
    [MeasurableSingletonClass β] (b : β) :
    MeasurableSet {f : ι → β | b ∈ range f} := by
  have : {f : ι → β | b ∈ range f} = ⋃ i, Function.eval i ⁻¹' {b} := by ext f; simp
  rw [this]
  exact MeasurableSet.iUnion fun i => measurable_pi_apply i (measurableSet_singleton b)

end MeasureTheory
