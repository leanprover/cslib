/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Thomas Waring
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

`HasFiniteSupport` records this property as a typeclass, with an instance for
finite products.

## Main statements

- `MeasureTheory.HasFiniteSupport`: a measure vanishes off some finite set.
- `MeasureTheory.NullMeasurableSet.of_hasFiniteSupport`: every set is
  null-measurable for a measure with finite support, including finite products.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

/-- A measure vanishes off a finite set. -/
class HasFiniteSupport {α : Type*} [MeasurableSpace α] (μ : Measure α) : Prop where
  /-- Some finite set has null complement. -/
  exists_finite_measure_compl_zero : ∃ s : Set α, s.Finite ∧ μ sᶜ = 0

/-- Every set is null-measurable for a measure with finite support. -/
theorem NullMeasurableSet.of_hasFiniteSupport {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure α} [HasFiniteSupport μ]
    (t : Set α) : NullMeasurableSet t μ := by
  obtain ⟨s, hs, hμ⟩ := HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ)
  rw [← inter_union_sdiff t s]
  exact (hs.subset inter_subset_right).measurableSet.nullMeasurableSet.union_null
    (measure_mono_null (sdiff_subset_compl t s) hμ)

section Pi

variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]

instance [∀ i, HasFiniteSupport (μ i)] : HasFiniteSupport (Measure.pi μ) where
  exists_finite_measure_compl_zero := by
    choose s hs hμ using fun i =>
      HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ i)
    refine ⟨univ.pi s, Finite.pi hs, ?_⟩
    refine measure_mono_null ?_
      (measure_iUnion_null fun i => Measure.pi_eval_preimage_null μ (hμ i))
    intro f hf
    simpa using hf

end Pi

end MeasureTheory
