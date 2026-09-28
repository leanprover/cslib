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
- `MeasureTheory.Measure.pi_compl_univ_pi_null`: a product measure vanishes
  off the product of supports.
- `MeasureTheory.NullMeasurableSet.pi_of_finite_compl_null`: every set is
  null-measurable for a product of measures with finite supports.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

/-- A measure vanishes off a finite set. -/
class HasFiniteSupport {α : Type*} [MeasurableSpace α] (μ : Measure α) : Prop where
  /-- Some finite set has null complement. -/
  exists_finite_measure_compl_zero : ∃ s : Set α, s.Finite ∧ μ sᶜ = 0

/-- If `μ` vanishes off a finite set `s`, then every set is null-measurable
for `μ`: it splits as a finite (hence measurable) part inside `s` and a null
part outside. -/
theorem NullMeasurableSet.of_finite_compl_null {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure α} {s : Set α} (hs : s.Finite)
    (hμ : μ sᶜ = 0) (t : Set α) : NullMeasurableSet t μ := by
  rw [← inter_union_sdiff t s]
  exact (hs.subset inter_subset_right).measurableSet.nullMeasurableSet.union_null
    (measure_mono_null (sdiff_subset_compl t s) hμ)

/-- Every set is null-measurable for a measure with finite support. -/
theorem NullMeasurableSet.of_hasFiniteSupport {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure α} [HasFiniteSupport μ]
    (t : Set α) : NullMeasurableSet t μ := by
  obtain ⟨s, hs, hμ⟩ := HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ)
  exact .of_finite_compl_null hs hμ t

section Pi

variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]

/-- If each factor `μ i` vanishes off `s i`, the product measure vanishes off
`Set.pi univ s`. -/
theorem Measure.pi_compl_univ_pi_null {s : ∀ i, Set (X i)} (hs : ∀ i, μ i (s i)ᶜ = 0) :
    Measure.pi μ (univ.pi s)ᶜ = 0 := by
  refine mono_null ?_
    (measure_iUnion_null fun i => Measure.pi_eval_preimage_null μ (hs i))
  intro f hf
  simpa using hf

instance [∀ i, HasFiniteSupport (μ i)] : HasFiniteSupport (Measure.pi μ) where
  exists_finite_measure_compl_zero := by
    choose s hs hμ using fun i =>
      HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ i)
    exact ⟨univ.pi s, Finite.pi hs, Measure.pi_compl_univ_pi_null μ hμ⟩

/-- If each factor `μ i` vanishes off a finite set `s i`, then every set is
null-measurable for the product measure. -/
theorem NullMeasurableSet.pi_of_finite_compl_null [∀ i, MeasurableSingletonClass (X i)]
    {s : ∀ i, Set (X i)} (hs : ∀ i, (s i).Finite) (hμ : ∀ i, μ i (s i)ᶜ = 0)
    (t : Set (∀ i, X i)) : NullMeasurableSet t (Measure.pi μ) :=
  .of_finite_compl_null (Finite.pi hs) (Measure.pi_compl_univ_pi_null μ hμ) t

end Pi

end MeasureTheory
