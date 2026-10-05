/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Measures supported on finite sets

For a measure that vanishes off a finite set, every set is null-measurable if
singletons are measurable. Finite support is preserved by finite products of
finite measures. These facts let sample-complexity arguments in learning
theory measure failure events of *arbitrary* (non-measurable) learners under
finitely supported adversarial distributions.

`HasFiniteSupport` records this property as a typeclass, with an instance for
finite products.

The [PFR project](https://github.com/teorth/pfr/blob/master/PFR/ForMathlib/Entropy/Measure.lean)
has an equivalent `ProbabilityTheory.FiniteSupport` class, expressed using an almost-everywhere
`Finset` witness.

## Main statements

- `MeasureTheory.HasFiniteSupport`: a measure vanishes off some finite set.
- `MeasureTheory.HasFiniteSupport.exists_eq_sum_smul_dirac`: on a space with measurable
  singletons, a measure with finite support is a finite sum of Dirac measures weighted by
  its singleton masses.
- `MeasureTheory.HasFiniteSupport.isFiniteMeasure`: a sigma-finite measure with finite
  support is finite.
- `MeasureTheory.NullMeasurableSet.of_hasFiniteSupport`: on a space with measurable
  singletons, every set is null-measurable for a measure with finite support,
  including finite products.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

/-- A measure vanishes off a finite set. -/
class HasFiniteSupport {α : Type*} [MeasurableSpace α] (μ : Measure α) : Prop where
  /-- Some finite set has null complement. -/
  exists_finite_measure_compl_zero : ∃ s : Set α, s.Finite ∧ μ sᶜ = 0

namespace Measure

open HasFiniteSupport

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The support of a measure. This is defined for any measure `μ`, but is most useful when `μ` has
finite support. -/
def supp (μ : Measure α) : Set α := ⋂₀ {s | μ sᶜ = 0}

lemma mem_supp_iff {x : α} : x ∈ μ.supp ↔ μ {x} ≠ 0 := by
  rw [supp, mem_sInter]
  contrapose!
  constructor
  · intro ⟨t, ht, hmem⟩
    exact μ.mono_null (singleton_subset_iff.mpr hmem) ht
  · intro h
    use {x}ᶜ
    simpa

lemma notMem_supp_iff {x : α} : x ∉ μ.supp ↔ μ {x} = 0 := not_iff_comm.mp mem_supp_iff.symm

lemma measure_singleton_inter_supp (x : α) : μ {x} = μ ({x} ∩ μ.supp) := by
  by_cases hx : x ∈ μ.supp
  · rw [Set.singleton_inter_of_mem hx]
  · simpa [singleton_inter_of_notMem hx] using notMem_supp_iff.mp hx

-- can `(s \ μ.supp).Countable` be removed?
lemma measure_inter_supp_of_countable {s : Set α} (h : (s \ μ.supp).Countable) :
    μ s = μ (s ∩ μ.supp) := by
  refine le_antisymm ?_ (μ.mono inter_subset_left)
  nth_grw 1 [← inter_union_sdiff s (μ.supp), measure_union_le]
  suffices μ (s \ μ.supp) = 0 by simp [this]
  rw [← (s \ μ.supp).biUnion_of_singleton, measure_biUnion_null_iff h]
  intro x ⟨_, hx⟩
  exact notMem_supp_iff.mp hx

variable [HasFiniteSupport μ]

lemma supp_finite : μ.supp.Finite := by
  obtain ⟨s, hs, hnull⟩ := exists_finite_measure_compl_zero (μ := μ)
  refine Set.Finite.subset hs <| sInter_subset_of_mem hnull

@[simp] lemma measure_supp_compl : μ μ.suppᶜ = 0 := by
  obtain ⟨s, hs, hnull⟩ := exists_finite_measure_compl_zero (μ := μ)
  have heq : μ.supp = ⋂₀ {t | t ⊆ s ∧ μ tᶜ = 0} := by
    refine subset_antisymm (sInter_subset_sInter fun _ ⟨_, h⟩ => h) ?_
    intro a h t (ht : μ tᶜ = 0)
    refine inter_subset_right <| h (s ∩ t) ⟨inter_subset_left, ?_⟩
    simp [compl_inter, hnull, ht]
  have hcount : {t | t ⊆ s ∧ μ tᶜ = 0}.Countable := (hs.powerset.subset <| by grind).countable
  rw [heq, compl_sInter, measure_sUnion_null_iff (hcount.image _)]
  rintro _ ⟨t, ⟨-, ht⟩, rfl⟩
  exact ht

omit [HasFiniteSupport μ] in
/-- The support of `μ` provides a canonical witness for the existential statement of
`HasFiniteSupport μ`. -/
theorem hasFiniteSupport_iff : HasFiniteSupport μ ↔ μ.supp.Finite ∧ μ μ.suppᶜ = 0 :=
  ⟨fun _ ↦ ⟨μ.supp_finite, μ.measure_supp_compl⟩, fun ⟨h, h'⟩ ↦ ⟨μ.supp, h, h'⟩⟩

lemma ae_mem_supp : ∀ᵐ (a : α) ∂μ, a ∈ μ.supp := μ.measure_supp_compl

/-- On a space with measurable singletons, a measure with finite support is a finite sum
of Dirac measures weighted by its singleton masses. This is `Measure.ae_mem_finset_iff`
applied to a finite support. Conversely, a measure of this form can be synthesised to have finite
support using `MeasureTheory.instHasFiniteSupportSum`, `MeasureTheory.instHasFiniteSupportSMul` and
`MeasureTheory.instHasFiniteSupportDirac`. -/
theorem exists_eq_sum_smul_dirac [MeasurableSingletonClass α] :
    μ = ∑ a ∈ μ.supp_finite.toFinset, μ {a} • Measure.dirac a := by
  simpa [← μ.ae_mem_finset_iff] using μ.ae_mem_supp

lemma measure_eq_measure_inter_supp {s : Set α} : μ s = μ (s ∩ μ.supp) := by
  refine le_antisymm ?_ (measure_mono inter_subset_left)
  nth_rw 1 [← inter_union_sdiff s (μ.supp)]
  convert measure_union_le (μ := μ) (s ∩ μ.supp) (s \ μ.supp)
  simp [measure_mono_null (sdiff_subset_compl ..) measure_supp_compl]

@[simp] lemma measure_supp : μ μ.supp = μ .univ := by
  simpa using measure_eq_measure_inter_supp (s := .univ) |>.symm

lemma supp_subset_iff {s : Set α} : μ.supp ⊆ s ↔ μ sᶜ = 0 := by
  refine ⟨?_, sInter_subset_of_mem (S := {s | μ sᶜ = 0})⟩
  rw [← le_zero_iff, ← measure_supp_compl (μ := μ)]
  exact (measure_mono <| compl_subset_compl.mpr ·)

lemma nullMeasurableSet_supp : NullMeasurableSet μ.supp μ :=
  compl_compl μ.supp ▸ (NullMeasurableSet.of_null measure_supp_compl).compl

theorem restrict_supp_eq : μ.restrict μ.supp = μ  := μ.restrict_eq_self_of_ae_mem μ.ae_mem_supp

end Measure

/-- A finite set has finite measure under a sigma-finite measure. TODO: delete once
[Mathlib PR 44381](https://github.com/leanprover-community/mathlib4/pull/44381) is available. -/
theorem _root_.Set.Finite.measure_lt_top_of_sigmaFinite {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SigmaFinite μ] {s : Set α} (hs : s.Finite) : μ s < ∞ := by
  simpa using measure_biUnion_lt_top hs
    (fun a _ ↦ measure_singleton_lt_top (μ := μ) (a := a))

/-- A sigma-finite measure with finite support is finite. -/
-- Try direct `IsFiniteMeasure` instances before deriving finiteness from finite support.
instance (priority := 100) HasFiniteSupport.isFiniteMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [HasFiniteSupport μ] [SigmaFinite μ] : IsFiniteMeasure μ where
  measure_univ_lt_top := by
    rw [← μ.measure_supp]
    exact μ.supp_finite.measure_lt_top_of_sigmaFinite

-- possibly the hypotheses here are too restrictive to be interesting
theorem IsFiniteMeasure.hasFiniteSupport_iff_of_countable {α : Type*} [Countable α]
    [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] :
    HasFiniteSupport μ ↔ NullMeasurableSet μ.supp μ ∧ μ.supp.Finite := by
  refine ⟨fun _ ↦ ⟨μ.nullMeasurableSet_supp, μ.supp_finite⟩, fun ⟨h, h'⟩ ↦ ⟨μ.supp, h', ?_⟩⟩
  simp [← ae_eq_univ, ae_eq_univ_iff_measure_eq h,
      μ.measure_inter_supp_of_countable (countable_univ.mono sdiff_subset)]

/-- On a space with measurable singletons, every set is null-measurable for a measure
with finite support. -/
theorem NullMeasurableSet.of_hasFiniteSupport {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure α} [HasFiniteSupport μ]
    (t : Set α) : NullMeasurableSet t μ := by
  obtain ⟨s, hs, hμ⟩ := HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ)
  rw [← inter_union_sdiff t s]
  exact (hs.subset inter_subset_right).measurableSet.nullMeasurableSet.union_null
    (measure_mono_null (sdiff_subset_compl t s) hμ)

theorem HasFiniteSupport.integrable {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [HasFiniteSupport μ] [IsFiniteMeasure μ] [NormedAddCommGroup β] (f : α → β) :
    Integrable f μ := by
  have : IntegrableOn f μ.supp μ := .of_finite μ.supp_finite
  rwa [IntegrableOn, μ.restrict_supp_eq] at this

instance instHasFiniteSupportOfFinite {α : Type*} [Finite α] [MeasurableSpace α] (μ : Measure α) :
    HasFiniteSupport μ where
  exists_finite_measure_compl_zero := by use Set.univ; simp

instance {α : Type*} [MeasurableSpace α] : HasFiniteSupport (0 : Measure α) := ⟨∅, by simp⟩

/-- The pushforward of finitely supported measure along an almost-everywhere measurable function
  is finitely supported so long as the image is null-measurable. See
  `MeasureTheory.instHasFiniteSupportMap` for an alternate version whose hypotheses can be found by
  instance synthesis. -/
theorem HasFiniteSupport.map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    [HasFiniteSupport μ] {f : α → β} (hf : AEMeasurable f μ)
    (hsupp : NullMeasurableSet (f '' μ.supp) (μ.map f)) :
    HasFiniteSupport (μ.map f) where
  exists_finite_measure_compl_zero := by
    use f '' μ.supp, μ.supp_finite.image f
    rw [Measure.map_apply₀ hf hsupp.compl,
      Set.preimage_compl]
    apply Measure.mono_null ?_ μ.measure_supp_compl
    exact compl_subset_compl_of_subset <| Set.subset_preimage_image f μ.supp

/-- A `HasFiniteSupport` instance on a pushforward measure. In particular, this synthesises
  `HasFiniteSupport (μ.map f)` for `f : ι → α` with the hypotheses
  `[Finite ι] [DiscreteMeasurableSpace ι] [MeasurableSingletonClass α]`. -/
instance instHasFiniteSupportMap {α β : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β] (μ : Measure α) [HasFiniteSupport μ]
    (f : α → β) : HasFiniteSupport (μ.map f) :=
  .map μ .of_discrete (μ.supp_finite.image f).measurableSet.nullMeasurableSet

instance instHasFiniteSupportAdd {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [HasFiniteSupport μ] [HasFiniteSupport ν] : HasFiniteSupport (μ + ν) where
  exists_finite_measure_compl_zero := by
    use μ.supp ∪ ν.supp, μ.supp_finite.union ν.supp_finite
    rw [compl_union, Measure.coe_add, Pi.add_apply, add_eq_zero]
    exact ⟨μ.mono_null Set.inter_subset_left μ.measure_supp_compl,
      ν.mono_null Set.inter_subset_right ν.measure_supp_compl⟩

instance instHasFiniteSupportSum {α ι : Type*} [MeasurableSpace α] (s : Finset ι)
    (μ : ι → Measure α) [∀ i, HasFiniteSupport (μ i)] : HasFiniteSupport (∑ i ∈ s, μ i) where
  exists_finite_measure_compl_zero := by
    refine ⟨⋃ i ∈ s, (μ i).supp, s.finite_toSet.biUnion ?_, ?_⟩
    · intro i _
      exact (μ i).supp_finite
    · simp_rw [compl_iUnion, Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_zero_iff]
      intro i h
      exact (μ i).mono_null (iInter₂_subset i h) (μ i).measure_supp_compl

instance instHasFiniteSupportSMul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [HasFiniteSupport μ] (c : ℝ≥0∞) : HasFiniteSupport (c • μ) := ⟨μ.supp, μ.supp_finite, by simp⟩

instance instHasFiniteSupportDirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (x : α) : HasFiniteSupport (Measure.dirac x) where
  exists_finite_measure_compl_zero := by
    use {x}, Set.finite_singleton x
    simp

instance {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, HasFiniteSupport (μ i)] [∀ i, IsFiniteMeasure (μ i)] :
    HasFiniteSupport (Measure.pi μ) where
  exists_finite_measure_compl_zero := by
    choose s hs hμ using fun i =>
      HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ i)
    refine ⟨univ.pi s, Finite.pi hs, ?_⟩
    refine measure_mono_null ?_
      (measure_iUnion_null fun i => Measure.pi_eval_preimage_null μ (hμ i))
    intro f hf
    simpa using hf

end MeasureTheory
