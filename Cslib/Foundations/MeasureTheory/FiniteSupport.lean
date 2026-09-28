/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Data.Fintype.Order

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

## Possible connections ...

- `MeasureTheory.Measure.ae_mem_finset_iff`: measures of this form can be represented as a sum
of dirac measures.

-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Typeclass for measures induced by their restriction to a finite set. -/
class HasFiniteSupport (μ : Measure α) where
  exists_finite_measure_compl_zero : ∃ s : Set α, s.Finite ∧ μ sᶜ = 0

namespace HasFiniteSupport

variable [HasFiniteSupport μ]

/-- Canonical representative for the existential statement
`HasFiniteSupport.exists_finite_measure_compl_zero`: see `HasFiniteSupport.supp_finite` and
`HasFiniteSupport.measure_supp_compl`. -/
def supp (μ : Measure α) [HasFiniteSupport μ] : Set α := ⋂₀ {s | μ sᶜ = 0}

lemma supp_finite : (supp μ).Finite := by
  obtain ⟨s, hs, hnull⟩ := exists_finite_measure_compl_zero (μ := μ)
  refine Set.Finite.subset hs <| sInter_subset_of_mem hnull

@[simp] lemma measure_supp_compl : μ (supp μ)ᶜ = 0 := by
  obtain ⟨s, hs, hnull⟩ := exists_finite_measure_compl_zero (μ := μ)
  have heq : supp μ = ⋂₀ {t | t ⊆ s ∧ μ tᶜ = 0} := by
    refine subset_antisymm (sInter_subset_sInter fun _ ⟨_, h⟩ => h) ?_
    intro a h t (ht : μ tᶜ = 0)
    refine inter_subset_right <| h (s ∩ t) ⟨inter_subset_left, ?_⟩
    simp [compl_inter, hnull, ht]
  have hcount : {t | t ⊆ s ∧ μ tᶜ = 0}.Countable := (hs.powerset.subset <| by grind).countable
  rw [heq, compl_sInter, measure_sUnion_null_iff (hcount.image _)]
  rintro _ ⟨t, ⟨-, ht⟩, rfl⟩
  exact ht

lemma measure_eq_measure_inter_supp {s : Set α} : μ s = μ (s ∩ supp μ) := by
  refine le_antisymm ?_ (measure_mono inter_subset_left)
  nth_rw 1 [← inter_union_sdiff s (supp μ)]
  convert measure_union_le (μ := μ) (s ∩ supp μ) (s \ supp μ)
  simp [measure_mono_null (sdiff_subset_compl ..) measure_supp_compl]

@[simp] lemma measure_supp : μ (supp μ) = μ .univ := by
  simpa using measure_eq_measure_inter_supp (s := .univ) |>.symm

lemma supp_subset_iff {s : Set α} : supp μ ⊆ s ↔ μ sᶜ = 0 := by
  refine ⟨?_, sInter_subset_of_mem (S := {s | μ sᶜ = 0})⟩
  rw [← le_zero_iff, ← measure_supp_compl (μ := μ)]
  exact (measure_mono <| compl_subset_compl.mpr ·)

lemma nullMeasurableSet_supp : NullMeasurableSet (μ := μ) (supp μ) :=
  compl_compl (supp μ) ▸ (NullMeasurableSet.of_null measure_supp_compl).compl

/-- See also `MeasureTheory.Measure.restrict_eq_self_of_ae_mem` for an alternate path to this
result (which would use that `μ (supp μ)ᶜ = 0`). -/
theorem eq_restrict_supp : μ = μ.restrict (supp μ) := by
  ext s hs
  simpa [μ.restrict_apply hs] using measure_eq_measure_inter_supp

/-- If `μ` vanishes off a finite set `s`, then every set is null-measurable
for `μ`: it splits as a finite (hence measurable) part inside `s` and a null
part outside. -/
theorem _root_.MeasureTheory.NullMeasurableSet.of_hasFiniteSupport [MeasurableSingletonClass α]
    (t : Set α) : NullMeasurableSet t μ := by
  rw [← inter_union_sdiff t (supp μ)]
  exact (supp_finite.subset inter_subset_right).measurableSet.nullMeasurableSet.union_null <|
    measure_mono_null (sdiff_subset_compl ..) measure_supp_compl

instance instIsFiniteMeasureOfSigmaFinite [SigmaFinite μ] : IsFiniteMeasure μ where
  measure_univ_lt_top := by
    suffices ∃ n, supp μ ⊆ spanningSets μ n from measure_supp (μ := μ) ▸
      measure_lt_top_mono (Classical.choose_spec this) (measure_spanningSets_lt_top _ _)
    use ⨆ x : supp μ, spanningSetsIndex μ x
    have : Finite (supp μ) := supp_finite.to_subtype
    intro x hx
    exact mem_spanningSets_of_index_le μ x <|
      Finite.le_ciSup (fun (x : supp μ) ↦ spanningSetsIndex μ x) ⟨x, hx⟩

instance {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] [∀ i, HasFiniteSupport (μ i)] :
    HasFiniteSupport (Measure.pi μ) where
  exists_finite_measure_compl_zero := by
    use univ.pi (fun i => supp (μ i)), Finite.pi (fun _ => supp_finite)
    refine Measure.mono_null ?_ <|
      measure_iUnion_null fun i => Measure.pi_eval_preimage_null μ (measure_supp_compl (μ := μ i))
    intro f hf
    simpa using hf

/-- If each factor `μ i` vanishes off a finite set `s i`, then every set is
null-measurable for the product measure. -/
example {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] [∀ i, MeasurableSingletonClass (X i)]
    [∀ i, HasFiniteSupport (μ i)] (t : Set (∀ i, X i)) : NullMeasurableSet t (Measure.pi μ) :=
  .of_hasFiniteSupport t

end HasFiniteSupport

end MeasureTheory
