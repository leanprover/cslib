/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Thomas Waring
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

import all Mathlib.MeasureTheory.Constructions.Pi

/-! # Measures supported on finite sets

For a measure that vanishes off a finite set, every set is null-measurable if
singletons are measurable. Finite support is preserved by finite products. These facts let
sample-complexity arguments in learning theory measure failure events of *arbitrary*
(non-measurable) learners under finitely supported adversarial distributions.

`HasFiniteSupport` records this property as a typeclass, with an instance for
finite products.

The [PFR project](https://github.com/teorth/pfr/blob/master/PFR/ForMathlib/Entropy/Measure.lean)
has an equivalent `ProbabilityTheory.FiniteSupport` class, expressed using an almost-everywhere
`Finset` witness.

## Main statements

- `MeasureTheory.HasFiniteSupport`: a measure vanishes off some finite set.
- `MeasureTheory.HasFiniteSupport.exists_eq_sum_smul_dirac`: a measure with finite support is a
  finite sum of Dirac measures weighted by its singleton masses.
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

/-- Inside a finite measurable set `G`, a point `a ∈ G` has a minimal measurable
neighbourhood `A ⊆ G`: every measurable set contains `A` or is disjoint from it. -/
private theorem exists_minimal_measurableSet {α : Type*} [MeasurableSpace α] {G : Finset α}
    {a : α} (ha : a ∈ G) (hG : MeasurableSet (G : Set α)) :
    ∃ A : Finset α, A ⊆ G ∧ a ∈ A ∧ MeasurableSet (A : Set α) ∧ ∀ T, MeasurableSet T →
      (a ∈ T → (A : Set α) ⊆ T) ∧ (a ∉ T → Disjoint (A : Set α) T) := by
  classical
  obtain ⟨A, hA, hmin⟩ := (G.powerset.filter fun A : Finset α => a ∈ A ∧
    MeasurableSet (A : Set α)).exists_min_image Finset.card ⟨G, by simp [ha, hG]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA hmin
  -- splitting `A` along a measurable set leaves the part containing `a` equal to `A`
  have split (p : α → Prop) [DecidablePred p] (hp : p a)
      (hm : MeasurableSet ((A.filter p : Finset α) : Set α)) : ∀ x ∈ A, p x := fun x hx =>
    (Finset.mem_filter.mp ((Finset.eq_of_subset_of_card_le (Finset.filter_subset p A)
      (hmin _ ⟨(Finset.filter_subset _ _).trans hA.1, by simp [hA.2.1, hp], hm⟩)).symm ▸ hx)).2
  refine ⟨A, hA.1, hA.2.1, hA.2.2, fun T hT => ⟨fun h x hx => ?_, fun h => ?_⟩⟩
  · exact split (· ∈ T) h (by rw [Finset.coe_filter]; exact hA.2.2.inter hT) x hx
  · exact Set.disjoint_left.mpr fun x hx =>
      split (· ∉ T) h (by rw [Finset.coe_filter]; exact hA.2.2.diff hT) x hx

/-- A measure concentrated on a finite measurable set `G` is a weighted sum of Dirac masses
at points of `G`. -/
private theorem exists_eq_sum_of_finset {α : Type*} [MeasurableSpace α] (G : Finset α) :
    ∀ μ : Measure α, MeasurableSet (G : Set α) → μ (G : Set α)ᶜ = 0 →
      ∃ s ⊆ G, ∀ T, MeasurableSet T → μ T = ∑ a ∈ s, μ {a} * T.indicator 1 a := by
  classical
  induction G using Finset.strongInduction with
  | H G ih =>
  intro μ hG h0
  rcases G.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨∅, Finset.empty_subset _, fun T _ => by simp_all⟩
  -- split off the minimal measurable neighbourhood `A` of `a` and recurse on `G \ A`
  obtain ⟨A, hAG, haA, hAm, hAT⟩ := exists_minimal_measurableSet ha hG
  have hG'm : MeasurableSet ((G \ A : Finset α) : Set α) := by
    rw [Finset.coe_sdiff]; exact hG.diff hAm
  obtain ⟨s', hs'G, hs'⟩ := ih (G \ A) (Finset.sdiff_ssubset hAG ⟨a, haA⟩)
    (μ.restrict ((G \ A : Finset α) : Set α)) hG'm (by rw [Measure.restrict_apply' hG'm]; simp)
  refine ⟨insert a s', Finset.insert_subset ha (hs'G.trans Finset.sdiff_subset), fun T hT => ?_⟩
  rw [Finset.sum_insert fun h => (Finset.mem_sdiff.mp (hs'G h)).2 haA]
  have e1 : μ T = μ (T ∩ A) + μ.restrict ((G \ A : Finset α) : Set α) T := by
    rw [Measure.restrict_apply hT, ← measure_inter_conull (s := T) h0,
      ← Set.union_sdiff_cancel (Finset.coe_subset.mpr hAG), ← Finset.coe_sdiff,
      Set.inter_union_distrib_left]
    refine measure_union (Set.disjoint_left.mpr fun x hx hx' => ?_) (hT.inter hG'm)
    rw [Finset.coe_sdiff] at hx'
    exact hx'.2.2 hx.2
  have hsing : μ {a} = μ A := le_antisymm (measure_mono (Set.singleton_subset_iff.mpr haA)) <| by
    rw [← measure_toMeasurable {a}]
    exact measure_mono
      ((hAT _ (measurableSet_toMeasurable μ {a})).1 (subset_toMeasurable μ {a} rfl))
  have e2 : μ (T ∩ A) = μ {a} * T.indicator 1 a := by
    by_cases h : a ∈ T
    · rw [Set.inter_eq_right.mpr ((hAT T hT).1 h), hsing, Set.indicator_of_mem h]; simp
    · rw [Set.inter_comm, ((hAT T hT).2 h).inter_eq, Set.indicator_of_notMem h]; simp
  rw [e1, e2, hs' T hT]
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Measure.restrict_apply' hG'm, Set.inter_eq_left.mpr
    (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr (hs'G hb)))]

/-- A measure with finite support is a finite sum of Dirac measures weighted by its singleton
masses. -/
theorem HasFiniteSupport.exists_eq_sum_smul_dirac {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [HasFiniteSupport μ] :
    ∃ s : Finset α, μ = ∑ a ∈ s, μ {a} • Measure.dirac a := by
  obtain ⟨F, hF, hμ⟩ := HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ)
  -- the complement of a measurable null superset of `Fᶜ` is a finite measurable conull set
  have hfin : (toMeasurable μ Fᶜ)ᶜ.Finite :=
    hF.subset (Set.compl_subset_comm.mp (subset_toMeasurable μ Fᶜ))
  obtain ⟨s, -, hs⟩ := exists_eq_sum_of_finset hfin.toFinset μ
    (by rw [Set.Finite.coe_toFinset]; exact (measurableSet_toMeasurable μ Fᶜ).compl)
    (by simp [measure_toMeasurable, hμ])
  refine ⟨s, Measure.ext fun T hT => ?_⟩
  rw [hs T hT, FunLike.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => by rw [smul_apply, Measure.dirac_apply' _ hT, smul_eq_mul]

/-- A sigma-finite measure with finite support is finite. -/
-- Try direct `IsFiniteMeasure` instances before deriving finiteness from finite support.
instance (priority := 100) HasFiniteSupport.isFiniteMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [HasFiniteSupport μ] [SigmaFinite μ] : IsFiniteMeasure μ where
  measure_univ_lt_top := by
    obtain ⟨s, hs, hμ⟩ := HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ)
    rw [← union_compl_self s]
    exact measure_union_lt_top hs.measure_lt_top_of_sigmaFinite (by simp [hμ])

/-- On a space with measurable singletons, every set is null-measurable for a measure
with finite support. -/
theorem NullMeasurableSet.of_hasFiniteSupport {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure α} [HasFiniteSupport μ]
    (t : Set α) : NullMeasurableSet t μ := by
  obtain ⟨s, hs, hμ⟩ := HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ)
  rw [← inter_union_sdiff t s]
  exact (hs.subset inter_subset_right).measurableSet.nullMeasurableSet.union_null
    (measure_mono_null (sdiff_subset_compl t s) hμ)

/-- A cylinder over a null set is null for the product measure. This is
`Measure.pi_eval_preimage_null` without σ-finiteness. -/
theorem Measure.pi_eval_preimage_null' {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) {i : ι} {s : Set (X i)}
    (hs : μ i s = 0) : Measure.pi μ (Function.eval i ⁻¹' s) = 0 := by
  classical
  obtain ⟨t, hst, htm, hμt⟩ := exists_measurable_superset_of_null hs
  refine measure_mono_null (preimage_mono hst) ?_
  have hm : MeasurableSet (pi univ (Function.update (fun j => (univ : Set (X j))) i t)) := by
    rw [univ_pi_update_univ]; exact measurable_pi_apply i htm
  rw [← univ_pi_update_univ, Measure.pi, toMeasure_apply _ _ hm]
  refine le_antisymm ((OuterMeasure.pi_pi_le _ _).trans ?_) zero_le
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hμt])]

instance {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, HasFiniteSupport (μ i)] :
    HasFiniteSupport (Measure.pi μ) where
  exists_finite_measure_compl_zero := by
    choose s hs hμ using fun i =>
      HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ i)
    refine ⟨univ.pi s, Finite.pi hs, ?_⟩
    refine measure_mono_null ?_
      (measure_iUnion_null fun i => Measure.pi_eval_preimage_null' μ (hμ i))
    intro f hf
    simpa using hf

end MeasureTheory
