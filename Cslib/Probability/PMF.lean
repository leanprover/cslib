/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Probability.Distributions.Uniform

/-!
# PMF Utilities

## NB: This module is temporary

Everything here is a general PMF bind/pure lemma with no dependence on
any domain-specific structure. It should be upstreamed to Mathlib
(likely `Mathlib.Probability.ProbabilityMassFunction.Monad` or a new
`Mathlib.Probability.ProbabilityMassFunction.Prod`). Once accepted
upstream, this file should be deleted and its consumers should import
the Mathlib module instead.

## Main results

- `Cslib.Probability.PMF.bind_pair_apply`: the "pairing" bind at `(a, b)` equals `p a * f a b`
- `Cslib.Probability.PMF.bind_pair_tsum_fst`: marginalizing over the first component
- `Cslib.Probability.PMF.uniformOfFintype_map_equiv`:
  a uniform distribution is invariant under equivalence
- `Cslib.Probability.PMF.uniformOfFintype_prod`: a uniform pair is two independent uniform samples
- `Cslib.Probability.PMF.toOuterMeasure_bind_failure_le`: errors compose through a
  state-dependent continuation without independence assumptions
- `Cslib.Probability.PMF.posteriorDist`: the posterior as a `PMF`
- `Cslib.Probability.PMF.posteriorDist_eq_prior_of_outputIndist`:
  if the output distribution does not depend on the input, conditioning does
  not change the prior
-/

@[expose] public section

namespace Cslib.Probability.PMF

open ENNReal

universe u v
variable {α : Type u} {β : Type v}

/-- Real-valued probability masses are summable, even on an infinite ambient type. -/
theorem summable_toReal (p : PMF α) : Summable (fun a => (p a).toReal) :=
  ENNReal.summable_toReal p.tsum_coe_ne_top

/-- The real-valued masses of any discrete distribution sum to one. -/
@[simp] theorem tsum_toReal (p : PMF α) : ∑' a, (p a).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe, ENNReal.toReal_one]

/-- An injective representation of outcomes also embeds their complete probability laws. -/
theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (PMF.map f) := by
  classical
  intro p q h
  ext a
  simpa [hf.eq_iff] using DFunLike.congr_fun h (f a)

/-- Relabeling a distribution by an equivalence preserves each corresponding point mass. -/
theorem map_equiv_apply (p : PMF α) (e : α ≃ β) (b : β) :
    p.map e b = p (e.symm b) := by
  classical
  simp [← e.symm_apply_eq]

/-- A deterministic map preserves at least the mass of each individual preimage. -/
theorem le_map_apply (p : PMF α) (f : α → β) (a : α) : p a ≤ (p.map f) (f a) := by
  classical
  rw [PMF.map_apply]
  simpa using ENNReal.le_tsum (f := fun x => if f a = f x then p x else 0) a

/-- A randomized continuation preserves at least the joint mass of any one execution path. -/
theorem mul_le_bind_apply (p : PMF α) (f : α → PMF β) (a : α) (b : β) :
    p a * f a b ≤ p.bind f b := by
  rw [PMF.bind_apply]
  exact ENNReal.le_tsum (f := fun x => p x * f x b) a

/-- The real-valued probabilities of a finite distribution sum to one. -/
theorem sum_toReal [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by simpa using tsum_toReal p

/-- An event has probability at most one. -/
theorem toOuterMeasure_le_one (p : PMF α) (event : Set α) : p.toOuterMeasure event ≤ 1 := by
  rw [PMF.toOuterMeasure_apply, ← p.tsum_coe]
  exact ENNReal.tsum_le_tsum (fun a => Set.indicator_apply_le (fun _ => le_rfl))

/-- The probability of any event is finite. -/
theorem toOuterMeasure_ne_top (p : PMF α) (event : Set α) : p.toOuterMeasure event ≠ ⊤ :=
  ne_of_lt ((toOuterMeasure_le_one p event).trans_lt ENNReal.one_lt_top)

open Classical in
/-- Event probabilities on finite spaces are sums of the masses of their members. -/
theorem toOuterMeasure_apply_toReal [Fintype α] (p : PMF α) (event : Set α) :
    (p.toOuterMeasure event).toReal = ∑ a, if a ∈ event then (p a).toReal else 0 := by
  rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ event <;> simp [ha]
  · intro a _
    by_cases ha : a ∈ event <;> simp [ha, PMF.apply_ne_top]

/-- An event and its complement have total probability one, in real-valued probability units. -/
theorem toOuterMeasure_toReal_add_compl (p : PMF α) (event : Set α) :
    (p.toOuterMeasure event).toReal + (p.toOuterMeasure eventᶜ).toReal = 1 := by
  have h : p.toOuterMeasure event + p.toOuterMeasure eventᶜ = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    simp [Set.indicator_self_add_compl_apply]
  rw [← ENNReal.toReal_add (toOuterMeasure_ne_top p _) (toOuterMeasure_ne_top p _), h,
    ENNReal.toReal_one]

/-- An event has positive real probability exactly when it contains a possible outcome. -/
theorem toOuterMeasure_toReal_pos_iff (p : PMF α) (event : Set α) :
    0 < (p.toOuterMeasure event).toReal ↔ ∃ a ∈ event, a ∈ p.support := by
  simp [ENNReal.toReal_pos_iff, lt_top_iff_ne_top, toOuterMeasure_ne_top, pos_iff_ne_zero,
    PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left, and_comm]

open Classical in
/-- Conditioning keeps the event's masses and divides them by its probability. -/
theorem filter_apply_toReal (p : PMF α) (event : Set α)
    (hevent : ∃ a ∈ event, a ∈ p.support) (a : α) :
    ((p.filter event hevent) a).toReal =
      if a ∈ event then (p a).toReal / (p.toOuterMeasure event).toReal else 0 := by
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply]
  by_cases ha : a ∈ event <;> simp [ha, div_eq_mul_inv]

/-- Event probability after a finite random choice is the average conditional probability. -/
theorem toOuterMeasure_bind_toReal [Fintype α] (p : PMF α) (kernel : α → PMF β)
    (event : Set β) :
    ((p.bind kernel).toOuterMeasure event).toReal =
      ∑ a, (p a).toReal * ((kernel a).toOuterMeasure event).toReal := by
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum
    (fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (toOuterMeasure_ne_top _ _))]
  simp

/-- A randomized continuation can fail because its precondition was already false or because
it fails from a valid input. No independence or finite-state assumption is needed. -/
theorem toOuterMeasure_bind_failure_le (p : PMF α) (kernel : α → PMF β)
    (pre : Set α) (failure : Set β) (error : ENNReal)
    (hstep : ∀ a ∈ p.support, a ∈ pre → (kernel a).toOuterMeasure failure ≤ error) :
    (p.bind kernel).toOuterMeasure failure ≤ p.toOuterMeasure preᶜ + error := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply, ← one_mul error, ← p.tsum_coe,
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ pre
  · rw [Set.indicator_of_notMem (by simpa using ha), zero_add]
    by_cases hs : a ∈ p.support
    · exact mul_le_mul_of_nonneg_left (hstep a hs ha) zero_le
    · simp [(PMF.apply_eq_zero_iff p a).2 hs]
  · rw [Set.indicator_of_mem ha]
    exact le_add_right (mul_le_of_le_one_right' (toOuterMeasure_le_one _ _))

/-- The real-valued error rule for a randomized continuation. -/
theorem toOuterMeasure_bind_failure_toReal_le (p : PMF α) (kernel : α → PMF β)
    (pre : Set α) (failure : Set β) {error : ℝ} (herror : 0 ≤ error)
    (hstep : ∀ a ∈ p.support, a ∈ pre →
      ((kernel a).toOuterMeasure failure).toReal ≤ error) :
    ((p.bind kernel).toOuterMeasure failure).toReal ≤
      (p.toOuterMeasure preᶜ).toReal + error := by
  rw [← ENNReal.toReal_ofReal herror, ← ENNReal.toReal_add (toOuterMeasure_ne_top _ _)
    ofReal_ne_top]
  exact ENNReal.toReal_mono (add_ne_top.2 ⟨toOuterMeasure_ne_top _ _, ofReal_ne_top⟩)
    (toOuterMeasure_bind_failure_le p kernel pre failure _ fun a ha hpre =>
      (le_ofReal_iff_toReal_le (toOuterMeasure_ne_top _ _) herror).2 (hstep a ha hpre))

/-- If a randomized test beats a threshold on average, at least its excess probability mass
consists of inputs whose conditional acceptance probability reaches that threshold. -/
theorem toOuterMeasure_rate_ge (p : PMF α) (kernel : α → PMF β) (event : Set β)
    {threshold : ℝ} (hthreshold : 0 ≤ threshold) :
    ((p.bind kernel).toOuterMeasure event).toReal - threshold ≤
      (p.toOuterMeasure {a | threshold ≤ ((kernel a).toOuterMeasure event).toReal}).toReal := by
  have h := toOuterMeasure_bind_failure_toReal_le p kernel
    {a | ((kernel a).toOuterMeasure event).toReal < threshold} event hthreshold
    (fun a _ ha => le_of_lt ha)
  simpa [Set.compl_ofPred] using h

/-- Randomized postprocessing averages the outcome probabilities over any discrete input. -/
theorem bind_apply_toReal_tsum (p : PMF α) (kernel : α → PMF β) (b : β) :
    (p.bind kernel b).toReal = ∑' a, (p a).toReal * (kernel a b).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq (fun a =>
    ENNReal.mul_ne_top (p.apply_ne_top a) ((kernel a).apply_ne_top b))]
  simp

/-- The probability of an outcome after a finite random choice is its weighted average. -/
theorem bind_apply_toReal [Fintype α] (p : PMF α)
    (kernel : α → PMF β) (b : β) :
    (p.bind kernel b).toReal =
      ∑ a, (p a).toReal * (kernel a b).toReal := by
  simpa using bind_apply_toReal_tsum p kernel b

/-- The mass of a deterministic image is the sum of the masses in its fiber. -/
theorem map_apply_toReal [Fintype α] [DecidableEq β] (p : PMF α) (f : α → β) (b : β) :
    ((p.map f) b).toReal = ∑ a, if b = f a then (p a).toReal else 0 := by
  rw [← PMF.bind_pure_comp, bind_apply_toReal]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : b = f a <;> simp [h]

/-- Averaging a score after a deterministic map is averaging its composite with that map. -/
theorem sum_map_mul [Fintype α] [Fintype β] (p : PMF α) (f : α → β) (score : β → ℝ) :
    ∑ b, ((p.map f) b).toReal * score b = ∑ a, (p a).toReal * score (f a) := by
  classical
  simp only [map_apply_toReal, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

/-- Averaging a score after a random choice averages its conditional scores. -/
theorem sum_bind_mul [Fintype α] [Fintype β] (p : PMF α) (kernel : α → PMF β)
    (score : β → ℝ) :
    ∑ b, (p.bind kernel b).toReal * score b =
      ∑ a, (p a).toReal * ∑ b, (kernel a b).toReal * score b := by
  simp only [bind_apply_toReal, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The expectation of an affine score is the same affine function of its expectation. -/
theorem sum_affine [Fintype α] (p : PMF α) (a b : ℝ) (score : α → ℝ) :
    (∑ x, (p x).toReal * (a + b * score x)) =
      a + b * ∑ x, (p x).toReal * score x := by
  simp [mul_add, mul_left_comm _ b, Finset.sum_add_distrib, ← Finset.sum_mul, sum_toReal,
    ← Finset.mul_sum]

/-- A uniform upper bound on a score also bounds its expectation. -/
theorem sum_mul_le [Fintype α] (p : PMF α) (score : α → ℝ) (bound : ℝ)
    (hscore : ∀ a, score a ≤ bound) :
    ∑ a, (p a).toReal * score a ≤ bound := by
  calc
    _ ≤ ∑ a, (p a).toReal * bound := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (hscore a) ENNReal.toReal_nonneg)
    _ = bound := by rw [← Finset.sum_mul, sum_toReal, one_mul]

/-- The mass of an image of a uniform input is its fiber size divided by the input size. -/
theorem uniformOfFintype_map_apply [Fintype α] [Nonempty α] (f : α → β) (b : β) :
    ((PMF.uniformOfFintype α).map f) b =
      (Nat.card {a // f a = b} : ℝ≥0∞) / Fintype.card α := by
  classical
  simp [← Finset.sum_filter, div_eq_mul_inv, Fintype.card_subtype, eq_comm]

/-- A continuation only needs to agree on outcomes which the preceding distribution can produce. -/
theorem bind_congr_on_support (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · simp [(PMF.apply_eq_zero_iff p a).2 ha]

/-- Re-encoding only needs to agree on outcomes which the distribution can produce. -/
theorem map_congr_on_support (p : PMF α) (f g : α → β)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g :=
  bind_congr_on_support p _ _ (fun a ha => congrArg PMF.pure (h a ha))

/-- Evaluating the "pairing" bind `(do let a ← p; return (a, ← f a))` at `(a, b)`
gives the product `p a * f a b`. -/
theorem bind_pair_apply (p : PMF α) (f : α → PMF β) (a : α) (b : β) :
    (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) = p a * f a b := by
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [PMF.bind_apply]; congr 1; rw [tsum_eq_single b]
    · simp [PMF.pure_apply]
    · intro b' hb'; simp [PMF.pure_apply, hb'.symm]
  · intro a' ha'; rw [PMF.bind_apply]; simp [PMF.pure_apply, ha'.symm]

/-- The pairing law also holds when the second sample's type depends on the first. -/
theorem bind_sigma_apply {β : α → Type*} (p : PMF α) (f : (a : α) → PMF (β a))
    (a : α) (b : β a) :
    (p.bind (fun a => (f a).map (Sigma.mk a))) ⟨a, b⟩ = p a * f a b := by
  classical
  rw [PMF.bind_apply, tsum_eq_single a]
  · congr 1
    simp
  · intro i hi
    have hne (c : β i) : (Sigma.mk a b : Sigma β) ≠ ⟨i, c⟩ :=
      fun h => hi (congrArg Sigma.fst h).symm
    simp [hne]

/-- Summing the pairing bind over the first component gives the marginal. -/
theorem bind_pair_tsum_fst (p : PMF α) (f : α → PMF β) (b : β) :
    ∑' a, (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) =
      (p.bind f) b := by
  simp_rw [bind_pair_apply, PMF.bind_apply]

/-- Marginalizing a joint distribution over its freshly sampled second component. -/
@[simp] theorem map_fst_bind_pair (p : PMF α) (f : α → PMF β) :
    (p.bind (fun a => (f a).map (a, ·))).map Prod.fst = p := by
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  change p.bind (fun a => (f a).map (Function.const β a)) = p
  simp

/-- Marginalizing a joint distribution over its first component gives ordinary sequencing. -/
@[simp] theorem map_snd_bind_pair (p : PMF α) (f : α → PMF β) :
    (p.bind (fun a => (f a).map (a, ·))).map Prod.snd = p.bind f := by
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  change p.bind (fun a => (f a).map id) = p.bind f
  simp [PMF.map_id]

/-- A uniform distribution on a finite type is invariant under any equivalence. -/
theorem uniformOfFintype_map_equiv {γ : Type v} [Fintype α] [Fintype γ] [Nonempty α] [Nonempty γ]
    (e : α ≃ γ) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype γ := by
  ext c
  rw [PMF.map_apply, tsum_eq_single (e.symm c)]
  · simp [Fintype.card_congr e]
  · exact fun a ha => ite_eq_right fun h => ha (by simp [h])

/-- A uniform pair consists of two independent uniform samples. -/
theorem uniformOfFintype_prod [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    PMF.uniformOfFintype (α × β) = (PMF.uniformOfFintype α).bind
      (fun a => (PMF.uniformOfFintype β).map (fun b => (a, b))) := by
  ext ⟨a, b⟩
  simp only [PMF.map, Function.comp_def, bind_pair_apply, PMF.uniformOfFintype_apply,
    Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv] <;> simp

/-- The posterior distribution `Pr[A = a | B = b]` as a `PMF`,
given `a ← p`, `b ← f a`, and that `b` has positive marginal probability:
the joint distribution's slice at `b`, normalized. -/
noncomputable def posteriorDist (p : PMF α) (f : α → PMF β) (b : β)
    (hb : b ∈ (p.bind f).support) : PMF α :=
  PMF.normalize
    (fun a => (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b))
    (by rw [bind_pair_tsum_fst]; exact (PMF.mem_support_iff _ _).mp hb)
    (by rw [bind_pair_tsum_fst]; exact PMF.apply_ne_top _ _)

@[simp]
theorem posteriorDist_apply (p : PMF α) (f : α → PMF β) (b : β)
    (hb : b ∈ (p.bind f).support) (a : α) :
    posteriorDist p f b hb a =
      (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) /
        (p.bind f) b := by
  rw [posteriorDist, PMF.normalize_apply, bind_pair_tsum_fst, div_eq_mul_inv]

/-- If the output distribution of a channel does not depend on the input, then
conditioning on any output with positive probability leaves the prior unchanged. -/
theorem posteriorDist_eq_prior_of_outputIndist (p : PMF α) (f : α → PMF β)
    (h : ∀ a₀ a₁ : α, f a₀ = f a₁)
    (b : β) (hb : b ∈ (p.bind f).support) :
    posteriorDist p f b hb = p := by
  ext a
  have hbind : p.bind f = f a :=
    (congrArg p.bind (funext fun a' => h a' a)).trans (PMF.bind_const p (f a))
  rw [posteriorDist_apply, bind_pair_apply, hbind]
  exact ENNReal.mul_div_cancel_right ((PMF.mem_support_iff _ _).mp (hbind ▸ hb))
    (PMF.apply_ne_top _ _)

end Cslib.Probability.PMF
