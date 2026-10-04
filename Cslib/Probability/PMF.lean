/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Devon Tuma, Kexing Ying, Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# PMF Utilities

## NB: This module is temporary

The bind/pure and posterior lemmas here have no dependence on any domain-specific
structure. They should be upstreamed to Mathlib
(likely `Mathlib.Probability.ProbabilityMassFunction.Monad` or a new
`Mathlib.Probability.ProbabilityMassFunction.Prod`). Once accepted upstream,
these lemmas should be removed and their consumers should import the Mathlib module instead.

The uniform samplers retain the PMF interface removed in
[mathlib#42909](https://github.com/leanprover-community/mathlib4/pull/42909),
pending a decision on CSLib's probability API. Their definitions and proofs are adapted from
`Mathlib.Probability.Distributions.Uniform` before that PR, by Josha Dekker, Devon Tuma,
and Kexing Ying, under the Apache 2.0 license.
Original sampler copyright (c) 2024 Josha Dekker. All rights reserved.

## Main results

- `Cslib.Probability.PMF.bind_pair_apply`: the "pairing" bind at `(a, b)` equals `p a * f a b`
- `Cslib.Probability.PMF.bind_pair_tsum_fst`: marginalizing over the first component
- `Cslib.Probability.PMF.uniformOfFintype_map_equiv`:
  a uniform distribution is invariant under equivalence
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

/-- Uniform probability mass function on a nonempty finite set. -/
noncomputable def uniformOfFinset (s : Finset α) (hs : s.Nonempty) : PMF α := by
  classical
  refine PMF.ofFinset (fun a => if a ∈ s then s.card⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : ℝ≥0∞) ≠ 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempty_iff_ne_empty.1 hs
    exact ENNReal.mul_inv_cancel this <| ENNReal.natCast_ne_top s.card
  · exact fun x hx => by simp only [hx, ite_false]

open scoped Classical in
@[simp]
theorem uniformOfFinset_apply (s : Finset α) (hs : s.Nonempty) (a : α) :
    uniformOfFinset s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 :=
  rfl

theorem mem_support_uniformOfFinset_iff {s : Finset α} (hs : s.Nonempty) (a : α) :
    a ∈ (uniformOfFinset s hs).support ↔ a ∈ s := by
  classical
  simp [PMF.mem_support_iff]

/-- Uniform probability mass function on a nonempty finite type. -/
noncomputable def uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOfFinset Finset.univ Finset.univ_nonempty

@[simp]
theorem uniformOfFintype_apply [Fintype α] [Nonempty α] (a : α) :
    uniformOfFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformOfFintype]

/-- Real-valued probability masses are summable, even on an infinite ambient type. -/
theorem summable_toReal (p : PMF α) : Summable (fun a => (p a).toReal) :=
  ENNReal.summable_toReal p.tsum_coe_ne_top

/-- The real-valued masses of any discrete distribution sum to one. -/
@[simp] theorem tsum_toReal (p : PMF α) : ∑' a, (p a).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe, ENNReal.toReal_one]

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

/-- Evaluating the "pairing" bind `(do let a ← p; return (a, ← f a))` at `(a, b)`
gives the product `p a * f a b`. -/
theorem bind_pair_apply (p : PMF α) (f : α → PMF β) (a : α) (b : β) :
    (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) = p a * f a b := by
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [PMF.bind_apply]; congr 1; rw [tsum_eq_single b]
    · simp [PMF.pure_apply]
    · intro b' hb'; simp [PMF.pure_apply, hb'.symm]
  · intro a' ha'; rw [PMF.bind_apply]; simp [PMF.pure_apply, ha'.symm]

/-- Summing the pairing bind over the first component gives the marginal. -/
theorem bind_pair_tsum_fst (p : PMF α) (f : α → PMF β) (b : β) :
    ∑' a, (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) =
      (p.bind f) b := by
  simp_rw [bind_pair_apply, PMF.bind_apply]

/-- A uniform distribution on a finite type is invariant under any equivalence. -/
theorem uniformOfFintype_map_equiv {γ : Type v} [Fintype α] [Fintype γ] [Nonempty α] [Nonempty γ]
    (e : α ≃ γ) :
    (uniformOfFintype α).map e = uniformOfFintype γ := by
  ext c
  rw [PMF.map_apply, tsum_eq_single (e.symm c)]
  · simp [Fintype.card_congr e]
  · exact fun a ha => ite_eq_right fun h => ha (by simp [h])

/-- Independent uniform sampling on `α` and `β` equals uniform sampling on `α × β`. -/
theorem uniformOfFintype_prod (α β : Type*)
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    ((PMF.uniformOfFintype α).bind fun a =>
      (PMF.uniformOfFintype β).map fun b => (a, b)) =
    PMF.uniformOfFintype (α × β) := by
  ext ⟨a, b⟩
  simp only [PMF.map, Function.comp_def, bind_pair_apply,
    PMF.uniformOfFintype_apply]
  simp [Fintype.card_prod, ENNReal.mul_inv]

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
