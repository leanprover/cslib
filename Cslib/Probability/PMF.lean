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
