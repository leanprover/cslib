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
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype γ := by
  ext c
  rw [PMF.map_apply, tsum_eq_single (e.symm c)]
  · simp [Fintype.card_congr e]
  · exact fun a ha => ite_eq_right fun h => ha (by simp [h])

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
