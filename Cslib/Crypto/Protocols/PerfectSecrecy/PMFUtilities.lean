/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Probability.ProbabilityMassFunction.Monad

@[expose] public section

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

- `PMFUtilities.bind_pair_apply`: the "pairing" bind at `(a, b)` equals `p a * f a b`
- `PMFUtilities.bind_pair_tsum_fst`: marginalizing over the first component
- `PMFUtilities.posterior_hasSum`: posterior probabilities sum to 1
- `PMFUtilities.posteriorDist`: the posterior as a `PMF`
-/

namespace Cslib.Crypto.Protocols.PerfectSecrecy.PMFUtilities

open PMF ENNReal

universe u
variable {α β : Type u}

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

/-- Posterior probabilities `joint(a, b) / marginal(b)` sum to 1
when `b` is in the support of the marginal. -/
theorem posterior_hasSum (p : PMF α) (f : α → PMF β) (b : β)
    (hb : b ∈ (p.bind f).support) :
    HasSum (fun a =>
      (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) /
        (p.bind f) b) 1 := by
  have hne := (PMF.mem_support_iff _ _).mp hb
  have hne_top := ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one (p.bind f) b)
  have : ∑' a, (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) /
      (p.bind f) b = 1 := by
    simp only [div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, bind_pair_tsum_fst]
    exact ENNReal.mul_inv_cancel hne hne_top
  exact this ▸ ENNReal.summable.hasSum

/-- The posterior distribution `Pr[A = a | B = b]` as a `PMF`,
given `a ← p`, `b ← f a`, and that `b` has positive marginal probability. -/
noncomputable def posteriorDist (p : PMF α) (f : α → PMF β) (b : β)
    (hb : b ∈ (p.bind f).support) : PMF α :=
  ⟨fun a =>
    (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) /
      (p.bind f) b,
   posterior_hasSum p f b hb⟩

@[simp]
theorem posteriorDist_apply (p : PMF α) (f : α → PMF β) (b : β)
    (hb : b ∈ (p.bind f).support) (a : α) :
    posteriorDist p f b hb a =
      (p.bind fun a' => (f a').bind fun b' => PMF.pure (a', b')) (a, b) /
        (p.bind f) b :=
  rfl

end Cslib.Crypto.Protocols.PerfectSecrecy.PMFUtilities
