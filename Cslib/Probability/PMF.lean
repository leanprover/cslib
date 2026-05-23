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
- `Cslib.Probability.PMF.posterior_hasSum`: posterior probabilities sum to 1
- `Cslib.Probability.PMF.posteriorDist`: the posterior as a `PMF`
- `Cslib.Probability.PMF.posteriorDist_eq_prior_of_outputIndist`:
  if the output distribution does not depend on the input, conditioning does
  not change the prior
-/

@[expose] public section

namespace Cslib.Probability.PMF

open PMF ENNReal

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
  classical
  have hcard : Fintype.card α = Fintype.card γ := Fintype.card_congr e
  ext c
  rw [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_eq_single (e.symm c)]
  · simp_rw [PMF.uniformOfFintype_apply]
    simp [hcard]
  · intro a ha
    simp_rw [PMF.uniformOfFintype_apply]
    split_ifs with h
    · exfalso
      apply ha
      simpa using congrArg e.symm h.symm
    · simp

/-- Pushing forward a uniform distribution on the subtype `↥s` along `Subtype.val`
gives the uniform distribution on the underlying finset `s`. -/
theorem map_subtypeVal_uniformOfFintype (s : Finset α) (hs : s.Nonempty) :
    haveI : Nonempty {x // x ∈ s} := hs.coe_sort
    (PMF.uniformOfFintype {x // x ∈ s}).map Subtype.val = PMF.uniformOfFinset s hs := by
  classical
  haveI : Nonempty {x // x ∈ s} := hs.coe_sort
  ext a
  rw [PMF.map_apply, PMF.uniformOfFinset_apply]
  by_cases ha : a ∈ s
  · rw [tsum_eq_single ⟨a, ha⟩, if_pos rfl, PMF.uniformOfFintype_apply,
      Fintype.card_coe, if_pos ha]
    intro x hx
    rw [if_neg (fun h => hx (Subtype.ext h.symm))]
  · rw [if_neg ha, ENNReal.tsum_eq_zero]
    intro x
    rw [if_neg]
    rintro rfl; exact ha x.2

/-- Binding a uniform distribution on `Bool` against a two-branch `pure` gives the
uniform distribution on the (possibly singleton) two-element finset. -/
theorem uniformOfFintype_bool_bind_ite [DecidableEq α] (a b : α) :
    ((PMF.uniformOfFintype Bool).bind fun x => PMF.pure (bif x then a else b)) =
      PMF.uniformOfFinset {a, b} (Finset.insert_nonempty a {b}) := by
  ext m
  rw [PMF.bind_apply, PMF.uniformOfFinset_apply,
    tsum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool]
  by_cases hab : a = b
  · subst hab
    by_cases hm : m = a <;>
      simp [hm, PMF.pure_apply, ENNReal.inv_two_add_inv_two]
  · by_cases h₀ : m = a <;> by_cases h₁ : m = b
    all_goals simp_all [Finset.card_pair (Ne.symm fun h => hab h.symm),
      PMF.pure_apply, ENNReal.inv_two_add_inv_two]

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

/-- If the output distribution of a channel does not depend on the input, then
conditioning on any output with positive probability leaves the prior unchanged. -/
theorem posteriorDist_eq_prior_of_outputIndist (p : PMF α) (f : α → PMF β)
    (h : ∀ a₀ a₁ : α, f a₀ = f a₁)
    (b : β) (hb : b ∈ (p.bind f).support) :
    posteriorDist p f b hb = p := by
  ext a
  rw [posteriorDist_apply, bind_pair_apply, PMF.bind_apply]
  have hf : ∀ a', f a' b = f a b := fun a' => by rw [h a' a]
  simp_rw [hf]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hb' : (p.bind f) b ≠ 0 := (PMF.mem_support_iff _ _).mp hb
  have hmarg : (p.bind f) b = f a b := by
    rw [PMF.bind_apply]
    simp_rw [hf]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  exact ENNReal.mul_div_cancel_right (hmarg ▸ hb')
    (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one _ _))

@[simp]
lemma monad_pure_eq_pure (x : α) : (pure x : PMF α) = PMF.pure x := rfl

lemma monad_bind_eq_bind {α β} (p : PMF α) (q : α → PMF β) : p >>= q = p.bind q := rfl

end Cslib.Probability.PMF
