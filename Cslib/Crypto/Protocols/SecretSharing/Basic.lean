/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.SecretSharing.Defs
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-!
# Secret Sharing: Basic Privacy Theory

This file proves that the two standard information-theoretic formulations of
privacy agree for secret-sharing schemes:

- view indistinguishability for unauthorized coalitions
- posterior equals prior after conditioning on one unauthorized view

## Main results

- `Cslib.Crypto.Protocols.SecretSharing.Scheme.perfectlyPrivate_of_viewIndist`
- `Cslib.Crypto.Protocols.SecretSharing.Scheme.viewIndist_of_perfectlyPrivate`
- `Cslib.Crypto.Protocols.SecretSharing.Scheme.perfectlyPrivate_iff_viewIndist`

## References

* [Adi Shamir, *How to Share a Secret*][Shamir1979]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

namespace Cslib.Crypto.Protocols.SecretSharing

open PMF ENNReal

namespace Scheme

variable {Secret Randomness Party Share : Type*} [DecidableEq Party]

/-- View indistinguishability implies posterior privacy. -/
theorem perfectlyPrivate_of_viewIndist
    (scheme : Scheme Secret Randomness Party Share)
    (h : scheme.ViewIndist) :
    scheme.PerfectlyPrivate := by
  intro s hs secretDist v hv
  exact Cslib.Crypto.Protocols.PerfectSecrecy.PMFUtilities.posteriorDist_eq_prior_of_outputIndist
    (p := secretDist) (f := scheme.viewDist s)
    (fun secret₀ secret₁ => h s hs secret₀ secret₁) v hv

/-- Posterior privacy implies view indistinguishability for unauthorized
coalitions. -/
theorem viewIndist_of_perfectlyPrivate
    (scheme : Scheme Secret Randomness Party Share)
    (h : scheme.PerfectlyPrivate) :
    scheme.ViewIndist := by
  classical
  intro s hs secret₀ secret₁
  ext v
  let secrets : Finset Secret := {secret₀, secret₁}
  have hsecrets : secrets.Nonempty := ⟨secret₀, by simp [secrets]⟩
  let μ : PMF Secret := PMF.uniformOfFinset secrets hsecrets
  by_cases hv : v ∈ (μ.bind (scheme.viewDist s)).support
  · have hmarg : (μ.bind (scheme.viewDist s)) v ≠ 0 :=
      (PMF.mem_support_iff _ _).mp hv
    have hmarg_top : (μ.bind (scheme.viewDist s)) v ≠ ∞ :=
      ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one (μ.bind (scheme.viewDist s)) v)
    have hkey :
        ∀ secret ∈ secrets, scheme.viewDist s secret v = (μ.bind (scheme.viewDist s)) v := by
      intro secret hsecret
      have hμ_mem : secret ∈ μ.support :=
        (PMF.mem_support_uniformOfFinset_iff hsecrets secret).2 hsecret
      have hμ_ne : μ secret ≠ 0 := (PMF.mem_support_iff _ _).mp hμ_mem
      have hμ_top : μ secret ≠ ∞ :=
        ne_top_of_le_ne_top one_ne_top (PMF.coe_le_one μ secret)
      have hpost : scheme.posteriorSecretDist s μ v hv secret = μ secret :=
        congrArg (fun q : PMF Secret => q secret) (h s hs μ v hv)
      rw [posteriorSecretDist_apply,
        Cslib.Crypto.Protocols.PerfectSecrecy.PMFUtilities.bind_pair_apply] at hpost
      have hpost' :
          (μ.bind (scheme.viewDist s)) v * μ secret =
            μ secret * (scheme.viewDist s secret) v :=
        (ENNReal.eq_div_iff hmarg hmarg_top).mp hpost.symm
      rw [mul_comm ((μ.bind (scheme.viewDist s)) v) (μ secret)] at hpost'
      exact (ENNReal.mul_right_inj hμ_ne hμ_top).mp hpost'.symm
    exact (hkey secret₀ (by simp [secrets])).trans (hkey secret₁ (by simp [secrets])).symm
  · have hkey :
        ∀ secret ∈ secrets, scheme.viewDist s secret v = 0 := by
      intro secret hsecret
      by_contra hsecretv
      have hμ_mem : secret ∈ μ.support :=
        (PMF.mem_support_uniformOfFinset_iff hsecrets secret).2 hsecret
      exact hv <| (PMF.mem_support_bind_iff _ _ _).2
        ⟨secret, hμ_mem, (PMF.mem_support_iff _ _).2 hsecretv⟩
    rw [hkey secret₀ (by simp [secrets]), hkey secret₁ (by simp [secrets])]

/-- Posterior privacy and view indistinguishability are equivalent. -/
theorem perfectlyPrivate_iff_viewIndist
    (scheme : Scheme Secret Randomness Party Share) :
    scheme.PerfectlyPrivate ↔ scheme.ViewIndist :=
  ⟨viewIndist_of_perfectlyPrivate scheme, perfectlyPrivate_of_viewIndist scheme⟩

end Scheme

end Cslib.Crypto.Protocols.SecretSharing
