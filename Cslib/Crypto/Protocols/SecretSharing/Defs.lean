/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.SecretSharing.Scheme

/-!
# Secret Sharing: Definitions

Privacy for secret sharing is part of the `Scheme` interface. This file exposes
the corresponding view and posterior distributions, plus theorem-friendly
consequences of the built-in privacy field.

## Main definitions

- `Cslib.Crypto.Protocols.SecretSharing.Scheme.shareDist`:
  the full share distribution for one secret
- `Cslib.Crypto.Protocols.SecretSharing.Scheme.viewDist`:
  the distribution of the restricted view for one coalition
- `Cslib.Crypto.Protocols.SecretSharing.Scheme.posteriorSecretDist`:
  the posterior distribution on secrets after observing one view
- `Cslib.Crypto.Protocols.SecretSharing.Scheme.PerfectlyPrivate`:
  independence of secrets and unauthorized views
- `Cslib.Crypto.Protocols.SecretSharing.Scheme.perfectlyPrivate`:
  every scheme has measure-theoretic privacy

## References

* [Adi Shamir, *How to Share a Secret*][Shamir1979]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SecretSharing

namespace Scheme

open MeasureTheory ProbabilityTheory Cslib.Probability.Measure

variable {Secret Randomness Party Share : Type*}
variable [MeasurableSpace Secret] [MeasurableSpace Randomness] [MeasurableSpace Share]

/-- The distribution of the full share assignment for one secret. -/
noncomputable abbrev shareDist (scheme : Scheme Secret Randomness Party Share)
    (secret : Secret) : Measure (Party → Share) :=
  scheme.gen.map (fun r => scheme.share r secret)

/-- The view distribution induced on the coalition `s`. -/
noncomputable abbrev viewDist (scheme : Scheme Secret Randomness Party Share)
    (s : Finset Party) (secret : Secret) : Measure (s → Share) :=
  scheme.viewKernel s secret

/-- Unauthorized coalitions receive secret-independent view distributions. -/
theorem viewDist_eq_of_not_authorized
    (scheme : Scheme Secret Randomness Party Share)
    {s : Finset Party} (hs : ¬ scheme.authorized s)
    (secret₀ secret₁ : Secret) :
    scheme.viewDist s secret₀ = scheme.viewDist s secret₁ :=
  by
    simp only [viewDist, viewKernel, sampleKernel_apply]
    exact scheme.view_indist s hs secret₀ secret₁

/-- Mathlib's regular conditional distribution on secrets given a coalition view. -/
noncomputable abbrev posteriorSecretDist [StandardBorelSpace Secret] [Nonempty Secret]
    (scheme : Scheme Secret Randomness Party Share)
    (s : Finset Party) (secretDist : Measure Secret) [IsProbabilityMeasure secretDist] :
    Kernel (s → Share) Secret :=
  posterior (scheme.viewKernel s) secretDist

/-- Unauthorized views and secrets are independent for every probability prior.
Equality of joint measures also handles observations of zero singleton mass. -/
def PerfectlyPrivate (scheme : Scheme Secret Randomness Party Share) : Prop :=
  ∀ (s : Finset Party), ¬ scheme.authorized s →
    ∀ (secretDist : Measure Secret) [IsProbabilityMeasure secretDist],
      secretDist ⊗ₘ scheme.viewKernel s =
        secretDist.prod (scheme.viewKernel s ∘ₘ secretDist)

/-- Every scheme has measure-theoretic privacy by its view-indistinguishability field. -/
theorem perfectlyPrivate (scheme : Scheme Secret Randomness Party Share) :
    scheme.PerfectlyPrivate := by
  intro s hs secretDist _
  exact compProd_eq_prod_of_outputIndist secretDist (scheme.viewKernel s)
    (scheme.viewDist_eq_of_not_authorized hs)

/-- Conditioning on an unauthorized view leaves the prior unchanged almost surely. -/
theorem posteriorSecretDist_eq_prior [StandardBorelSpace Secret] [Nonempty Secret]
    (scheme : Scheme Secret Randomness Party Share)
    {s : Finset Party} (hs : ¬ scheme.authorized s)
    (secretDist : Measure Secret) [IsProbabilityMeasure secretDist] :
    scheme.posteriorSecretDist s secretDist =ᵐ[scheme.viewKernel s ∘ₘ secretDist]
      fun _ => secretDist :=
  posterior_eq_prior_of_compProd_eq_prod secretDist (scheme.viewKernel s)
    (scheme.perfectlyPrivate s hs secretDist)

end Scheme

end Cslib.Crypto.Protocols.SecretSharing
