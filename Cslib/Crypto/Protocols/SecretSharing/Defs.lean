/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.PMF
public import Cslib.Crypto.Protocols.SecretSharing.Scheme

@[expose] public section

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
  posterior equals prior for unauthorized coalitions
- `Cslib.Crypto.Protocols.SecretSharing.Scheme.perfectlyPrivate`:
  every scheme has posterior privacy

## References

* [Adi Shamir, *How to Share a Secret*][Shamir1979]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

namespace Cslib.Crypto.Protocols.SecretSharing

namespace Scheme

variable {Secret Randomness Party Share : Type*}

/-- The distribution of the full share assignment for one secret. -/
noncomputable def shareDist (scheme : Scheme Secret Randomness Party Share)
    (secret : Secret) : PMF (Party → Share) :=
  scheme.gen.map (fun r => scheme.share r secret)

/-- The view distribution induced on the coalition `s`. -/
noncomputable def viewDist (scheme : Scheme Secret Randomness Party Share)
    (s : Finset Party) (secret : Secret) : PMF (s → Share) :=
  viewDistOf scheme.gen scheme.share s secret

/-- Unauthorized coalitions receive secret-independent view distributions. -/
theorem viewDist_eq_of_not_authorized
    (scheme : Scheme Secret Randomness Party Share)
    {s : Finset Party} (hs : ¬ scheme.authorized s)
    (secret₀ secret₁ : Secret) :
    scheme.viewDist s secret₀ = scheme.viewDist s secret₁ := by
  unfold viewDist
  exact scheme.view_indist s hs secret₀ secret₁

/-- The posterior distribution on secrets after observing the coalition view
`v`. -/
noncomputable def posteriorSecretDist
    (scheme : Scheme Secret Randomness Party Share)
    (s : Finset Party) (secretDist : PMF Secret) (v : s → Share)
    (hv : v ∈ (secretDist.bind (scheme.viewDist s)).support) : PMF Secret :=
  Cslib.Probability.PMF.posteriorDist
    (p := secretDist) (f := scheme.viewDist s) v hv

@[simp]
theorem posteriorSecretDist_apply
    (scheme : Scheme Secret Randomness Party Share)
    (s : Finset Party) (secretDist : PMF Secret) (v : s → Share)
    (hv : v ∈ (secretDist.bind (scheme.viewDist s)).support) (secret : Secret) :
    scheme.posteriorSecretDist s secretDist v hv secret =
      (secretDist.bind fun secret' =>
        (scheme.viewDist s secret').bind fun v' => PMF.pure (secret', v')) (secret, v) /
        (secretDist.bind (scheme.viewDist s)) v :=
  rfl

/-- Perfect privacy for unauthorized coalitions: conditioning on a view does not
change the prior on secrets. -/
def PerfectlyPrivate (scheme : Scheme Secret Randomness Party Share) : Prop :=
  ∀ (s : Finset Party) (_hs : ¬ scheme.authorized s)
    (secretDist : PMF Secret) (v : s → Share)
    (hv : v ∈ (secretDist.bind (scheme.viewDist s)).support),
      scheme.posteriorSecretDist s secretDist v hv = secretDist

/-- Every scheme has posterior privacy by definition of `Scheme`. -/
theorem perfectlyPrivate
    (scheme : Scheme Secret Randomness Party Share) :
    scheme.PerfectlyPrivate := by
  intro s hs secretDist v hv
  exact Cslib.Probability.PMF.posteriorDist_eq_prior_of_outputIndist
    (p := secretDist) (f := scheme.viewDist s)
    (fun secret₀ secret₁ => scheme.viewDist_eq_of_not_authorized hs secret₀ secret₁) v hv

end Scheme

end Cslib.Crypto.Protocols.SecretSharing
