/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.PMFUtilities
public import Cslib.Crypto.Protocols.SecretSharing.Scheme

@[expose] public section

/-!
# Secret Sharing: Definitions

Privacy for secret sharing is formalized by looking at the view induced on one
coalition, then comparing posterior and prior distributions on secrets.

## Main definitions

- `Cslib.Crypto.Protocols.SecretSharing.Scheme.shareDist`:
  the full share distribution for one secret
- `Cslib.Crypto.Protocols.SecretSharing.Scheme.viewDist`:
  the distribution of the restricted view for one coalition
- `Cslib.Crypto.Protocols.SecretSharing.Scheme.posteriorSecretDist`:
  the posterior distribution on secrets after observing one view
- `Cslib.Crypto.Protocols.SecretSharing.Scheme.ViewIndist`:
  indistinguishability of views for unauthorized coalitions
- `Cslib.Crypto.Protocols.SecretSharing.Scheme.PerfectlyPrivate`:
  posterior equals prior for unauthorized coalitions

## References

* [Adi Shamir, *How to Share a Secret*][Shamir1979]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

namespace Cslib.Crypto.Protocols.SecretSharing

namespace Scheme

variable {Secret Randomness Party Share : Type*} [DecidableEq Party]

/-- The distribution of the full share assignment for one secret. -/
noncomputable def shareDist (scheme : Scheme Secret Randomness Party Share)
    (secret : Secret) : PMF (Party → Share) :=
  scheme.gen.map (fun r => scheme.share r secret)

/-- The view distribution induced on the coalition `s`. -/
noncomputable def viewDist (scheme : Scheme Secret Randomness Party Share)
    (s : Finset Party) (secret : Secret) : PMF (s → Share) :=
  scheme.gen.map (fun r => scheme.view s r secret)

/-- The posterior distribution on secrets after observing the coalition view
`v`. -/
noncomputable def posteriorSecretDist
    (scheme : Scheme Secret Randomness Party Share)
    (s : Finset Party) (secretDist : PMF Secret) (v : s → Share)
    (hv : v ∈ (secretDist.bind (scheme.viewDist s)).support) : PMF Secret :=
  Cslib.Crypto.Protocols.PerfectSecrecy.PMFUtilities.posteriorDist
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

/-- View indistinguishability for unauthorized coalitions. -/
def ViewIndist (scheme : Scheme Secret Randomness Party Share) : Prop :=
  ∀ (s : Finset Party), ¬ scheme.authorized s → ∀ secret₀ secret₁ : Secret,
    scheme.viewDist s secret₀ = scheme.viewDist s secret₁

/-- Perfect privacy for unauthorized coalitions: conditioning on a view does not
change the prior on secrets. -/
def PerfectlyPrivate (scheme : Scheme Secret Randomness Party Share) : Prop :=
  ∀ (s : Finset Party) (_hs : ¬ scheme.authorized s)
    (secretDist : PMF Secret) (v : s → Share)
    (hv : v ∈ (secretDist.bind (scheme.viewDist s)).support),
      scheme.posteriorSecretDist s secretDist v hv = secretDist

end Scheme

end Cslib.Crypto.Protocols.SecretSharing
