/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Probability.Measure

/-!
# Secret Sharing Schemes

A secret-sharing scheme bundles the deterministic sharing/reconstruction
interface, the distribution on randomness, and privacy for unauthorized
coalitions.

## Main definitions

- `Cslib.Crypto.Protocols.SecretSharing.Scheme`:
  a secret-sharing scheme with correctness and privacy
- `Cslib.Crypto.Protocols.SecretSharing.Scheme.view`:
  the restricted shares seen by one coalition

## References

* [Adi Shamir, *How to Share a Secret*][Shamir1979]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Cslib.Probability.Measure

namespace Cslib.Crypto.Protocols.SecretSharing

/-- The view distribution induced by raw sharing data. -/
noncomputable def viewDistOf {Secret Randomness Party Share : Type*}
    [MeasurableSpace Randomness] [MeasurableSpace Share]
    (gen : Measure Randomness) (share : Randomness → Secret → Party → Share)
    (s : Finset Party) (secret : Secret) : Measure (s → Share) :=
  Measure.map (fun r : Randomness => (fun i : s => share r secret i : s → Share)) gen

/--
A secret-sharing scheme over secret space `Secret`, randomness space
`Randomness`, party set `Party`, and share space `Share`.

Correctness is deterministic: every authorized coalition reconstructs the
secret from the shares generated using any randomness seed. Privacy is
distributional: unauthorized coalitions have the same view distribution for all
secrets.
-/
structure Scheme (Secret Randomness Party Share : Type*)
    [MeasurableSpace Secret] [MeasurableSpace Randomness] [MeasurableSpace Share] where
  /-- The distribution used to sample the protocol's randomness. -/
  gen : Measure Randomness
  /-- Randomness sampling has total mass one. -/
  gen_isProbabilityMeasure : IsProbabilityMeasure gen
  /-- Sharing algorithm: one randomness seed determines one share per party. -/
  share : Randomness → Secret → Party → Share
  /-- Sharing is jointly measurable in its randomness and secret. -/
  share_measurable : Measurable (Function.uncurry share)
  /-- Reconstruction from a coalition's observed shares. -/
  reconstruct (s : Finset Party) : (s → Share) → Secret
  /-- Authorized coalitions. -/
  authorized : Finset Party → Prop
  /-- Authorization is monotone in the coalition. -/
  authorized_mono : Monotone authorized
  /-- Authorized coalitions reconstruct the secret from the restricted view. -/
  correct :
    ∀ (r : Randomness) (secret : Secret) (s : Finset Party),
      authorized s → reconstruct s (fun i => share r secret i) = secret
  /-- Unauthorized coalitions receive secret-independent view distributions. -/
  view_indist :
    ∀ (s : Finset Party), ¬ authorized s → ∀ secret₀ secret₁ : Secret,
      viewDistOf gen share s secret₀ = viewDistOf gen share s secret₁

attribute [instance] Scheme.gen_isProbabilityMeasure

namespace Scheme

variable {Secret Randomness Party Share : Type*}
variable [MeasurableSpace Secret] [MeasurableSpace Randomness] [MeasurableSpace Share]

/-- The restricted shares observed by the coalition `s`. -/
def view (scheme : Scheme Secret Randomness Party Share) (s : Finset Party)
    (r : Randomness) (secret : Secret) : s → Share :=
  fun i => scheme.share r secret i

/-- The measurable channel from secrets to coalition views. -/
noncomputable def viewKernel (scheme : Scheme Secret Randomness Party Share)
    (s : Finset Party) : Kernel Secret (s → Share) :=
  sampleKernel scheme.gen (scheme.view s) <|
    Measurable.of_eval fun i => (measurable_pi_apply (i : Party)).comp scheme.share_measurable

instance (scheme : Scheme Secret Randomness Party Share) (s : Finset Party) :
    IsMarkovKernel (scheme.viewKernel s) := by
  dsimp [viewKernel]
  infer_instance

@[simp]
theorem view_apply (scheme : Scheme Secret Randomness Party Share) (s : Finset Party)
    (r : Randomness) (secret : Secret) (i : s) :
    scheme.view s r secret i = scheme.share r secret i :=
  rfl

/-- Authorized coalitions reconstruct the secret from the restricted view. -/
theorem reconstruct_view_eq_secret
    (scheme : Scheme Secret Randomness Party Share)
    (r : Randomness) (secret : Secret) {s : Finset Party}
    (hs : scheme.authorized s) :
    scheme.reconstruct s (scheme.view s r secret) = secret :=
  scheme.correct r secret s hs

/-- Any sub-coalition of an unauthorized coalition is unauthorized as well. -/
theorem not_authorized_of_subset
    (scheme : Scheme Secret Randomness Party Share)
    {s t : Finset Party} (hst : s ⊆ t)
    (ht : ¬ scheme.authorized t) :
    ¬ scheme.authorized s :=
  mt (scheme.authorized_mono hst) ht

end Scheme

end Cslib.Crypto.Protocols.SecretSharing
