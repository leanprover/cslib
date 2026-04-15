/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.PerfectSecrecy.PMFUtilities
public import Cslib.Crypto.Protocols.SecretSharing.Scheme
public import Cslib.Crypto.Protocols.SecretSharing.Internal.ShamirAlgebra
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-!
# Shamir Secret Sharing

This module presents a hardened API for finite-party Shamir secret sharing
through the abstract `SecretSharing.Scheme` interface.

The secure public constructors require two pieces of data:

- public parameters consisting of a threshold together with distinct, nonzero
  evaluation points for a finite party set
- a translation-invariant sampler on the tail coefficients

Translation invariance is exactly the symmetry used in the privacy proof. The
canonical finite-field instance is obtained by taking the sampler to be uniform.
For correctness-only arguments and tests, the internal namespace still exposes a
raw constructor with an arbitrary coefficient distribution.

## Main definitions

- `Cslib.Crypto.Protocols.SecretSharing.Shamir.Params`:
  the threshold and public evaluation points
- `Cslib.Crypto.Protocols.SecretSharing.Shamir.Randomness`:
  the vector of tail coefficients
- `Cslib.Crypto.Protocols.SecretSharing.Shamir.TailSampler`:
  a translation-invariant distribution on tail coefficients
- `Cslib.Crypto.Protocols.SecretSharing.Shamir.schemeWith`:
  Shamir's scheme with a privacy-preserving tail sampler
- `Cslib.Crypto.Protocols.SecretSharing.Shamir.scheme`:
  the corresponding finite-field scheme with uniform randomness

## Main results

- `Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct_view_eq_secret`:
  any authorized coalition reconstructs the secret
- `Cslib.Crypto.Protocols.SecretSharing.Shamir.authorized_univ`:
  the full party set is always authorized

## Notes

The public share type is just the field `F`: the evaluation points are fixed in
`Params`, so one share consists only of the corresponding field value.

## References

* [Adi Shamir, *How to Share a Secret*][Shamir1979]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

noncomputable section

namespace Cslib.Crypto.Protocols.SecretSharing.Shamir

open Polynomial

variable {F Party : Type*} [Field F] [Fintype Party] [DecidableEq Party]

/-- Public parameters for a finite Shamir secret-sharing instance. The threshold
is bundled with the evaluation points so the API can enforce the standard
non-vacuous `threshold < number of parties` side condition. -/
structure Params (F : Type*) [Zero F] (Party : Type*) [Fintype Party] where
  /-- A coalition of size `threshold + 1` is the first authorized size. -/
  threshold : ℕ
  /-- Standard Shamir sharing requires `threshold < number of parties`. -/
  threshold_lt_card : threshold < Fintype.card Party
  /-- The public evaluation point assigned to each party. -/
  point : Party → F
  /-- Distinct parties receive distinct evaluation points. -/
  point_injective : Function.Injective point
  /-- Standard Shamir sharing forbids the point `0`, which would reveal the
  secret directly. -/
  point_nonzero : ∀ i : Party, point i ≠ 0

/-- The random coefficients of the degree-`threshold - 1` tail polynomial. -/
abbrev Randomness (params : Params F Party) := Fin params.threshold → F

/-- A coalition is authorized exactly when it contains at least
`params.threshold + 1` parties. -/
def authorized (params : Params F Party) (s : Finset Party) : Prop :=
  params.threshold + 1 ≤ s.card

/-- Because `params.threshold < |Party|`, the full party set can always
reconstruct the secret. -/
theorem authorized_univ {F Party : Type*} [Field F] [Fintype Party]
    (params : Params F Party) :
    authorized params (Finset.univ : Finset Party) := by
  simpa [authorized] using Nat.succ_le_of_lt params.threshold_lt_card

namespace Internal

/-- Correctness-only Shamir skeleton with an arbitrary coefficient sampler. This
constructor does not carry any privacy guarantee and is intended for internal
proofs and tests. -/
noncomputable def rawSchemeWith (params : Params F Party)
    (gen : PMF (Randomness params)) :
    SecretSharing.Scheme F (Randomness params) Party F where
  gen := gen
  share coeffs secretValue i :=
    (sharingPolynomial secretValue (tailPolynomial params.threshold coeffs)).eval (params.point i)
  reconstruct s σ := reconstruct s params.point σ
  authorized := authorized params
  authorized_mono := by
    intro s u hsu hs
    exact le_trans hs (Finset.card_le_card hsu)
  correct coeffs secretValue s hs := by
    have hdeg₀ :
        (sharingPolynomial secretValue (tailPolynomial params.threshold coeffs)).degree <
          (params.threshold + 1 : WithBot ℕ) :=
      degree_sharingPolynomial_tailPolynomial_lt_succ secretValue params.threshold coeffs
    have hdeg :
        (sharingPolynomial secretValue (tailPolynomial params.threshold coeffs)).degree < s.card :=
      lt_of_lt_of_le hdeg₀ (by exact_mod_cast hs)
    simpa using
      reconstruct_sharingPolynomial_eq_secret
        (x := params.point)
        (secretValue := secretValue)
        (tail := tailPolynomial params.threshold coeffs)
        (params.point_injective.injOn)
        hdeg

@[simp]
theorem rawSchemeWith_authorized_iff (params : Params F Party)
    (gen : PMF (Randomness params)) (s : Finset Party) :
    (rawSchemeWith params gen).authorized s ↔ params.threshold + 1 ≤ s.card :=
  Iff.rfl

@[simp]
theorem rawSchemeWith_share_eq_eval (params : Params F Party)
    (gen : PMF (Randomness params)) (coeffs : Randomness params)
    (secretValue : F) (i : Party) :
    (rawSchemeWith params gen).share coeffs secretValue i =
      (sharingPolynomial secretValue
        (tailPolynomial params.threshold coeffs)).eval (params.point i) :=
  rfl

end Internal

/-- A sampler on Shamir tail coefficients is privacy-compatible when its
distribution is invariant under translation by any coefficient vector. This is
the exact symmetry needed in the privacy proof. -/
structure TailSampler (params : Params F Party) where
  /-- The underlying coefficient distribution. -/
  gen : PMF (Randomness params)
  /-- Translating the coefficients does not change the distribution. -/
  map_add_eq_self : ∀ δ : Randomness params, gen.map (fun coeffs => coeffs + δ) = gen

private def coeffTranslate {params : Params F Party} (δ : Randomness params) :
    Randomness params ≃ Randomness params where
  toFun coeffs := coeffs + δ
  invFun coeffs := coeffs - δ
  left_inv coeffs := by simp
  right_inv coeffs := by simp

/-- Uniform tail coefficients form the canonical privacy-compatible sampler. -/
noncomputable def uniformTailSampler (params : Params F Party)
    [Fintype F] [Nonempty F] : TailSampler params where
  gen := PMF.uniformOfFintype (Randomness params)
  map_add_eq_self δ := by
    simpa [coeffTranslate] using
      (Cslib.Crypto.Protocols.PerfectSecrecy.PMFUtilities.uniformOfFintype_map_equiv
        (coeffTranslate (params := params) δ))

/-- Shamir's scheme built from a privacy-compatible tail sampler. -/
noncomputable def schemeWith (params : Params F Party) (sampler : TailSampler params) :
    SecretSharing.Scheme F (Randomness params) Party F :=
  Internal.rawSchemeWith params sampler.gen

/-- The canonical finite-field Shamir scheme with uniformly sampled tail
coefficients. -/
noncomputable def scheme (params : Params F Party)
    [Fintype F] [Nonempty F] :
    SecretSharing.Scheme F (Randomness params) Party F :=
  schemeWith params (uniformTailSampler params)

@[simp]
theorem schemeWith_authorized_iff (params : Params F Party)
    (sampler : TailSampler params) (s : Finset Party) :
    (schemeWith params sampler).authorized s ↔ params.threshold + 1 ≤ s.card :=
  Iff.rfl

@[simp]
theorem scheme_authorized_iff (params : Params F Party)
    [Fintype F] [Nonempty F] (s : Finset Party) :
    (scheme params).authorized s ↔ params.threshold + 1 ≤ s.card :=
  Iff.rfl

@[simp]
theorem schemeWith_share_eq_eval (params : Params F Party)
    (sampler : TailSampler params) (coeffs : Randomness params)
    (secretValue : F) (i : Party) :
    (schemeWith params sampler).share coeffs secretValue i =
      (Internal.sharingPolynomial secretValue
        (Internal.tailPolynomial params.threshold coeffs)).eval (params.point i) :=
  rfl

/-- Any authorized coalition reconstructs the secret from the shares it sees. -/
theorem reconstruct_view_eq_secret
    (params : Params F Party) (sampler : TailSampler params)
    (coeffs : Randomness params) (secretValue : F) {s : Finset Party}
    (hs : (schemeWith params sampler).authorized s) :
    (schemeWith params sampler).reconstruct s
      ((schemeWith params sampler).view s coeffs secretValue) = secretValue :=
  SecretSharing.Scheme.reconstruct_view_eq_secret
    (schemeWith params sampler) coeffs secretValue hs

end Cslib.Crypto.Protocols.SecretSharing.Shamir
