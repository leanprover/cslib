/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.SecretSharing.Basic
public import Cslib.Crypto.Protocols.SecretSharing.Shamir

@[expose] public section

/-!
# Shamir Secret Sharing: Privacy

This file proves the standard privacy statement for the public
`SecretSharing.Scheme` interface instantiated by Shamir secret sharing.

The key assumption is no longer “uniform coefficients” at the API boundary.
Instead, the public constructor `Shamir.schemeWith` accepts only
translation-invariant tail samplers, and that symmetry is exactly what the
privacy proof uses. The canonical finite-field construction arises by taking
the sampler to be uniform.

## Main results

- `Cslib.Crypto.Protocols.SecretSharing.Shamir.schemeWith_viewIndist`:
  unauthorized coalitions have secret-independent view distributions for any
  translation-invariant sampler
- `Cslib.Crypto.Protocols.SecretSharing.Shamir.viewIndist`:
  the canonical finite-field scheme has secret-independent views
- `Cslib.Crypto.Protocols.SecretSharing.Shamir.schemeWith_perfectlyPrivate`:
  any translation-invariant Shamir instance has posterior privacy
- `Cslib.Crypto.Protocols.SecretSharing.Shamir.perfectlyPrivate`:
  the canonical finite-field scheme has posterior privacy

## References

* [Adi Shamir, *How to Share a Secret*][Shamir1979]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

noncomputable section

namespace Cslib.Crypto.Protocols.SecretSharing.Shamir

open Polynomial

variable {F Party : Type*} [Field F] [Fintype Party] [DecidableEq Party]

/-- The interpolation correction polynomial that compensates for changing the
secret from `secret₀` to `secret₁` on the observed coalition. -/
private noncomputable def privacyCorrectionPolynomial
    (params : Params F Party) (s : Finset Party)
    (secret₀ secret₁ : F) : F[X] :=
  Lagrange.interpolate s.attach (fun i : s => params.point i)
    (fun i : s => (secret₀ - secret₁) / params.point i)

private theorem points_injOn_subtype {F Party : Type*} [Field F] [Fintype Party]
    (params : Params F Party) (s : Finset Party) :
    Set.InjOn (fun i : s => params.point i) (s.attach : Finset s) := by
  intro i _ j _ hij
  apply Subtype.ext
  exact params.point_injective hij

/-- The correction polynomial has the prescribed values on the observed
evaluation points. -/
private theorem privacyCorrectionPolynomial_eval
    (params : Params F Party) (s : Finset Party)
    (secret₀ secret₁ : F) (i : s) :
    (privacyCorrectionPolynomial (F := F) params s secret₀ secret₁).eval (params.point i) =
      (secret₀ - secret₁) / params.point i := by
  simpa using
    (Lagrange.eval_interpolate_at_node
      (s := s.attach)
      (v := fun j : s => params.point j)
      (r := fun j : s => (secret₀ - secret₁) / params.point j)
      (points_injOn_subtype (F := F) params s)
      (by simp))

private theorem privacyCorrectionPolynomial_degree_lt
    (params : Params F Party) (s : Finset Party)
    (secret₀ secret₁ : F) (hcard : s.card ≤ params.threshold) :
    (privacyCorrectionPolynomial (F := F) params s secret₀ secret₁).degree <
      params.threshold := by
  refine lt_of_lt_of_le
    (Lagrange.degree_interpolate_lt
      (s := s.attach)
      (v := fun i : s => params.point i)
      (r := fun i : s => (secret₀ - secret₁) / params.point i)
      (points_injOn_subtype (F := F) params s))
    ?_
  simpa using hcard

/-- Re-encode the correction polynomial as a coefficient vector in the Shamir
randomness space. -/
private noncomputable def privacyCorrection
    (params : Params F Party) (s : Finset Party)
    (hcard : s.card ≤ params.threshold)
    (secret₀ secret₁ : F) : Randomness params :=
  Polynomial.degreeLTEquiv F params.threshold
    ⟨privacyCorrectionPolynomial (F := F) params s secret₀ secret₁,
      Polynomial.mem_degreeLT.2
        (privacyCorrectionPolynomial_degree_lt (F := F) params s secret₀ secret₁ hcard)⟩

private theorem tailPolynomial_add {F Party : Type*} [Field F] [Fintype Party]
    (params : Params F Party)
    (a b : Randomness params) :
    Internal.tailPolynomial (F := F) params.threshold (a + b) =
      Internal.tailPolynomial params.threshold a +
        Internal.tailPolynomial params.threshold b := by
  simp [Internal.tailPolynomial]

private theorem tailPolynomial_privacyCorrection
    (params : Params F Party) (s : Finset Party)
    (hcard : s.card ≤ params.threshold)
    (secret₀ secret₁ : F) :
    Internal.tailPolynomial (F := F) params.threshold
        (privacyCorrection (F := F) params s hcard secret₀ secret₁) =
      privacyCorrectionPolynomial (F := F) params s secret₀ secret₁ := by
  simp [privacyCorrection, Internal.tailPolynomial]

/-- Changing the secret can be compensated by translating the tail coefficients,
so the observed coalition view is unchanged. -/
private theorem view_eq_view_add_privacyCorrection
    (params : Params F Party) (s : Finset Party)
    (hcard : s.card ≤ params.threshold)
    (sampler : TailSampler params)
    (secret₀ secret₁ : F) (coeffs : Randomness params) :
    (schemeWith params sampler).view s coeffs secret₀ =
      (schemeWith params sampler).view s
        (coeffs + privacyCorrection (F := F) params s hcard secret₀ secret₁) secret₁ := by
  ext i
  rw [SecretSharing.Scheme.view_apply, SecretSharing.Scheme.view_apply]
  rw [schemeWith_share_eq_eval, schemeWith_share_eq_eval]
  rw [Internal.sharingPolynomial_eval, Internal.sharingPolynomial_eval]
  rw [tailPolynomial_add, eval_add, tailPolynomial_privacyCorrection]
  rw [privacyCorrectionPolynomial_eval (F := F) params s secret₀ secret₁ i]
  field_simp [params.point_nonzero i]
  ring

/-- Coalitions of size at most `params.threshold` have secret-independent view
distributions for any translation-invariant Shamir sampler. -/
theorem schemeWith_viewIndist (params : Params F Party)
    (sampler : TailSampler params) :
    (schemeWith params sampler).ViewIndist := by
  intro s hs secret₀ secret₁
  have hcard : s.card ≤ params.threshold := by
    have hs' : ¬ params.threshold + 1 ≤ s.card := by
      simpa [schemeWith_authorized_iff] using hs
    exact Nat.lt_succ_iff.mp (Nat.not_le.mp hs')
  unfold SecretSharing.Scheme.viewDist
  calc
    sampler.gen.map
        (fun coeffs => (schemeWith params sampler).view s coeffs secret₀) =
      sampler.gen.map
        (fun coeffs => (schemeWith params sampler).view s
          (coeffs + privacyCorrection (F := F) params s hcard secret₀ secret₁)
          secret₁) := by
        congr
        funext coeffs
        exact view_eq_view_add_privacyCorrection
          (F := F) params s hcard sampler secret₀ secret₁ coeffs
    _ = (sampler.gen.map
          (fun coeffs => coeffs + privacyCorrection (F := F) params s hcard secret₀ secret₁)).map
            (fun coeffs => (schemeWith params sampler).view s coeffs secret₁) := by
          rw [PMF.map_comp]
          rfl
    _ = sampler.gen.map
          (fun coeffs => (schemeWith params sampler).view s coeffs secret₁) := by
          rw [sampler.map_add_eq_self]

/-- The canonical finite-field Shamir scheme has secret-independent view
distributions for unauthorized coalitions. -/
theorem viewIndist (params : Params F Party)
    [Fintype F] [Nonempty F] :
    (scheme params).ViewIndist := by
  simpa [scheme] using
    (schemeWith_viewIndist (F := F) params (uniformTailSampler params))

/-- Any translation-invariant Shamir instance is perfectly private against
unauthorized coalitions. -/
theorem schemeWith_perfectlyPrivate (params : Params F Party)
    (sampler : TailSampler params) :
    (schemeWith params sampler).PerfectlyPrivate :=
  SecretSharing.Scheme.perfectlyPrivate_of_viewIndist
    (schemeWith params sampler) (schemeWith_viewIndist (F := F) params sampler)

/-- The canonical finite-field Shamir scheme is perfectly private against
unauthorized coalitions. -/
theorem perfectlyPrivate (params : Params F Party)
    [Fintype F] [Nonempty F] :
    (scheme params).PerfectlyPrivate :=
  SecretSharing.Scheme.perfectlyPrivate_of_viewIndist
    (scheme params) (viewIndist (F := F) params)

end Cslib.Crypto.Protocols.SecretSharing.Shamir
