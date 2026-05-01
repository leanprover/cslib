/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Crypto.Protocols.SecretSharing.Scheme
public import Mathlib.Probability.Distributions.Uniform
public import Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial
import Cslib.Probability.PMF

@[expose] public section

/-!
# Shamir Secret Sharing

This module presents a secure-by-construction API for finite-party Shamir secret
sharing through the abstract `SecretSharing.Scheme` interface.

The public constructors require two pieces of data:

- public parameters consisting of a threshold together with distinct, nonzero
  evaluation points for a finite party set
- a translation-invariant sampler on the tail coefficients

Translation invariance is exactly the symmetry used in the privacy proof. The
canonical finite-field instance is obtained by taking the sampler to be uniform.

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

variable {F Party : Type*} [Field F] [Fintype Party]

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

/-- The Shamir share value sent to one party. -/
noncomputable def share (params : Params F Party)
    (coeffs : Randomness params) (secretValue : F) (i : Party) : F :=
  (Polynomial.sharingPolynomial secretValue
    (Polynomial.tailPolynomial params.threshold coeffs)).eval (params.point i)

/-- Reconstruct the secret from one coalition's Shamir shares. -/
noncomputable def reconstruct (params : Params F Party)
    (s : Finset Party) (σ : s → F) : F :=
  Polynomial.reconstruct (fun i : s => params.point i) σ

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
      (Cslib.Probability.PMF.uniformOfFintype_map_equiv
        (coeffTranslate (params := params) δ))

private noncomputable def privacyCorrectionPolynomial
    (params : Params F Party) (s : Finset Party)
    (secret₀ secret₁ : F) : _root_.Polynomial F :=
  by
    classical
    exact _root_.Lagrange.interpolate s.attach (fun i : s => params.point i)
      (fun i : s => (secret₀ - secret₁) / params.point i)

private theorem points_injOn_subtype {F Party : Type*} [Field F] [Fintype Party]
    (params : Params F Party) (s : Finset Party) :
    Set.InjOn (fun i : s => params.point i) (s.attach : Finset s) := by
  intro i _ j _ hij
  apply Subtype.ext
  exact params.point_injective hij

private theorem privacyCorrectionPolynomial_eval
    (params : Params F Party) (s : Finset Party)
    (secret₀ secret₁ : F) (i : s) :
    (privacyCorrectionPolynomial (F := F) params s secret₀ secret₁).eval (params.point i) =
      (secret₀ - secret₁) / params.point i := by
  classical
  simpa using
    (_root_.Lagrange.eval_interpolate_at_node
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
  classical
  refine lt_of_lt_of_le
    (_root_.Lagrange.degree_interpolate_lt
      (s := s.attach)
      (v := fun i : s => params.point i)
      (r := fun i : s => (secret₀ - secret₁) / params.point i)
      (points_injOn_subtype (F := F) params s))
    ?_
  simpa using hcard

private noncomputable def privacyCorrection
    (params : Params F Party) (s : Finset Party)
    (hcard : s.card ≤ params.threshold)
    (secret₀ secret₁ : F) : Randomness params :=
  _root_.Polynomial.degreeLTEquiv F params.threshold
    ⟨privacyCorrectionPolynomial (F := F) params s secret₀ secret₁,
      _root_.Polynomial.mem_degreeLT.2
        (privacyCorrectionPolynomial_degree_lt (F := F) params s secret₀ secret₁ hcard)⟩

private theorem tailPolynomial_privacyCorrection
    (params : Params F Party) (s : Finset Party)
    (hcard : s.card ≤ params.threshold)
    (secret₀ secret₁ : F) :
    Polynomial.tailPolynomial (F := F) params.threshold
        (privacyCorrection (F := F) params s hcard secret₀ secret₁) =
      privacyCorrectionPolynomial (F := F) params s secret₀ secret₁ := by
  simp [privacyCorrection, Polynomial.tailPolynomial]

private theorem view_eq_view_add_privacyCorrection
    (params : Params F Party) (s : Finset Party)
    (hcard : s.card ≤ params.threshold)
    (secret₀ secret₁ : F) (coeffs : Randomness params) :
    (fun i : s => share params coeffs secret₀ i) =
      (fun i : s =>
        share params
          (coeffs + privacyCorrection (F := F) params s hcard secret₀ secret₁)
          secret₁ i) := by
  ext i
  unfold share
  rw [Polynomial.sharingPolynomial_eval, Polynomial.sharingPolynomial_eval]
  rw [Polynomial.tailPolynomial_add, _root_.Polynomial.eval_add, tailPolynomial_privacyCorrection]
  rw [privacyCorrectionPolynomial_eval (F := F) params s secret₀ secret₁ i]
  field_simp [params.point_nonzero i]
  ring

/-- Translation-invariant Shamir tail samplers induce secret-independent views
for unauthorized coalitions. -/
theorem view_indist_of_tailSampler (params : Params F Party)
    (sampler : TailSampler params) :
    ∀ (s : Finset Party), ¬ authorized params s → ∀ secret₀ secret₁ : F,
      viewDistOf sampler.gen (share params) s secret₀ =
        viewDistOf sampler.gen (share params) s secret₁ := by
  intro s hs secret₀ secret₁
  have hcard : s.card ≤ params.threshold := by
    have hs' : ¬ params.threshold + 1 ≤ s.card := by
      simpa [authorized] using hs
    exact Nat.lt_succ_iff.mp (Nat.not_le.mp hs')
  unfold viewDistOf
  calc
    PMF.map (fun coeffs : Randomness params =>
        (fun i : s => share params coeffs secret₀ i : s → F)) sampler.gen =
      PMF.map
        (fun coeffs : Randomness params => (fun i : s =>
          share params
            (coeffs + privacyCorrection (F := F) params s hcard secret₀ secret₁)
            secret₁ i : s → F)) sampler.gen := by
        congr 1
        funext coeffs
        exact view_eq_view_add_privacyCorrection
          (F := F) params s hcard secret₀ secret₁ coeffs
    _ = PMF.map (fun coeffs : Randomness params =>
          (fun i : s => share params coeffs secret₁ i : s → F))
        (PMF.map
          (fun coeffs => coeffs + privacyCorrection (F := F) params s hcard secret₀ secret₁)
          sampler.gen) := by
          rw [PMF.map_comp]
          rfl
    _ = PMF.map (fun coeffs : Randomness params =>
          (fun i : s => share params coeffs secret₁ i : s → F)) sampler.gen := by
          rw [sampler.map_add_eq_self]

/-- Shamir's scheme built from a privacy-compatible tail sampler. -/
noncomputable def schemeWith (params : Params F Party) (sampler : TailSampler params)
    :
    SecretSharing.Scheme F (Randomness params) Party F :=
  { gen := sampler.gen
    share := share params
    reconstruct := reconstruct params
    authorized := authorized params
    authorized_mono := by
      intro s u hsu hs
      exact le_trans hs (Finset.card_le_card hsu)
    correct := by
      intro coeffs secretValue s hs
      have hdeg₀ :
          (Polynomial.sharingPolynomial secretValue
              (Polynomial.tailPolynomial params.threshold coeffs)).degree <
            (params.threshold + 1 : WithBot ℕ) :=
        Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ
          secretValue params.threshold coeffs
      have hdeg :
          (Polynomial.sharingPolynomial secretValue
              (Polynomial.tailPolynomial params.threshold coeffs)).degree <
            Fintype.card s := by
        simpa using
          (lt_of_lt_of_le hdeg₀ (by exact_mod_cast hs) :
            (Polynomial.sharingPolynomial secretValue
                (Polynomial.tailPolynomial params.threshold coeffs)).degree <
              s.card)
      have hx : Function.Injective (fun i : s => params.point i) := by
        intro i j hij
        exact Subtype.ext (params.point_injective hij)
      simpa [share, reconstruct] using
        Polynomial.reconstruct_sharingPolynomial_eq_secret
          (x := fun i : s => params.point i)
          (secretValue := secretValue)
          (tail := Polynomial.tailPolynomial params.threshold coeffs)
          hx
          hdeg
    view_indist := view_indist_of_tailSampler params sampler }

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
theorem schemeWith_share_eq (params : Params F Party)
    (sampler : TailSampler params) (coeffs : Randomness params)
    (secretValue : F) (i : Party) :
    (schemeWith params sampler).share coeffs secretValue i =
      share params coeffs secretValue i :=
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
