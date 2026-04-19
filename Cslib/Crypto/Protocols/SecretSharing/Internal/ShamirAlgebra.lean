/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# Shamir Secret Sharing: Algebraic Core

This internal file contains the interpolation lemmas used to prove correctness
of the public Shamir scheme construction and privacy of the corresponding
finite-field instance.
-/

noncomputable section

namespace Cslib.Crypto.Protocols.SecretSharing.Shamir.Internal

open Polynomial

variable {F : Type*} [Field F]

/-- The secret carried by a sharing polynomial is its value at `0`. -/
def secret (p : F[X]) : F :=
  p.eval 0

@[simp]
theorem secret_eq_coeff_zero (p : F[X]) : secret p = p.coeff 0 :=
  (Polynomial.coeff_zero_eq_eval_zero p).symm

/-- The tail polynomial determined by the first `n` coefficients. -/
def tailPolynomial (n : ℕ) (coeffs : Fin n → F) : F[X] :=
  ↑((Polynomial.degreeLTEquiv F n).symm coeffs)

@[simp]
theorem tailPolynomial_coeff (n : ℕ) (coeffs : Fin n → F) (i : Fin n) :
    (tailPolynomial (F := F) n coeffs).coeff i = coeffs i := by
  have h := congrFun (LinearEquiv.apply_symm_apply (Polynomial.degreeLTEquiv F n) coeffs) i
  simpa [tailPolynomial, Polynomial.degreeLTEquiv] using h

/-- `tailPolynomial n coeffs` has degree `< n` by construction. -/
theorem tailPolynomial_degree_lt (n : ℕ) (coeffs : Fin n → F) :
    (tailPolynomial (F := F) n coeffs).degree < n :=
  Polynomial.mem_degreeLT.1
    (((Polynomial.degreeLTEquiv F n).symm coeffs : Polynomial.degreeLT F n)).2

/-- The standard Shamir sharing polynomial `s + X * q(X)`. -/
def sharingPolynomial (secretValue : F) (tail : F[X]) : F[X] :=
  C secretValue + X * tail

@[simp]
theorem sharingPolynomial_eval (secretValue x : F) (tail : F[X]) :
    (sharingPolynomial secretValue tail).eval x = secretValue + x * tail.eval x := by
  simp [sharingPolynomial, mul_comm]

@[simp]
theorem coeff_zero_sharingPolynomial (secretValue : F) (tail : F[X]) :
    (sharingPolynomial secretValue tail).coeff 0 = secretValue := by
  simp [sharingPolynomial]

theorem secret_sharingPolynomial (secretValue : F) (tail : F[X]) :
    secret (sharingPolynomial secretValue tail) = secretValue := by
  simp [secret_eq_coeff_zero]

/-- If the tail polynomial has degree `< n`, then the sharing polynomial has
degree `< n + 1`. -/
theorem degree_sharingPolynomial_lt_succ (secretValue : F) (tail : F[X]) {n : ℕ}
    (hdeg : tail.degree < n) :
    (sharingPolynomial secretValue tail).degree < (n + 1 : WithBot ℕ) := by
  have hadd := Polynomial.degree_add_le (C secretValue) ((X : F[X]) * tail)
  simp only [sharingPolynomial] at hadd ⊢
  refine lt_of_le_of_lt hadd (max_lt ?_ ?_)
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Nat.succ_pos n)
  · by_cases htail : tail = 0
    · simp [htail]
    · rw [mul_comm, Polynomial.degree_mul_X, Polynomial.degree_eq_natDegree htail]
      have := Polynomial.degree_eq_natDegree htail ▸ hdeg
      exact_mod_cast Nat.succ_lt_succ (by exact_mod_cast this)

/-- The coefficient-vector version of `degree_sharingPolynomial_lt_succ`. -/
theorem degree_sharingPolynomial_tailPolynomial_lt_succ
    (secretValue : F) (n : ℕ) (coeffs : Fin n → F) :
    (sharingPolynomial secretValue (tailPolynomial n coeffs)).degree <
      (n + 1 : WithBot ℕ) :=
  degree_sharingPolynomial_lt_succ secretValue (tailPolynomial n coeffs)
    (tailPolynomial_degree_lt n coeffs)

variable {ι : Type*} [DecidableEq ι]

/-- Reconstruct the secret from a coalition's share values by interpolating the
unique low-degree polynomial that matches them. -/
def reconstruct (s : Finset ι) (x : ι → F) (σ : s → F) : F :=
  secret <| Lagrange.interpolate s.attach (fun i : s => x i) σ

/-- If a polynomial of degree `< s.card` matches the observed share values on
the coalition `s`, reconstruction recovers its secret. -/
theorem reconstruct_eq_secret_of_eval_eq
    {s : Finset ι} {x : ι → F} {σ : s → F} {p : F[X]}
    (hx : Set.InjOn x s)
    (hvalues : ∀ i : s, σ i = p.eval (x i))
    (hdeg : p.degree < s.card) :
    reconstruct s x σ = secret p := by
  have hx' : Set.InjOn (fun i : s => x i) (s.attach : Finset s) := by
    intro i _ j _ hij
    apply Subtype.ext
    exact hx i.property j.property hij
  have hp :
      p = Lagrange.interpolate s.attach (fun i : s => x i) σ :=
    Lagrange.eq_interpolate_of_eval_eq
      (s := s.attach)
      (v := fun i : s => x i)
      (r := σ)
      hx'
      (by simpa using hdeg)
      (by
        intro i hi
        simpa using (hvalues i).symm)
  simpa [reconstruct, secret] using congrArg (fun q : F[X] => q.eval 0) hp.symm

/-- Reconstruction succeeds on the values of a Shamir sharing polynomial once
the coalition is large enough. -/
theorem reconstruct_sharingPolynomial_eq_secret
    {s : Finset ι} {x : ι → F} {secretValue : F} {tail : F[X]}
    (hx : Set.InjOn x s)
    (hdeg : (sharingPolynomial secretValue tail).degree < s.card) :
    reconstruct s x
      (fun i : s => (sharingPolynomial secretValue tail).eval (x i)) = secretValue := by
  rw [reconstruct_eq_secret_of_eval_eq
    (σ := fun i : s => (sharingPolynomial secretValue tail).eval (x i))
    (p := sharingPolynomial secretValue tail) hx (by intro i; rfl) hdeg]
  exact secret_sharingPolynomial secretValue tail

end Cslib.Crypto.Protocols.SecretSharing.Shamir.Internal
