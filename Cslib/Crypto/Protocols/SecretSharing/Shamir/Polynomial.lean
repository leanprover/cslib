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
# Shamir Secret Sharing: Polynomial Utilities

This file contains the Shamir-specific polynomial and interpolation utilities
used to prove correctness and privacy of the public scheme construction.
-/

noncomputable section

namespace Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial

variable {F : Type*} [Field F]

/-- The tail polynomial determined by the first `n` coefficients. -/
def tailPolynomial (n : ℕ) (coeffs : Fin n → F) : _root_.Polynomial F :=
  ↑((_root_.Polynomial.degreeLTEquiv F n).symm coeffs)

@[simp]
theorem tailPolynomial_coeff (n : ℕ) (coeffs : Fin n → F) (i : Fin n) :
    (tailPolynomial (F := F) n coeffs).coeff i = coeffs i := by
  have h := congrFun
    (LinearEquiv.apply_symm_apply (_root_.Polynomial.degreeLTEquiv F n) coeffs) i
  simpa [tailPolynomial, _root_.Polynomial.degreeLTEquiv] using h

/-- `tailPolynomial n coeffs` has degree `< n` by construction. -/
theorem tailPolynomial_degree_lt (n : ℕ) (coeffs : Fin n → F) :
    (tailPolynomial (F := F) n coeffs).degree < n :=
  _root_.Polynomial.mem_degreeLT.1
    (((_root_.Polynomial.degreeLTEquiv F n).symm coeffs :
      _root_.Polynomial.degreeLT F n)).2

/-- `tailPolynomial` is additive in its coefficient vector. -/
theorem tailPolynomial_add (n : ℕ) (a b : Fin n → F) :
    tailPolynomial (F := F) n (a + b) = tailPolynomial n a + tailPolynomial n b := by
  simp [tailPolynomial]

/-- The standard Shamir sharing polynomial `s + X * q(X)`. -/
def sharingPolynomial (secretValue : F) (tail : _root_.Polynomial F) : _root_.Polynomial F :=
  _root_.Polynomial.C secretValue + _root_.Polynomial.X * tail

@[simp]
theorem sharingPolynomial_eval (secretValue x : F) (tail : _root_.Polynomial F) :
    (sharingPolynomial secretValue tail).eval x = secretValue + x * tail.eval x := by
  simp [sharingPolynomial, mul_comm]

theorem coeff_zero_sharingPolynomial (secretValue : F) (tail : _root_.Polynomial F) :
    (sharingPolynomial secretValue tail).coeff 0 = secretValue := by
  simp [sharingPolynomial]

theorem constantCoeff_sharingPolynomial (secretValue : F) (tail : _root_.Polynomial F) :
    (sharingPolynomial secretValue tail).constantCoeff = secretValue := by
  simpa [_root_.Polynomial.constantCoeff_apply] using
    coeff_zero_sharingPolynomial secretValue tail

/-- If the tail polynomial has degree `< n`, then the sharing polynomial has
natural degree at most `n`. -/
theorem natDegree_sharingPolynomial_le (secretValue : F) (tail : _root_.Polynomial F) {n : ℕ}
    (hdeg : tail.degree < n) :
    (sharingPolynomial secretValue tail).natDegree ≤ n := by
  rw [sharingPolynomial]
  refine (_root_.Polynomial.natDegree_add_le _ _).trans ?_
  rw [max_le_iff]
  constructor
  · rw [_root_.Polynomial.natDegree_C]
    exact Nat.zero_le n
  · by_cases htail : tail = 0
    · simp [htail]
    · rw [_root_.Polynomial.natDegree_X_mul htail]
      have htailDegree : tail.natDegree < n := by
        have := hdeg
        rw [_root_.Polynomial.degree_eq_natDegree htail] at this
        exact_mod_cast this
      exact Nat.succ_le_of_lt htailDegree

/-- If the tail polynomial has degree `< n`, then the sharing polynomial has
degree `< n + 1`. -/
theorem degree_sharingPolynomial_lt_succ (secretValue : F) (tail : _root_.Polynomial F) {n : ℕ}
    (hdeg : tail.degree < n) :
    (sharingPolynomial secretValue tail).degree < (n + 1 : WithBot ℕ) := by
  by_cases hsharing : sharingPolynomial secretValue tail = 0
  · simp [hsharing]
  · rw [_root_.Polynomial.degree_eq_natDegree hsharing]
    exact_mod_cast Nat.lt_succ_of_le (natDegree_sharingPolynomial_le secretValue tail hdeg)

/-- The coefficient-vector version of `degree_sharingPolynomial_lt_succ`. -/
theorem degree_sharingPolynomial_tailPolynomial_lt_succ
    (secretValue : F) (n : ℕ) (coeffs : Fin n → F) :
    (sharingPolynomial secretValue (tailPolynomial n coeffs)).degree <
      (n + 1 : WithBot ℕ) :=
  degree_sharingPolynomial_lt_succ secretValue (tailPolynomial n coeffs)
    (tailPolynomial_degree_lt n coeffs)

variable {ι : Type*} [Fintype ι]

/-- Reconstruct the secret from finitely indexed share values by interpolating
the unique low-degree polynomial that matches them. -/
def reconstruct (x σ : ι → F) : F :=
  by
    classical
    exact (_root_.Lagrange.interpolate Finset.univ x σ).constantCoeff

/-- Reconstruction recovers the constant coefficient of any low-degree
polynomial from its values at distinct points. -/
theorem reconstruct_eq_constantCoeff_of_eval_eq
    {x : ι → F} {p : _root_.Polynomial F}
    (hx : Function.Injective x)
    (hdeg : p.degree < Fintype.card ι) :
    reconstruct x (fun i => p.eval (x i)) = p.constantCoeff := by
  classical
  have hp :
      p = _root_.Lagrange.interpolate Finset.univ x (fun i => p.eval (x i)) :=
    _root_.Lagrange.eq_interpolate
      (s := Finset.univ)
      (v := x)
      hx.injOn
      (by simpa using hdeg)
  simpa [reconstruct] using congrArg _root_.Polynomial.constantCoeff hp.symm

/-- Reconstruction succeeds on the values of a Shamir sharing polynomial once
the finite index type is large enough. -/
theorem reconstruct_sharingPolynomial_eq_secret
    {x : ι → F} {secretValue : F} {tail : _root_.Polynomial F}
    (hx : Function.Injective x)
    (hdeg : (sharingPolynomial secretValue tail).degree < Fintype.card ι) :
    reconstruct x
      (fun i => (sharingPolynomial secretValue tail).eval (x i)) = secretValue := by
  rw [reconstruct_eq_constantCoeff_of_eval_eq
    (p := sharingPolynomial secretValue tail) hx hdeg]
  exact constantCoeff_sharingPolynomial secretValue tail

end Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial
