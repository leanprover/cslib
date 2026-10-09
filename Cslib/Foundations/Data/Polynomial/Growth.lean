/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Cslib.Foundations.Data.Polynomial.Monotone
public import Mathlib.Tactic.FunProp
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Polynomial bounds and polynomial expressions

The growth condition `PolynomiallyBounded` does not prescribe how bounds are represented.
Polynomials over `ℕ` provide convenient monotone majorants for composing concrete estimates.
-/

@[expose] public section

namespace Cslib

open Polynomial

/-- Polynomial growth is equivalent to a pointwise bound by a natural-coefficient polynomial. -/
theorem polynomiallyBounded_iff_polynomial {f : ℕ → ℕ} :
    PolynomiallyBounded f ↔ ∃ p : ℕ[X], ∀ n, f n ≤ p.eval n := by
  rw [polynomiallyBounded_iff_le]
  constructor
  · rintro ⟨c, d, h⟩
    exact ⟨C c * (X + 1) ^ d, by simpa using h⟩
  · rintro ⟨p, h⟩
    refine ⟨p.eval 1, p.natDegree, fun n => (h n).trans ?_⟩
    rw [eval_eq_sum_range, eval_eq_sum_range, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    simp only [one_pow, mul_one]
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (by lia : n ≤ n + 1) i).trans
      (Nat.pow_le_pow_right (by lia) (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi))

namespace PolynomiallyBounded

variable {f g : ℕ → ℕ}

/-- Any pointwise smaller natural-valued function has the same growth bound. -/
theorem mono (hg : PolynomiallyBounded g) (h : ∀ n, f n ≤ g n) : PolynomiallyBounded f := by
  obtain ⟨d, hd⟩ := hg
  exact ⟨d, hd.mono fun n hn => (h n).trans hn⟩

attribute [fun_prop] PolynomiallyBounded

/-- A polynomial expression has polynomial growth. -/
@[fun_prop] theorem eval (p : ℕ[X]) : PolynomiallyBounded (fun n => p.eval n) :=
  polynomiallyBounded_iff_polynomial.mpr ⟨p, fun _ => le_rfl⟩

/-- Constant functions have polynomial growth. -/
@[fun_prop] theorem const (c : ℕ) : PolynomiallyBounded (fun _ => c) := by
  simpa using eval (C c)

/-- The identity function has polynomial growth. -/
@[fun_prop] theorem id : PolynomiallyBounded (fun n => n) := by
  simpa using eval X

/-- Sums preserve polynomial growth. -/
@[fun_prop] theorem add (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n + g n) := by
  obtain ⟨p, hp⟩ := polynomiallyBounded_iff_polynomial.mp hf
  obtain ⟨q, hq⟩ := polynomiallyBounded_iff_polynomial.mp hg
  exact (eval (p + q)).mono fun n => by simpa using Nat.add_le_add (hp n) (hq n)

/-- Products preserve polynomial growth. -/
@[fun_prop] theorem mul (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n * g n) := by
  obtain ⟨p, hp⟩ := polynomiallyBounded_iff_polynomial.mp hf
  obtain ⟨q, hq⟩ := polynomiallyBounded_iff_polynomial.mp hg
  exact (eval (p * q)).mono fun n => by simpa using Nat.mul_le_mul (hp n) (hq n)

/-- Fixed powers preserve polynomial growth. -/
@[fun_prop] theorem pow (hf : PolynomiallyBounded f) (k : ℕ) :
    PolynomiallyBounded (fun n => f n ^ k) := by
  obtain ⟨p, hp⟩ := polynomiallyBounded_iff_polynomial.mp hf
  exact (eval (p ^ k)).mono fun n => by simpa using Nat.pow_le_pow_left (hp n) k

/-- Composition preserves polynomial growth. -/
@[fun_prop] theorem comp (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f (g n)) := by
  obtain ⟨p, hp⟩ := polynomiallyBounded_iff_polynomial.mp hf
  obtain ⟨q, hq⟩ := polynomiallyBounded_iff_polynomial.mp hg
  exact (eval (p.comp q)).mono fun n => by
    simpa using (hp (g n)).trans (p.eval_mono (hq n))

/-- Every bound has a monotone majorant with polynomial growth. -/
theorem exists_monotone (hf : PolynomiallyBounded f) :
    ∃ g : ℕ → ℕ, Monotone g ∧ PolynomiallyBounded g ∧ ∀ n, f n ≤ g n := by
  obtain ⟨p, hp⟩ := polynomiallyBounded_iff_polynomial.mp hf
  exact ⟨fun n => p.eval n, p.monotone_eval, eval p, hp⟩

/-- Maxima preserve polynomial growth. -/
@[fun_prop] theorem max (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => max (f n) (g n)) :=
  (hf.add hg).mono fun n => by lia

/-- Minima preserve polynomial growth. -/
@[fun_prop] theorem min (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => min (f n) (g n)) :=
  (hf.add hg).mono fun n => by lia

end PolynomiallyBounded
end Cslib
