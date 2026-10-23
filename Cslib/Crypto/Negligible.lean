/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-!
# Negligible functions

Negligible bounds are Mathlib's superpolynomial decay at natural security parameters.
This module supplies zero, comparison, and polynomial-loss bounds for security games.

The decay bound may depend on the whole algorithm. Security definitions quantify over that
algorithm before asserting negligibility; this module does not change that quantifier order.
-/

@[expose] public section

namespace Cslib.Crypto

/-- An advantage is negligible when it decays faster than every inverse polynomial in the
security parameter. This is Mathlib's superpolynomial decay, specialized to natural parameters. -/
abbrev Negligible (ε : ℕ → ℝ) : Prop :=
  Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ)) ε

/-- The zero advantage is negligible. -/
@[simp] theorem negligible_zero : Negligible (fun _ => 0) :=
  Asymptotics.superpolynomialDecay_zero _ _

/-- A pointwise smaller nonnegative advantage is negligible. -/
theorem negligible_of_le {ε δ : ℕ → ℝ} (hδ : Negligible δ)
    (hε : ∀ n, 0 ≤ ε n) (hle : ∀ n, ε n ≤ δ n) : Negligible ε :=
  hδ.trans_abs_le fun n => abs_le_abs_of_nonneg (hε n) (hle n)

/-- Polynomially bounded factors preserve negligible decay, including for signed functions. -/
theorem Negligible.polynomiallyBounded_mul {ε : ℕ → ℝ} {p : ℕ → ℕ}
    (hε : Negligible ε) (hp : PolynomiallyBounded p) :
    Negligible (fun n => (p n : ℝ) * ε n) := by
  obtain ⟨d, hd⟩ := hp
  apply (hε.param_pow_mul d).trans_eventually_abs_le
  filter_upwards [hd] with n hn
  simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply, abs_mul, abs_pow, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (abs_nonneg _)

end Cslib.Crypto
