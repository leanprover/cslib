/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A logarithmic lower bound for the factorial

Bounding one term of the exponential series gives `n log n - n ≤ log (n!)`, including at zero.
-/

public section

namespace Nat

/-- The logarithm of the factorial is at least `n log n - n`. -/
theorem mul_log_sub_le_log_factorial (n : ℕ) :
    (n : ℝ) * Real.log n - n ≤ Real.log n.factorial := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  have h := Real.log_le_log (by positivity : 0 < (n : ℝ) ^ n / n.factorial)
    (Real.pow_div_factorial_le_exp (n : ℝ) (by positivity) n)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_exp] at h
  linarith

end Nat
