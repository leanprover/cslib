/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Asymptotic bounds on natural numbers

For any natural base greater than one, exponentials eventually dominate fixed multiples of
powers, and fixed multiples of logarithms are eventually at most the input. The inequalities
are stated in `ℕ`; the polynomial bound specializes Mathlib's
`isLittleO_pow_const_const_pow_of_one_lt`.
-/

public section

open Filter

namespace Nat

/-- Every fixed multiple of a power is eventually at most an exponential of base greater
than one. -/
theorem eventually_mul_pow_le_pow (c k : ℕ) {b : ℕ} (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop, c * n ^ k ≤ b ^ n := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have h := Asymptotics.isLittleO_iff_nat_mul_le.mp
    (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k hbR) c
  filter_upwards [h] with n hn
  exact_mod_cast (by simpa using hn : (c : ℝ) * n ^ k ≤ (b : ℝ) ^ n)

/-- Every fixed multiple of the logarithm in a base greater than one is eventually at most
the input. -/
theorem eventually_mul_log_le (c : ℕ) {b : ℕ} (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop, c * log b n ≤ n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_mul_pow_le_pow c 1 hb)
  filter_upwards [eventually_ge_atTop (b ^ N)] with n hn
  have hn0 : n ≠ 0 := ne_of_gt ((pow_pos (by omega) N).trans_le hn)
  have hh : c * log b n ≤ b ^ log b n := by
    simpa using hN (log b n) (le_log_of_pow_le hb hn)
  exact hh.trans (pow_log_le_self b hn0)

/-- Every fixed multiple of the binary logarithm is eventually at most the input. -/
theorem eventually_mul_log2_le (c : ℕ) :
    ∀ᶠ n : ℕ in atTop, c * log2 n ≤ n := by
  simpa only [log2_eq_log_two] using eventually_mul_log_le c one_lt_two

end Nat
