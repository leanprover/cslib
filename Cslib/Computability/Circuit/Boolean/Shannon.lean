/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Basic
public import Mathlib.Basic.Real.Basic
import Cslib.Computability.Circuit.Boolean.Counting
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Shannon's circuit lower bound

For all sufficiently large `n`, some Boolean function on `n` inputs requires more
than `2ⁿ/n` De Morgan gates. This matches Lupanov's upper bound asymptotically.

The logarithm of the counting bound is at most `s log s + O(s)` for `n + 1 ≤ s`.
At `s = ⌊2ⁿ/n⌋`, this is smaller than the logarithm of the `2^(2ⁿ)` Boolean functions.

## References

* [Claude E. Shannon, *The Synthesis of Two-Terminal Switching Circuits*][Shannon1949]:
  Theorem 7, Section 3(e), pp. 77-79, the original counting argument for switching circuits.
* [Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]:
  Lemma 1.12 and Theorem 1.14, a modern treatment of Boolean circuit counting.
-/

public section

namespace Cslib.Circuits.Boolean.Shannon

open Filter

-- Bound a single term of the exponential series to estimate the factorial.
private theorem mul_log_sub_le_log_factorial {s : ℕ} (hs : 0 < s) :
    (s : ℝ) * Real.log s - s ≤ Real.log s.factorial := by
  have h := Real.log_le_log (by positivity : 0 < (s : ℝ) ^ s / s.factorial)
    (Real.pow_div_factorial_le_exp (s : ℝ) (by positivity) s)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_exp] at h
  linarith

private theorem exists_card_le_exp :
    ∃ C : ℝ, ∀ n s : ℕ, n + 1 ≤ s →
      ((computableFunctions n s).card : ℝ) ≤ Real.exp ((s : ℝ) * Real.log s + C * s) := by
  refine ⟨Real.log 20 + 5, fun n s hn => ?_⟩
  let a := (computableFunctions n s).card
  by_cases ha : a = 0
  · simp only [show (computableFunctions n s).card = 0 from ha, Nat.cast_zero]
    positivity
  have ha : (0 : ℝ) < a := by exact_mod_cast (Nat.pos_of_ne_zero ha)
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  have hn' : (n : ℝ) + 1 ≤ s := by exact_mod_cast hn
  have hcount : (a : ℝ) * s.factorial ≤ (2 * (s : ℝ)) ^ 2 * (20 * (s : ℝ) ^ 2) ^ s := by
    calc
      (a : ℝ) * s.factorial ≤
          ((s : ℝ) + 1) * (5 * ((n : ℝ) + s + 1) ^ 2) ^ s * (n + s) := by
        exact_mod_cast card_computableFunctions_mul_factorial_le n s
      _ ≤ (2 * s) * (5 * (2 * (s : ℝ)) ^ 2) ^ s * (2 * s) := by gcongr <;> linarith
      _ = _ := by rw [show 5 * (2 * (s : ℝ)) ^ 2 = 20 * s ^ 2 by ring]; ring
  have hlog : Real.log a + Real.log s.factorial ≤
      2 * (Real.log 2 + Real.log s) + s * (Real.log 20 + 2 * Real.log s) := by
    simpa [Real.log_mul, Real.log_pow, ne_of_gt ha, Nat.factorial_ne_zero,
      ne_of_gt (zero_lt_one.trans_le hs)] using
      (Real.log_le_log (by positivity : 0 < (a : ℝ) * s.factorial) hcount)
  apply (Real.log_le_iff_le_exp ha).mp
  have hfactorial := mul_log_sub_le_log_factorial (s := s) (by omega)
  have hlogtwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlogs := Real.log_le_self (by positivity : (0 : ℝ) ≤ s)
  nlinarith

private theorem eventually_inputs_le_budget :
    ∀ᶠ n : ℕ in atTop, n + 1 ≤ 2 ^ n / n := by
  have growth := Asymptotics.isLittleO_iff_nat_mul_le.mp
    (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 2 (by norm_num : (1 : ℝ) < 2)) 2
  filter_upwards [growth, eventually_ge_atTop 1] with n hn hn0
  have hn' : 2 * n ^ 2 ≤ 2 ^ n := by
    exact_mod_cast (by simpa using hn : (2 : ℝ) * n ^ 2 ≤ 2 ^ n)
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  nlinarith

private theorem eventually_card_lt :
    ∀ᶠ n : ℕ in atTop, (computableFunctions n (2 ^ n / n)).card < 2 ^ (2 ^ n) := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨C, hC⟩ := exists_card_le_exp
  obtain ⟨t, ht⟩ := exists_nat_gt (C / Real.log 2)
  have hgap : C < t * Real.log 2 := (div_lt_iff₀ hlogtwo).mp ht
  filter_upwards [eventually_inputs_le_budget, eventually_ge_atTop t,
    eventually_ge_atTop (2 ^ t)] with n hn htn hlarge
  let s := 2 ^ n / n
  have hs : (0 : ℝ) < s := by exact_mod_cast (by dsimp [s]; omega : 0 < s)
  have hshift : s ≤ 2 ^ (n - t) := by
    apply Nat.div_le_of_le_mul
    calc
      2 ^ n = 2 ^ t * 2 ^ (n - t) := by rw [← pow_add, Nat.add_sub_of_le htn]
      _ ≤ n * 2 ^ (n - t) := Nat.mul_le_mul_right _ hlarge
  have hlog : Real.log s ≤ ((n : ℝ) - t) * Real.log 2 := by
    have h := Real.log_le_log hs (show (s : ℝ) ≤ (2 : ℝ) ^ (n - t) by exact_mod_cast hshift)
    simpa [Real.log_pow, Nat.cast_sub htn] using h
  have hsize : (n : ℝ) * s ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.mul_div_le (2 ^ n) n)
  have hexponent : (s : ℝ) * Real.log s + C * s <
      (2 : ℝ) ^ n * Real.log 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hlog hs.le,
      mul_le_mul_of_nonneg_right hsize hlogtwo.le, mul_lt_mul_of_pos_right hgap hs]
  have hcount : ((computableFunctions n s).card : ℝ) < (2 : ℝ) ^ (2 ^ n : ℕ) := by
    calc
      _ ≤ Real.exp ((s : ℝ) * Real.log s + C * s) := hC n s hn
      _ < Real.exp ((2 : ℝ) ^ n * Real.log 2) := Real.exp_lt_exp.mpr hexponent
      _ = (2 : ℝ) ^ (2 ^ n : ℕ) := by
        rw [show (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) by norm_cast,
          Real.exp_nat_mul, Real.exp_log (by norm_num)]
  exact_mod_cast hcount

/-- For all sufficiently large `n`, some Boolean function on `n` inputs requires
more than `2ⁿ/n` De Morgan gates, counting constants and negations. -/
theorem exists_hard_function :
    ∃ N : ℕ, ∀ n ≥ N, ∃ f : BooleanFunction n,
      ∀ {g} (c : Circuit signature n g 1),
        c.Computes f → 2 ^ n / (n : ℝ) < (c.size : ℝ) := by
  classical
  apply eventually_atTop.mp
  filter_upwards [eventually_card_lt, eventually_ge_atTop 1] with n hn hn0
  obtain ⟨f, _, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := computableFunctions n (2 ^ n / n)) (t := Finset.univ)
    (by simpa [BooleanFunction] using hn)
  refine ⟨f, fun {g} c hc => ?_⟩
  have hg : 2 ^ n / n < g := lt_of_not_ge fun hg =>
    hf (mem_computableFunctions.mpr ⟨g, hg, c, hc⟩)
  apply (div_lt_iff₀ (by exact_mod_cast (by omega : 0 < n) : (0 : ℝ) < n)).mpr
  exact_mod_cast (Nat.div_lt_iff_lt_mul (by omega : 0 < n)).mp hg

end Cslib.Circuits.Boolean.Shannon
