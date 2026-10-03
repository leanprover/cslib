/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Counting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.SetTheory.Cardinal.Finite

import Cslib.Foundations.Data.Nat.Asymptotics
import Cslib.Foundations.Data.Nat.Factorial
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Shannon's lower bounds for finite carriers

For any fixed finite signature whose operations have arity at most `k ≥ 2`, interpreted
on a finite carrier `U` with `q ≥ 2` elements, `exists_hard_function_of_arity_le` gives a
function on `n` inputs requiring more than `qⁿ / ((k - 1) * n)` gates for all sufficiently
large `n`. The threshold may depend on the signature, carrier, and arity bound.
`exists_hard_function` specializes this to binary bases.

`exists_card_le_exp` bounds the logarithm of the circuit count by
`(k - 1) * s * log s + O(s)` for `n + 1 ≤ s`. At `s = ⌊qⁿ / ((k - 1) * n)⌋`, this is
smaller than the logarithm of the `q^(qⁿ)` functions. This extends the Boolean counting
argument in the references to finite carriers and bounded arities.

`exists_hard_full_function` gives a finite criterion for the full basis with every parameter
explicit, including the arity, without a sufficiently-large-input assumption.

## References

* [Claude E. Shannon, *The Synthesis of Two-Terminal Switching Circuits*][Shannon1949]:
  Theorem 7, Section 3(e), pp. 77-79, the original counting argument for switching circuits.
* [Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]:
  Lemma 1.12 and Theorem 1.14, a modern treatment of Boolean circuit counting.
-/

public section

namespace Cslib.Circuits.Shannon

open Filter

universe v u
variable {σ : Signature.{v}} {U : Type u}

/-- A finite counting bound yields a hard function without asymptotic assumptions. -/
theorem exists_hard_function_of_card_lt [Fintype σ.Op] [Fintype U]
    (I : Interpretation σ U) (n s : ℕ)
    (h : (computableFunctions I n s).card < Fintype.card U ^ (Fintype.card U ^ n)) :
    ∃ f : (Fin n → U) → U, ∀ c : Circuit σ n 1, c.Computes I (single f) → s < c.size := by
  classical
  obtain ⟨f, _, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := computableFunctions I n s) (t := Finset.univ)
    (by simpa using h)
  exact ⟨f, fun c hc => lt_of_not_ge fun hs => hf (mem_computableFunctions.mpr ⟨c, hc, hs⟩)⟩

/-- A finite Shannon criterion for the full basis, valid simultaneously for every arity,
input count, and gate budget. The factorial correction accounts for gate relabelings. -/
theorem exists_hard_full_function [Fintype U] (k n s : ℕ)
    (h : (s + 1) * (max s (Fintype.card U ^ (Fintype.card U ^ k) * (n + s) ^ k +
      Fintype.card U)) ^ s * (n + s) <
        Fintype.card U ^ (Fintype.card U ^ n) * s.factorial) :
    ∃ f : (Fin n → U) → U, ∀ c : Circuit (fullSignature k U) n 1,
      c.Computes fullInterpretation (single f) → s < c.size := by
  classical
  apply exists_hard_function_of_card_lt
  exact (Nat.mul_lt_mul_right (Nat.factorial_pos s)).mp
    ((card_computableFunctions_full_mul_factorial_le (U := U) k n s).trans_lt h)

/-- The logarithm of the circuit count is at most `(k - 1) * s * log s + O(s)` for
any fixed finite basis of arity at most `k`. The factorial correction saves one factor
of `s` per gate compared with counting labeled programs. -/
theorem exists_card_le_exp [Fintype σ.Op] (I : Interpretation σ U)
    {k : ℕ} (hk : 2 ≤ k) (arity_le : ∀ op, σ.Arity op ≤ k) :
    ∃ C : ℝ, ∀ n s : ℕ, n + 1 ≤ s →
      ((computableFunctions I n s).card : ℝ) ≤ Real.exp ((k - 1 : ℝ) * s * Real.log s + C * s) := by
  let q := Fintype.card σ.Op + 1
  have hq : 1 ≤ q := Nat.succ_le_succ (Nat.zero_le _)
  refine ⟨Real.log (2 ^ k * (q : ℝ)) + 5, fun n s hn => ?_⟩
  let a := (computableFunctions I n s).card
  by_cases ha : a = 0
  · simp only [show (computableFunctions I n s).card = 0 from ha, Nat.cast_zero]
    positivity
  have ha : (0 : ℝ) < a := by exact_mod_cast (Nat.pos_of_ne_zero ha)
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast (by lia : 1 ≤ s)
  have hn' : (n : ℝ) + 1 ≤ s := by exact_mod_cast hn
  have hB : s ≤ q * (n + s + 1) ^ k := by
    calc
      s ≤ (n + s + 1) ^ 2 := by nlinarith [Nat.le_mul_self (n + s + 1)]
      _ ≤ (n + s + 1) ^ k := Nat.pow_le_pow_right (by lia) hk
      _ ≤ q * (n + s + 1) ^ k := by
        simpa using Nat.mul_le_mul_right ((n + s + 1) ^ k) hq
  have hlines (g : ℕ) (hg : g ≤ s) : Fintype.card (Line σ n g) ≤ q * (n + s + 1) ^ k :=
    (Line.card_le n g k arity_le).trans (Nat.mul_le_mul (Nat.le_succ _)
      (Nat.pow_le_pow_left (by lia : n + g + 1 ≤ n + s + 1) k))
  have hcount : (a : ℝ) * s.factorial ≤
      (2 * (s : ℝ)) ^ 2 * (2 ^ k * (q : ℝ) * (s : ℝ) ^ k) ^ s := by
    calc
      (a : ℝ) * s.factorial ≤
          ((s : ℝ) + 1) * ((q : ℝ) * ((n : ℝ) + s + 1) ^ k) ^ s * (n + s) := by
        exact_mod_cast card_computableFunctions_mul_factorial_le I n s _ hB hlines
      _ ≤ (2 * s) * ((q : ℝ) * (2 * (s : ℝ)) ^ k) ^ s * (2 * s) := by
        gcongr <;> linarith
      _ = _ := by rw [mul_pow]; ring
  have hlog : Real.log a + Real.log s.factorial ≤
      2 * (Real.log 2 + Real.log s) + s * (Real.log (2 ^ k * (q : ℝ)) + k * Real.log s) := by
    simpa [Real.log_mul, Real.log_pow, ne_of_gt ha, Nat.factorial_ne_zero,
      ne_of_gt (zero_lt_one.trans_le hs)] using
      (Real.log_le_log (by positivity : 0 < (a : ℝ) * s.factorial) hcount)
  apply (Real.log_le_iff_le_exp ha).mp
  have hfactorial := Nat.mul_log_sub_le_log_factorial s
  have hlogtwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlogs := Real.log_le_self (by positivity : (0 : ℝ) ≤ s)
  nlinarith

private theorem eventually_card_lt [Fintype σ.Op] [Fintype U] [Nontrivial U]
    (I : Interpretation σ U) {k : ℕ} (hk : 2 ≤ k) (arity_le : ∀ op, σ.Arity op ≤ k) :
    ∀ᶠ n : ℕ in atTop, (computableFunctions I n (Fintype.card U ^ n / ((k - 1) * n))).card <
      Fintype.card U ^ (Fintype.card U ^ n) := by
  let q := Fintype.card U
  have hq : 1 < q := Fintype.one_lt_card
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by lia : 1 ≤ k), Nat.cast_one]
  have hkR : (0 : ℝ) < (k : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by lia : 1 < k))
  obtain ⟨C, hC⟩ := exists_card_le_exp I hk arity_le
  obtain ⟨t, ht⟩ := exists_nat_gt (C / ((k - 1 : ℝ) * Real.log q))
  have hgap : C < (k - 1 : ℝ) * t * Real.log q := by
    have := (div_lt_iff₀ (mul_pos hkR hlogq)).mp ht
    nlinarith only [this]
  have hbudget : ∀ᶠ n : ℕ in atTop, n + 1 ≤ q ^ n / ((k - 1) * n) := by
    filter_upwards [Nat.eventually_mul_pow_le_pow (2 * (k - 1)) 2 hq,
      eventually_ge_atTop 1] with n hn hn0
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos (by lia) (by lia))).mpr
    nlinarith only [hn, Nat.mul_le_mul_left ((k - 1) * n) hn0]
  filter_upwards [hbudget, eventually_ge_atTop t,
    eventually_ge_atTop (q ^ t)] with n hn htn hlarge
  let s := q ^ n / ((k - 1) * n)
  have hs : (0 : ℝ) < s := by exact_mod_cast (by dsimp [s]; lia : 0 < s)
  have hshift : s ≤ q ^ (n - t) := by
    apply Nat.div_le_of_le_mul
    calc
      q ^ n = q ^ t * q ^ (n - t) := by rw [← pow_add, Nat.add_sub_of_le htn]
      _ ≤ ((k - 1) * n) * q ^ (n - t) := by
        gcongr
        exact hlarge.trans (by simpa using Nat.mul_le_mul_right n (show 1 ≤ k - 1 by lia))
  have hlog : Real.log s ≤ ((n : ℝ) - t) * Real.log q := by
    have h := Real.log_le_log hs (show (s : ℝ) ≤ (q : ℝ) ^ (n - t) by exact_mod_cast hshift)
    simpa [Real.log_pow, Nat.cast_sub htn] using h
  have hsize : (k - 1 : ℝ) * n * s ≤ (q : ℝ) ^ n := by
    rw [← hkcast]
    exact_mod_cast (Nat.mul_div_le (q ^ n) ((k - 1) * n))
  have hexponent : (k - 1 : ℝ) * s * Real.log s + C * s <
      (q : ℝ) ^ n * Real.log q := by
    nlinarith only [mul_le_mul_of_nonneg_left hlog (mul_nonneg hkR.le hs.le),
      mul_le_mul_of_nonneg_right hsize hlogq.le, mul_lt_mul_of_pos_right hgap hs]
  have hcount : ((computableFunctions I n s).card : ℝ) < (q : ℝ) ^ (q ^ n : ℕ) := by
    calc
      _ ≤ Real.exp ((k - 1 : ℝ) * s * Real.log s + C * s) := hC n s hn
      _ < Real.exp ((q : ℝ) ^ n * Real.log q) := Real.exp_lt_exp.mpr hexponent
      _ = (q : ℝ) ^ (q ^ n : ℕ) := by
        rw [show (q : ℝ) ^ n = ((q ^ n : ℕ) : ℝ) by norm_cast,
          Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hqR)]
  exact_mod_cast hcount

/-- For any fixed finite basis of arity at most `k ≥ 2`, sufficiently large input counts
admit a scalar function requiring more than `|U|^n / ((k - 1) * n)` gates. -/
theorem exists_hard_function_of_arity_le [Finite σ.Op] [Finite U] [Nontrivial U]
    (I : Interpretation σ U) {k : ℕ} (hk : 2 ≤ k) (arity_le : ∀ op, σ.Arity op ≤ k) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ f : (Fin n → U) → U,
      ∀ c : Circuit σ n 1,
        c.Computes I (single f) → (Nat.card U : ℝ) ^ n / ((k - 1 : ℝ) * n) < (c.size : ℝ) := by
  classical
  let := Fintype.ofFinite σ.Op
  let := Fintype.ofFinite U
  simp only [Nat.card_eq_fintype_card]
  apply eventually_atTop.mp
  filter_upwards [eventually_card_lt I hk arity_le, eventually_ge_atTop 1] with n hn hn0
  obtain ⟨f, hf⟩ := exists_hard_function_of_card_lt I n
    (Fintype.card U ^ n / ((k - 1) * n)) hn
  refine ⟨f, fun c hc => ?_⟩
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by lia : 1 ≤ k), Nat.cast_one]
  rw [← hkcast]
  have hden : 0 < (k - 1) * n := Nat.mul_pos (by lia) (by lia)
  apply (div_lt_iff₀ (by exact_mod_cast hden : (0 : ℝ) < (k - 1 : ℕ) * n)).mpr
  exact_mod_cast (Nat.div_lt_iff_lt_mul hden).mp (hf c hc)

/-- For all sufficiently large `n`, some function on `n` inputs over `U` requires more than
`|U|ⁿ/n` gates over the fixed finite signature, whose operations have arity at most two. -/
theorem exists_hard_function [Finite σ.Op] [Finite U] [Nontrivial U]
    (I : Interpretation σ U) (arity_le : ∀ op, σ.Arity op ≤ 2) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ f : (Fin n → U) → U,
      ∀ c : Circuit σ n 1,
        c.Computes I (single f) → (Nat.card U : ℝ) ^ n / n < (c.size : ℝ) := by
  have := exists_hard_function_of_arity_le I (by decide : 2 ≤ 2) arity_le
  norm_num at this
  exact this

end Cslib.Circuits.Shannon
