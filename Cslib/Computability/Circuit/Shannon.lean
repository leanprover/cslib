/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Counting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Cslib.Computability.Circuit.Full
import Cslib.Foundations.Data.Nat.Asymptotics
import Cslib.Foundations.Data.Nat.Factorial
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Shannon's lower bounds for finite carriers

For any fixed finite signature whose operations have arity at most `k ≥ 2`, interpreted
on a finite carrier `U` with `q ≥ 2` elements, almost all functions on `n` inputs require
more than `qⁿ / ((k - 1) * n)` gates: the fraction of functions computable within that budget
tends to zero. Hence, for all sufficiently large `n`, some function requires more than
`qⁿ / ((k - 1) * n)` gates; the threshold may depend on the signature, carrier, and arity
bound. This also holds when the signature has infinitely many operations, because the full
basis of arity `k` simulates every signature of arity at most `k` gate by gate, so its hard
functions are hard for all of them. `tendsto_card_computableFunctions_div` and
`exists_hard_function` specialize this to binary bases. For the De Morgan basis on `Bool`,
this matches Lupanov's upper bound asymptotically.

`exists_card_le_exp` bounds the logarithm of the circuit count by
`(k - 1) * s * log s + O(s)` for `n + 1 ≤ s`. At `s = ⌊qⁿ / ((k - 1) * n)⌋`, this is
smaller than the logarithm of the `q^(qⁿ)` functions by at least `s`. This extends the
Boolean counting argument in the references to finite carriers and bounded arities.

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

open Filter Topology
open Nat (card)

universe v u
variable {σ : Signature.{v}} {U : Type u}

/-- A finite counting bound yields a hard function without asymptotic assumptions. -/
theorem exists_hard_function_of_card_lt [Finite σ.Op] [Finite U]
    (I : Interpretation σ U) (n s : ℕ)
    (h : (computableFunctions I n s).ncard < card U ^ (card U ^ n)) :
    ∃ f : (Fin n → U) → U, ∀ c : Circuit σ n 1, c.Computes I (single f) → s < c.size := by
  obtain ⟨f, _, hf⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (s := computableFunctions I n s) (t := Set.univ) (by simpa [Nat.card_fun] using h)
  exact ⟨f, fun c hc => lt_of_not_ge fun hs => hf ⟨c, hc, hs⟩⟩

/-- A finite Shannon criterion for the full basis, valid simultaneously for every arity,
input count, and gate budget. The factorial correction accounts for gate relabelings. -/
theorem exists_hard_full_function [Finite U] (k n s : ℕ)
    (h : (s + 1) * fullBasisLineBound (card U) k n s ^ s * (n + s) <
        card U ^ (card U ^ n) * s.factorial) :
    ∃ f : (Fin n → U) → U, ∀ c : Circuit (fullSignature k U) n 1,
      c.Computes fullInterpretation (single f) → s < c.size := by
  apply exists_hard_function_of_card_lt
  exact (Nat.mul_lt_mul_right (Nat.factorial_pos s)).mp
    ((card_computableFunctions_full_mul_factorial_le (U := U) k n s).trans_lt h)

/-- The logarithm of the circuit count is at most `(k - 1) * s * log s + O(s)` for
any fixed finite basis of arity at most `k`. The factorial correction saves one factor
of `s` per gate compared with counting labeled programs. -/
theorem exists_card_le_exp [Finite σ.Op] (I : Interpretation σ U)
    {k : ℕ} (hk : 2 ≤ k) (arity_le : ∀ op, σ.Arity op ≤ k) :
    ∃ C : ℝ, ∀ n s : ℕ, n + 1 ≤ s →
      ((computableFunctions I n s).ncard : ℝ) ≤
        Real.exp ((k - 1 : ℝ) * s * Real.log s + C * s) := by
  let q := card σ.Op + 1
  have hq : 1 ≤ q := Nat.succ_le_succ (Nat.zero_le _)
  refine ⟨Real.log (2 ^ k * (q : ℝ)) + 5, fun n s hn => ?_⟩
  let a := (computableFunctions I n s).ncard
  by_cases ha : a = 0
  · simp only [show (computableFunctions I n s).ncard = 0 from ha, Nat.cast_zero]
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
  have hlines (g : ℕ) (hg : g ≤ s) : card (Line σ n g) ≤ q * (n + s + 1) ^ k :=
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

private theorem eventually_add_one_le_pow_div [Finite U] [Nontrivial U] {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ n : ℕ in atTop, n + 1 ≤ card U ^ n / ((k - 1) * n) := by
  filter_upwards [Nat.eventually_mul_pow_le_pow (2 * (k - 1)) 2 (Finite.one_lt_card (α := U)),
    eventually_ge_atTop 1] with n hn hn0
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos (by lia) (by lia))).mpr
  nlinarith only [hn, Nat.mul_le_mul_left ((k - 1) * n) hn0]

private theorem eventually_card_le_exp_neg [Finite σ.Op] [Finite U] [Nontrivial U]
    (I : Interpretation σ U) {k : ℕ} (hk : 2 ≤ k) (arity_le : ∀ op, σ.Arity op ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      ((computableFunctions I n (card U ^ n / ((k - 1) * n))).ncard : ℝ) ≤
        Real.exp (-((card U ^ n / ((k - 1) * n) : ℕ) : ℝ)) *
          (card U : ℝ) ^ (card U ^ n) := by
  let q := card U
  have hq : 1 < q := Finite.one_lt_card
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by lia : 1 ≤ k), Nat.cast_one]
  have hkR : (0 : ℝ) < (k : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by lia : 1 < k))
  obtain ⟨C, hC⟩ := exists_card_le_exp I hk arity_le
  obtain ⟨t, ht⟩ := exists_nat_gt ((C + 1) / ((k - 1 : ℝ) * Real.log q))
  have hgap : C + 1 < (k - 1 : ℝ) * t * Real.log q := by
    have := (div_lt_iff₀ (mul_pos hkR hlogq)).mp ht
    nlinarith only [this]
  filter_upwards [eventually_add_one_le_pow_div (U := U) hk, eventually_ge_atTop t,
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
  have hexponent : (k - 1 : ℝ) * s * Real.log s + C * s ≤
      -(s : ℝ) + (q : ℝ) ^ n * Real.log q := by
    nlinarith only [mul_le_mul_of_nonneg_left hlog (mul_nonneg hkR.le hs.le),
      mul_le_mul_of_nonneg_right hsize hlogq.le, mul_lt_mul_of_pos_right hgap hs]
  calc
    _ ≤ Real.exp ((k - 1 : ℝ) * s * Real.log s + C * s) := hC n s hn
    _ ≤ Real.exp (-(s : ℝ) + (q : ℝ) ^ n * Real.log q) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp (-(s : ℝ)) * (q : ℝ) ^ (q ^ n : ℕ) := by
      rw [Real.exp_add, show (q : ℝ) ^ n = ((q ^ n : ℕ) : ℝ) by norm_cast,
        Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hqR)]

/-- Almost all functions on `n` inputs require more than `|U|ⁿ / ((k - 1) * n)` gates over a
fixed finite signature whose operations have arity at most `k ≥ 2`: the fraction of functions
computable within that budget tends to zero. -/
theorem tendsto_card_computableFunctions_div_of_arity_le [Finite σ.Op] [Finite U] [Nontrivial U]
    (I : Interpretation σ U) {k : ℕ} (hk : 2 ≤ k) (arity_le : ∀ op, σ.Arity op ≤ k) :
    Tendsto (fun n : ℕ =>
      ((computableFunctions I n (card U ^ n / ((k - 1) * n))).ncard : ℝ) /
        (card U : ℝ) ^ (card U ^ n)) atTop (𝓝 0) := by
  have hq : (0 : ℝ) < card U := by exact_mod_cast Nat.card_pos
  have hbudget : Tendsto (fun n : ℕ => card U ^ n / ((k - 1) * n)) atTop atTop :=
    tendsto_atTop_mono' atTop (eventually_add_one_le_pow_div (U := U) hk)
      (tendsto_add_atTop_nat 1)
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.comp hbudget))
  filter_upwards [eventually_card_le_exp_neg I hk arity_le] with n hn
  exact (div_le_iff₀ (by positivity)).mpr hn

/-- Almost all functions on `n` inputs require more than `|U|ⁿ/n` gates over a fixed finite
signature whose operations have arity at most two: the fraction of functions computable within
that budget tends to zero. -/
theorem tendsto_card_computableFunctions_div [Finite σ.Op] [Finite U] [Nontrivial U]
    (I : Interpretation σ U) (arity_le : ∀ op, σ.Arity op ≤ 2) :
    Tendsto (fun n : ℕ => ((computableFunctions I n (card U ^ n / n)).ncard : ℝ) /
      (card U : ℝ) ^ (card U ^ n)) atTop (𝓝 0) := by
  simpa using tendsto_card_computableFunctions_div_of_arity_le I le_rfl arity_le

/-- For any fixed basis of arity at most `k ≥ 2`, which may have infinitely many operations,
sufficiently large input counts admit a scalar function requiring more than
`|U|ⁿ / ((k - 1) * n)` gates. The function is hard for the full basis of arity `k`, which
simulates the signature gate by gate. -/
theorem exists_hard_function_of_arity_le [Finite U] [Nontrivial U]
    (I : Interpretation σ U) {k : ℕ} (hk : 2 ≤ k) (arity_le : ∀ op, σ.Arity op ≤ k) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ f : (Fin n → U) → U,
      ∀ c : Circuit σ n 1,
        c.Computes I (single f) → (card U : ℝ) ^ n / ((k - 1 : ℝ) * n) < (c.size : ℝ) := by
  have hfull : ∀ op, (fullSignature k U).Arity op ≤ k := by
    rintro (_ | _) <;> simp [fullSignature]
  have hq : (0 : ℝ) < card U := by exact_mod_cast Nat.card_pos
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by lia : 1 ≤ k), Nat.cast_one]
  apply eventually_atTop.mp
  filter_upwards [(tendsto_card_computableFunctions_div_of_arity_le fullInterpretation hk
    hfull).eventually (gt_mem_nhds one_pos), eventually_ge_atTop 1] with n hn hn0
  rw [div_lt_one (pow_pos hq _)] at hn
  obtain ⟨f, hf⟩ := exists_hard_function_of_card_lt (fullInterpretation (k := k) (Carrier := U))
    n (card U ^ n / ((k - 1) * n)) (by exact_mod_cast hn)
  refine ⟨f, fun c hc => ?_⟩
  obtain ⟨d, hd, hsize⟩ := c.exists_simulation_le (fullInterpretation_simulatesWithCost I arity_le)
  have hg : card U ^ n / ((k - 1) * n) < c.size :=
    (hf d fun x => (congrFun hd x).trans (hc x)).trans_le (hsize.trans (by simp))
  have hden : 0 < (k - 1) * n := Nat.mul_pos (by lia) (by lia)
  rw [← hkcast]
  apply (div_lt_iff₀ (by exact_mod_cast hden : (0 : ℝ) < (k - 1 : ℕ) * n)).mpr
  exact_mod_cast (Nat.div_lt_iff_lt_mul hden).mp hg

/-- For all sufficiently large `n`, some function on `n` inputs over `U` requires more than
`|U|ⁿ/n` gates over a signature whose operations have arity at most two, which may have
infinitely many operations. -/
theorem exists_hard_function [Finite U] [Nontrivial U]
    (I : Interpretation σ U) (arity_le : ∀ op, σ.Arity op ≤ 2) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ f : (Fin n → U) → U,
      ∀ c : Circuit σ n 1,
        c.Computes I (single f) → (card U : ℝ) ^ n / n < (c.size : ℝ) := by
  have := exists_hard_function_of_arity_le I le_rfl arity_le
  norm_num at this
  exact this

end Cslib.Circuits.Shannon
