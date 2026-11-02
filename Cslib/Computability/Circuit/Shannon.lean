/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Counting
public import Mathlib.Basic.Real.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Cslib.Computability.Circuit.Full
import Cslib.Foundations.Data.Nat.Asymptotics
import Cslib.Foundations.Data.Nat.Factorial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Shannon's lower bound for finite carriers and binary bases

For any fixed finite signature with operation arities at most two, interpreted on a finite
carrier `U` with `q ≥ 2` elements, almost all functions on `n` inputs require more than `qⁿ/n`
gates: the fraction of functions computable within that budget tends to zero. Hence, for all
sufficiently large `n`, some function requires more than `qⁿ/n` gates. This also holds when the
signature has infinitely many operations, because the binary full basis simulates every
signature of arity at most two gate by gate, so its hard functions are hard for all of them.
For the De Morgan basis on `Bool`, this matches Lupanov's upper bound asymptotically.

The logarithm of the counting bound is at most `s log s + O(s)` for `n + 1 ≤ s`.
At `s = ⌊qⁿ/n⌋`, this is smaller than the logarithm of the `q^(qⁿ)` functions by at least `s`.
This extends the Boolean counting argument in the references to finite carriers.

## References

* [Claude E. Shannon, *The Synthesis of Two-Terminal Switching Circuits*][Shannon1949]:
  Theorem 7, Section 3(e), pp. 77-79, the original counting argument for switching circuits.
* [Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]:
  Lemma 1.12 and Theorem 1.14, a modern treatment of Boolean circuit counting.
-/

public section

namespace Cslib.Circuits.Shannon

open Filter Topology

universe v u
variable {σ : Signature.{v}} {U : Type u}

private theorem exists_card_le_exp [Finite σ.Op] (I : Interpretation σ U)
    (arity_le : ∀ op, σ.Arity op ≤ 2) :
    ∃ C : ℝ, ∀ n s : ℕ, n + 1 ≤ s →
      ((computableFunctions I n s).card : ℝ) ≤ Real.exp ((s : ℝ) * Real.log s + C * s) := by
  let q := Nat.card σ.Op + 1
  have hq : 1 ≤ q := Nat.succ_le_succ (Nat.zero_le _)
  refine ⟨Real.log (4 * (q : ℝ)) + 5, fun n s hn => ?_⟩
  let a := (computableFunctions I n s).card
  by_cases ha : a = 0
  · simp only [show (computableFunctions I n s).card = 0 from ha, Nat.cast_zero]
    positivity
  have ha : (0 : ℝ) < a := by exact_mod_cast (Nat.pos_of_ne_zero ha)
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  have hn' : (n : ℝ) + 1 ≤ s := by exact_mod_cast hn
  have hB : s ≤ q * (n + s + 1) ^ 2 := by
    calc
      s ≤ (n + s + 1) ^ 2 := by nlinarith [Nat.le_mul_self (n + s + 1)]
      _ ≤ q * (n + s + 1) ^ 2 := by
        simpa only [one_mul] using Nat.mul_le_mul_right ((n + s + 1) ^ 2) hq
  have hlines (g : ℕ) (hg : g ≤ s) : Nat.card (Line σ n g) ≤ q * (n + s + 1) ^ 2 :=
    (Line.card_le n g 2 arity_le).trans (Nat.mul_le_mul (Nat.le_succ _)
      (Nat.pow_le_pow_left (by omega : n + g + 1 ≤ n + s + 1) 2))
  have hcount : (a : ℝ) * s.factorial ≤
      (2 * (s : ℝ)) ^ 2 * (4 * (q : ℝ) * (s : ℝ) ^ 2) ^ s := by
    calc
      (a : ℝ) * s.factorial ≤
          ((s : ℝ) + 1) * ((q : ℝ) * ((n : ℝ) + s + 1) ^ 2) ^ s * (n + s) := by
        exact_mod_cast card_computableFunctions_mul_factorial_le I n s _ hB hlines
      _ ≤ (2 * s) * ((q : ℝ) * (2 * (s : ℝ)) ^ 2) ^ s * (2 * s) := by
        gcongr <;> linarith
      _ = _ := by rw [show (q : ℝ) * (2 * (s : ℝ)) ^ 2 = 4 * q * s ^ 2 by ring]; ring
  have hlog : Real.log a + Real.log s.factorial ≤
      2 * (Real.log 2 + Real.log s) + s * (Real.log (4 * (q : ℝ)) + 2 * Real.log s) := by
    simpa [Real.log_mul, Real.log_pow, ne_of_gt ha, Nat.factorial_ne_zero,
      ne_of_gt (zero_lt_one.trans_le hs)] using
      (Real.log_le_log (by positivity : 0 < (a : ℝ) * s.factorial) hcount)
  apply (Real.log_le_iff_le_exp ha).mp
  have hfactorial := Nat.mul_log_sub_le_log_factorial s
  have hlogtwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlogs := Real.log_le_self (by positivity : (0 : ℝ) ≤ s)
  nlinarith

private theorem eventually_card_le_exp_neg [Finite σ.Op] [Fintype U] [Nontrivial U]
    (I : Interpretation σ U) (arity_le : ∀ op, σ.Arity op ≤ 2) :
    ∀ᶠ n : ℕ in atTop, ((computableFunctions I n (Fintype.card U ^ n / n)).card : ℝ) ≤
      Real.exp (-((Fintype.card U ^ n / n : ℕ) : ℝ)) *
        (Fintype.card U : ℝ) ^ (Fintype.card U ^ n) := by
  let q := Fintype.card U
  have hq : 1 < q := Fintype.one_lt_card
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  obtain ⟨C, hC⟩ := exists_card_le_exp I arity_le
  obtain ⟨t, ht⟩ := exists_nat_gt ((C + 1) / Real.log q)
  have hgap : C + 1 < t * Real.log q := (div_lt_iff₀ hlogq).mp ht
  filter_upwards [Nat.eventually_add_one_le_pow_div hq, eventually_ge_atTop t,
    eventually_ge_atTop (q ^ t)] with n hn htn hlarge
  let s := q ^ n / n
  have hs : (0 : ℝ) < s := by exact_mod_cast (by dsimp [s]; omega : 0 < s)
  have hshift : s ≤ q ^ (n - t) := by
    apply Nat.div_le_of_le_mul
    calc
      q ^ n = q ^ t * q ^ (n - t) := by rw [← pow_add, Nat.add_sub_of_le htn]
      _ ≤ n * q ^ (n - t) := Nat.mul_le_mul_right _ hlarge
  have hlog : Real.log s ≤ ((n : ℝ) - t) * Real.log q := by
    have h := Real.log_le_log hs (show (s : ℝ) ≤ (q : ℝ) ^ (n - t) by exact_mod_cast hshift)
    simpa [Real.log_pow, Nat.cast_sub htn] using h
  have hsize : (n : ℝ) * s ≤ (q : ℝ) ^ n := by
    exact_mod_cast (Nat.mul_div_le (q ^ n) n)
  have hexponent : (s : ℝ) * Real.log s + C * s ≤ -(s : ℝ) + (q : ℝ) ^ n * Real.log q := by
    nlinarith only [mul_le_mul_of_nonneg_left hlog hs.le,
      mul_le_mul_of_nonneg_right hsize hlogq.le, mul_lt_mul_of_pos_right hgap hs]
  calc
    _ ≤ Real.exp ((s : ℝ) * Real.log s + C * s) := hC n s hn
    _ ≤ Real.exp (-(s : ℝ) + (q : ℝ) ^ n * Real.log q) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp (-(s : ℝ)) * (q : ℝ) ^ (q ^ n : ℕ) := by
      rw [Real.exp_add, show (q : ℝ) ^ n = ((q ^ n : ℕ) : ℝ) by norm_cast,
        Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hqR)]

/-- Almost all functions on `n` inputs require more than `|U|ⁿ/n` gates over a fixed finite
signature whose operations have arity at most two: the fraction of functions computable within
that budget tends to zero. -/
theorem tendsto_card_computableFunctions_div [Finite σ.Op] [Finite U] [Nontrivial U]
    (I : Interpretation σ U) (arity_le : ∀ op, σ.Arity op ≤ 2) :
    Tendsto (fun n : ℕ => ((computableFunctions I n (Nat.card U ^ n / n)).card : ℝ) /
      (Nat.card U : ℝ) ^ (Nat.card U ^ n)) atTop (𝓝 0) := by
  let := Fintype.ofFinite U
  simp only [Nat.card_eq_fintype_card]
  have hq : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hbudget : Tendsto (fun n : ℕ => Fintype.card U ^ n / n) atTop atTop :=
    tendsto_atTop_mono' atTop (Nat.eventually_add_one_le_pow_div Fintype.one_lt_card)
      (tendsto_add_atTop_nat 1)
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.comp hbudget))
  filter_upwards [eventually_card_le_exp_neg I arity_le] with n hn
  exact (div_le_iff₀ (by positivity)).mpr hn

/-- For all sufficiently large `n`, some function on `n` inputs over `U` requires more than
`|U|ⁿ/n` gates over a signature whose operations have arity at most two, which may have
infinitely many operations. The function is hard for the binary full basis, which simulates
the signature gate by gate. -/
theorem exists_hard_function [Finite U] [Nontrivial U]
    (I : Interpretation σ U) (arity_le : ∀ op, σ.Arity op ≤ 2) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ f : (Fin n → U) → U,
      ∀ c : Circuit σ n 1,
        c.Computes I (single f) → (Nat.card U : ℝ) ^ n / n < (c.size : ℝ) := by
  classical
  let := Fintype.ofFinite U
  have hfull : ∀ op, (fullSignature 2 U).Arity op ≤ 2 := by
    rintro (_ | _) <;> simp [fullSignature]
  have hq : (0 : ℝ) < Nat.card U := by exact_mod_cast Nat.card_pos
  apply eventually_atTop.mp
  filter_upwards [(tendsto_card_computableFunctions_div fullInterpretation hfull).eventually
    (gt_mem_nhds one_pos), eventually_ge_atTop 1] with n hn hn0
  rw [div_lt_one (pow_pos hq _)] at hn
  have hcard : (computableFunctions (fullInterpretation (k := 2) (Carrier := U)) n
      (Nat.card U ^ n / n)).card < Nat.card U ^ Nat.card U ^ n := by exact_mod_cast hn
  have huniv : (Finset.univ : Finset ((Fin n → U) → U)).card = Nat.card U ^ Nat.card U ^ n := by
    simp [Nat.card_eq_fintype_card]
  obtain ⟨f, _, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card (hcard.trans_eq huniv.symm)
  refine ⟨f, fun c hc => ?_⟩
  obtain ⟨d, hd, hsize⟩ := c.exists_simulation_le (fullInterpretation_simulatesWithCost I arity_le)
  have hg : Nat.card U ^ n / n < c.size := lt_of_not_ge fun hg =>
    hf (mem_computableFunctions.mpr
      ⟨d, fun x => (congrFun hd x).trans (hc x), hsize.trans (by simpa using hg)⟩)
  apply (div_lt_iff₀ (by exact_mod_cast (by omega : 0 < n) : (0 : ℝ) < n)).mpr
  exact_mod_cast (Nat.div_lt_iff_lt_mul (by omega : 0 < n)).mp hg

end Cslib.Circuits.Shannon
