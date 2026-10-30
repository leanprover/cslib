/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Full.LupanovBounds
public import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith

/-!
# The sharp Lupanov upper bound for a fixed full basis

For a fixed finite nontrivial carrier of size `q`, fixed gate arity `k ≥ 2`, and `ε > 0`,
every scalar function on `n` inputs has a circuit of size at most
`(1 + ε) * q ^ n / ((k - 1) * n)` for all sufficiently large `n`.
The threshold is uniform in the function. Constants count as gates.

The finite construction is in `LupanovConstruction`; `LupanovBounds` controls its
overhead after choosing logarithmic data coordinates and nearly `n` cells per block.
Together with `Shannon.exists_hard_function_of_arity_le`, this gives the sharp leading
constant `1 / (k - 1)` for the worst-case scalar complexity over the full basis.

## References

* [O. B. Lupanov, *On a Method of Circuit Synthesis*][Lupanov1958]: shared-table synthesis.
-/

public section

namespace Cslib.Circuits.Full.Lupanov

open Filter

variable {U : Type*} [Finite U] [Nontrivial U]

private theorem exists_circuit_of_split {n k r d t : ℕ} (hk : 2 ≤ k)
    (hsplit : r + d = n) (ht : 0 < t) (f : (Fin n → U) → U) :
    ∃ c : Circuit (fullSignature k U) n 1,
      c.Computes fullInterpretation (single f) ∧
        c.size ≤ 2 + bound (Nat.card U) k r d t 1 := by
  subst n
  exact exists_circuit hk ht (single f)

/-- For fixed carrier, gate arity, and `ε > 0`, every scalar function on sufficiently many
inputs has a circuit with at most `(1 + ε) * |U|^n / ((k - 1) * n)` gates, including
constant gates. The input threshold is uniform in the function. -/
theorem exists_circuit_asymptotic {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f : (Fin n → U) → U,
      ∃ c : Circuit (fullSignature k U) n 1,
        c.Computes fullInterpretation (single f) ∧
          (c.size : ℝ) ≤ (1 + ε) * (Nat.card U : ℝ) ^ n / ((k - 1 : ℝ) * n) := by
  let q := Nat.card U
  have hq : 2 ≤ q := Finite.one_lt_card
  apply eventually_atTop.mp
  obtain ⟨P, hP⟩ := exists_nat_gt (1 / ε)
  have hP0 : (0 : ℝ) < P := lt_trans (by positivity) hP
  have hcoefficient : (P : ℝ) + 1 ≤ (1 + ε) * P := by
    have := (div_lt_iff₀ hε).mp hP
    nlinarith
  filter_upwards [eventually_bound_le hq hk P, Nat.eventually_mul_log_le 6 (by lia : 1 < q),
    eventually_ge_atTop q] with n hb hl hn
  intro f
  have hlog : 1 ≤ Nat.log q n := Nat.le_log_of_pow_le (by lia) (by simpa using hn)
  have hsplit : (n - 3 * Nat.log q n) + 3 * Nat.log q n = n := by lia
  obtain ⟨c, hc, hg⟩ := exists_circuit_of_split hk hsplit (by lia : 0 < n - 5 * Nat.log q n) f
  refine ⟨c, hc, ?_⟩
  have hcost : (P : ℝ) * n * (k - 1 : ℝ) * c.size ≤ (P + 1 : ℝ) * (q : ℝ) ^ n := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by lia : 1 ≤ k)]
    exact_mod_cast (Nat.mul_le_mul_left (P * n * (k - 1)) hg).trans hb
  have hkR : (0 : ℝ) < (k : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by lia : 1 < k))
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by lia : 0 < n)
  apply (le_div_iff₀ (mul_pos hkR hnR)).mpr
  apply (mul_le_mul_iff_right₀ hP0).mp
  nlinarith [mul_le_mul_of_nonneg_right hcoefficient
    (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ n)]

end Cslib.Circuits.Full.Lupanov
