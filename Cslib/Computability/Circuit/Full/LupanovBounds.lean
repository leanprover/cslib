/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Full.LupanovConstruction
public import Mathlib.Data.Nat.Log

import Mathlib.Tactic.Linarith

/-!
# Estimates for the finite Lupanov budget

`mul_bound_le` separates the leading table-assembly term from the decoder, dictionary,
and rounding costs after multiplying the budget by `k - 1`.

For one output, `bound_le` chooses `d = 3 * Nat.log q n` data coordinates and blocks of
`t = n - 5 * Nat.log q n` cells. The leading term is then `⌈q^d / t⌉ * q^(n-d)`, while
the remaining costs are bounded by a polynomial in `n` and a multiple of `n * q^(n-d)`.
For fixed `q ≥ 2` and `k ≥ 2`, both errors are negligible relative to `q^n / n`.
These estimates prepare the sharp asymptotic Lupanov upper bound.
-/

public section

namespace Cslib.Circuits.Full.Lupanov

private theorem sum_powers_le {q : ℕ} (hq : 2 ≤ q) (r : ℕ) :
    (∑ j ∈ Finset.range r, q ^ (j + 1)) ≤ 2 * q ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [Nat.mul_le_mul_right (q ^ r) hq]

private theorem ceilDiv_mul_le (a b : ℕ) : (a ⌈/⌉ b) * b ≤ a + b := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  exact (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)

/-- After scaling by `k - 1`, the leading cost is one unit per section, block, and output.
The remaining terms bound the decoders, dictionaries, and rounding in the selectors. -/
theorem mul_bound_le {q : ℕ} (hq : 2 ≤ q) (k r d t m : ℕ) :
    (k - 1) * bound q k r d t m ≤
      m * q ^ r * (q ^ d ⌈/⌉ t) + (2 * (k - 1) + m * (2 * (k - 1) + 1)) * q ^ r +
        2 * (k - 1) * q ^ d + 2 * (k - 1) * (q ^ d ⌈/⌉ t) * q ^ t + m * (k - 1) := by
  have hl := Nat.mul_le_mul_left (k - 1) (sum_powers_le hq r)
  have hr := Nat.mul_le_mul_left (k - 1) (sum_powers_le hq d)
  have hb := Nat.mul_le_mul_left ((k - 1) * (q ^ d ⌈/⌉ t)) (sum_powers_le hq t)
  have hs := Nat.mul_le_mul_left (m * q ^ r) (ceilDiv_mul_le ((q ^ d ⌈/⌉ t) - 1) (k - 1))
  have ho := Nat.mul_le_mul_left m (ceilDiv_mul_le (q ^ r - 1) (k - 1))
  have hB := Nat.sub_le (q ^ d ⌈/⌉ t) 1
  have hA := Nat.sub_le (q ^ r) 1
  dsimp [bound]
  nlinarith only [hl, hr, hb, hs, ho,
    Nat.mul_le_mul_left (m * q ^ r) hB, Nat.mul_le_mul_left m hA]

/-- For one output, use `3 * Nat.log q n` data coordinates and blocks of
`n - 5 * Nat.log q n` cells. The first term bounds table assembly; the other two bound
all remaining gates, including the two constants. -/
theorem bound_le {q k : ℕ} (hq : 2 ≤ q) (hk : 2 ≤ k) (n : ℕ)
    (hn : 5 * Nat.log q n < n) :
    (k - 1) * (2 + bound q k (n - 3 * Nat.log q n) (3 * Nat.log q n)
      (n - 5 * Nat.log q n) 1) ≤
      (q ^ (3 * Nat.log q n) ⌈/⌉ (n - 5 * Nat.log q n)) * q ^ (n - 3 * Nat.log q n) +
        2 * (k - 1) * n ^ 3 + 10 * (k - 1) * n * q ^ (n - 3 * Nat.log q n) := by
  let l := Nat.log q n
  let d := 3 * l
  let r := n - d
  let t := n - 5 * l
  let B := q ^ d ⌈/⌉ t
  have hn0 : 0 < n := by lia
  have hl : q ^ l ≤ n := Nat.pow_log_le_self q (by lia)
  have hd : q ^ d ≤ n ^ 3 := by
    simpa [d, pow_mul, Nat.mul_comm] using Nat.pow_le_pow_left hl 3
  have ht : 0 < t := by dsimp [t, l]; lia
  have hblocks : B ≤ q ^ d :=
    (ceilDiv_le_iff_le_mul ht).mpr (by simpa using Nat.mul_le_mul_right (q ^ d) ht)
  have hshift : q ^ d * q ^ t = q ^ l * q ^ r := by
    rw [← pow_add, ← pow_add]
    congr 1
    dsimp [d, t, r, l]
    lia
  have hbank : B * q ^ t ≤ n * q ^ r := by
    calc
      B * q ^ t ≤ q ^ d * q ^ t := Nat.mul_le_mul_right _ hblocks
      _ = q ^ l * q ^ r := hshift
      _ ≤ n * q ^ r := Nat.mul_le_mul_right _ hl
  have hrow : q ^ r ≤ n * q ^ r := by
    simpa using Nat.mul_le_mul_right (q ^ r) hn0
  have hone : 1 ≤ n * q ^ r := Nat.mul_pos hn0 (pow_pos (by lia) _)
  have hother : (4 * (k - 1) + 1) * q ^ r + 3 * (k - 1) ≤
      8 * (k - 1) * n * q ^ r := by
    have hh : 4 * (k - 1) + 1 ≤ 5 * (k - 1) := by lia
    nlinarith only [Nat.mul_le_mul_right (q ^ r) hh,
      Nat.mul_le_mul_left (5 * (k - 1)) hrow, Nat.mul_le_mul_left (3 * (k - 1)) hone]
  have h := mul_bound_le hq k r d t 1
  change (k - 1) * (2 + bound q k r d t 1) ≤
    B * q ^ r + 2 * (k - 1) * n ^ 3 + 10 * (k - 1) * n * q ^ r
  nlinarith only [h, hother, Nat.mul_le_mul_left (2 * (k - 1)) hbank,
    Nat.mul_le_mul_left (2 * (k - 1)) hd]

end Cslib.Circuits.Full.Lupanov
