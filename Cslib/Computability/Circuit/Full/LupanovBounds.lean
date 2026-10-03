/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Full.LupanovConstruction
public import Cslib.Foundations.Data.Nat.Asymptotics

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Estimates for the finite Lupanov budget

`mul_bound_le` separates the leading table-assembly term from the decoder, dictionary,
and rounding costs after multiplying the budget by `k - 1`.

For one output, `bound_le` chooses `d = 3 * Nat.log q n` data coordinates and blocks of
`t = n - 5 * Nat.log q n` cells. The leading term is then `⌈q^d / t⌉ * q^(n-d)`, while
the remaining costs are bounded by a polynomial in `n` and a multiple of `n * q^(n-d)`.
For fixed `q ≥ 2` and `k ≥ 2`, both errors are negligible relative to `q^n / n`.
`eventually_bound_le` absorbs these errors: for every natural `P`, the complete budget
`B(n)` satisfies `P * n * (k - 1) * B(n) ≤ (P + 1) * q^n` for all sufficiently large `n`.
For positive `P`, this gives a factor `1 + 1 / P` above `q^n / ((k - 1) * n)`.
-/

public section

namespace Cslib.Circuits.Full.Lupanov

open Filter

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

private theorem main_term_le (P q n : ℕ)
    (hn : 5 * Nat.log q n < n) (hP : (P + 1) * (5 * Nat.log q n) ≤ n) :
    P * n * ((q ^ (3 * Nat.log q n) ⌈/⌉ (n - 5 * Nat.log q n)) *
      q ^ (n - 3 * Nat.log q n)) ≤ (P + 1) * q ^ n +
        (P + 1) * n * q ^ (n - 3 * Nat.log q n) := by
  let d := 3 * Nat.log q n
  let r := n - d
  let t := n - 5 * Nat.log q n
  have hsplit : d + r = n := by dsimp [d, r]; lia
  have hPt : P * n ≤ (P + 1) * t := by
    dsimp [t]
    nlinarith [Nat.sub_add_cancel hn.le]
  calc
    P * n * ((q ^ d ⌈/⌉ t) * q ^ r) ≤
        (P + 1) * t * ((q ^ d ⌈/⌉ t) * q ^ r) := by gcongr
    _ = (P + 1) * ((q ^ d ⌈/⌉ t) * t) * q ^ r := by ring
    _ ≤ (P + 1) * (q ^ d + t) * q ^ r := by gcongr; exact ceilDiv_mul_le _ _
    _ = (P + 1) * q ^ n + (P + 1) * t * q ^ r := by
      rw [show q ^ n = q ^ d * q ^ r by rw [← pow_add, hsplit]]
      ring
    _ ≤ (P + 1) * q ^ n + (P + 1) * n * q ^ r := by gcongr; exact Nat.sub_le _ _

private theorem overhead_le {q : ℕ} (hq : 2 ≤ q) (c n : ℕ)
    (hc : c * q ^ 3 ≤ n) (hn : 3 * Nat.log q n ≤ n) :
    c * n ^ 2 * q ^ (n - 3 * Nat.log q n) ≤ q ^ n := by
  let b := q ^ Nat.log q n
  have hb : n < q * b := by
    simpa [b, pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by lia : 1 < q) n
  have hcb : c * q ^ 2 ≤ b := by
    apply Nat.le_of_mul_le_mul_left (c := q) _ (by lia)
    nlinarith only [hc, hb]
  have hpoly : c * n ^ 2 ≤ b ^ 3 := by
    calc
      c * n ^ 2 ≤ c * (q * b) ^ 2 := by gcongr
      _ = (c * q ^ 2) * b ^ 2 := by ring
      _ ≤ b * b ^ 2 := by gcongr
      _ = b ^ 3 := by ring
  calc
    c * n ^ 2 * q ^ (n - 3 * Nat.log q n) ≤ b ^ 3 * q ^ (n - 3 * Nat.log q n) := by
      gcongr
    _ = q ^ n := by
      dsimp [b]
      rw [← pow_mul, ← pow_add]
      congr 1
      lia

/-- For fixed carrier size and gate arity, the budget for one output, including constant
gates, is eventually within a factor `1 + 1 / P` of `q^n / ((k - 1) * n)` when `P > 0`.
The scaled statement stays in natural numbers and also holds trivially at `P = 0`. -/
theorem eventually_bound_le {q k : ℕ} (hq : 2 ≤ q) (hk : 2 ≤ k) (P : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      P * n * (k - 1) * (2 + bound q k (n - 3 * Nat.log q n) (3 * Nat.log q n)
        (n - 5 * Nat.log q n) 1) ≤ (P + 1) * q ^ n := by
  -- Use precision `3 * P` to allocate equal allowances to the three error terms.
  let Q := 3 * P
  let c := 10 * Q * (k - 1) + Q + 1
  filter_upwards [Nat.eventually_mul_log_le (5 * (Q + 1) + 1) (by lia : 1 < q),
    Nat.eventually_mul_pow_le_pow (2 * Q * (k - 1)) 4 (by lia : 1 < q),
    eventually_ge_atTop (max q (c * q ^ 3))] with n hlog hpoly hn
  have hnq : q ≤ n := (le_max_left _ _).trans hn
  have hl : 1 ≤ Nat.log q n := Nat.le_log_of_pow_le (by lia) (by simpa using hnq)
  have hstrict : 5 * Nat.log q n < n := by nlinarith
  have hremoved : (Q + 1) * (5 * Nat.log q n) ≤ n := by nlinarith
  have hmain := main_term_le Q q n hstrict hremoved
  have herr := overhead_le hq c n ((le_max_right _ _).trans hn) (by lia)
  have hbound := Nat.mul_le_mul_left (Q * n) (bound_le hq hk n hstrict)
  have hmerge : (Q + 1) * n * q ^ (n - 3 * Nat.log q n) ≤
      (Q + 1) * n ^ 2 * q ^ (n - 3 * Nat.log q n) := by
    gcongr
    simpa [pow_two] using Nat.le_mul_self n
  have htotal : Q * n * (k - 1) *
      (2 + bound q k (n - 3 * Nat.log q n) (3 * Nat.log q n)
        (n - 5 * Nat.log q n) 1) ≤ (Q + 3) * q ^ n := by
    dsimp [c] at herr
    nlinarith only [hmain, herr, hpoly, hbound, hmerge]
  dsimp [Q] at htotal
  nlinarith only [htotal]

end Cslib.Circuits.Full.Lupanov
