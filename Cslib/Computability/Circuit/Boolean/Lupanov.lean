/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.LupanovConstruction
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log

/-!
# Lupanov's asymptotically optimal upper bound

Every Boolean function on `n` inputs has a De Morgan circuit with at most
`(1 + ε) * 2 ^ n / n` gates for all sufficiently large `n`, given any `ε > 0`.
The threshold is uniform in the function; size counts constants and negations.

We apply the finite construction with `3 log₂ n` address bits and blocks of `n - 5 log₂ n`
rows. The number of blocks times `2 ^ (n - 3 log₂ n)` gives the leading term `2 ^ n / n`;
minterms and pattern banks contribute lower-order terms.

## References

* [O. B. Lupanov, *On a Method of Circuit Synthesis*][Lupanov1958],
  Theorem 4 and Section 6, pp. 131-135: the upper bound for general weighted bases,
  specialized here to the De Morgan basis.
* [Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012],
  Theorem 1.15: a modern exposition.
-/

public section

namespace Cslib.Circuits.Boolean.Lupanov

open Filter

private theorem polynomial_le_pow (c r : ℕ) :
    ∀ᶠ n : ℕ in atTop, c * n ^ r ≤ 2 ^ n := by
  have h := Asymptotics.isLittleO_iff_nat_mul_le.mp
    (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) r (by norm_num : (1 : ℝ) < 2)) c
  filter_upwards [h] with n hn
  exact_mod_cast (by simpa using hn : (c : ℝ) * n ^ r ≤ (2 : ℝ) ^ n)

private theorem log_le (c : ℕ) : ∀ᶠ n : ℕ in atTop, c * Nat.log 2 n ≤ n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (polynomial_le_pow c 1)
  filter_upwards [eventually_ge_atTop (2 ^ N)] with n hn
  have hn0 : n ≠ 0 := ne_of_gt ((pow_pos (by omega) N).trans_le hn)
  have hh : c * Nat.log 2 n ≤ 2 ^ Nat.log 2 n := by
    simpa using hN (Nat.log 2 n) (Nat.le_log_of_pow_le (by omega) hn)
  exact hh.trans (Nat.pow_log_le_self 2 hn0)

private theorem bound_le (n : ℕ) (hn : 5 * Nat.log 2 n < n) :
    bound (3 * Nat.log 2 n) (n - 3 * Nat.log 2 n) (n - 5 * Nat.log 2 n) ≤
      (2 ^ (3 * Nat.log 2 n) / (n - 5 * Nat.log 2 n) + 1) *
        2 ^ (n - 3 * Nat.log 2 n) + 3 * n ^ 4 +
          16 * n * 2 ^ (n - 3 * Nat.log 2 n) := by
  let l := Nat.log 2 n
  let k := 3 * l
  let d := n - 3 * l
  let s := n - 5 * l
  let B := 2 ^ k / s + 1
  have hn0 : 0 < n := by omega
  have hs : 0 < s := by dsimp [s, l]; omega
  have hkd : k + d = n := by dsimp [k, d, l]; omega
  have hsd : s ≤ d := by dsimp [s, d]; omega
  have hsn : s ≤ n := Nat.sub_le _ _
  have hl : 2 ^ l ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hk : 2 ^ k ≤ n ^ 3 := by
    calc
      2 ^ k = (2 ^ l) ^ 3 := by simp [k, pow_mul, Nat.mul_comm]
      _ ≤ n ^ 3 := Nat.pow_le_pow_left hl _
  have hB : B * s ≤ 2 ^ k + s := by
    dsimp [B]
    nlinarith [Nat.div_mul_le_self (2 ^ k) s]
  have hshift : 2 ^ k * 2 ^ s = 2 ^ l * 2 ^ d := by
    rw [← pow_add, ← pow_add]
    congr 1
    dsimp [k, s, d, l]
    omega
  have hbank : (2 ^ k + s) * 2 ^ s ≤ 2 * n * 2 ^ d := by
    rw [Nat.add_mul, hshift]
    have := Nat.mul_le_mul hsn (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hsd)
    have := Nat.mul_le_mul_right (2 ^ d) hl
    nlinarith
  have hpattern : B * (2 ^ s * (2 * s + 4)) ≤ 12 * n * 2 ^ d := by
    calc
      B * (2 ^ s * (2 * s + 4)) ≤ B * (2 ^ s * (6 * s)) := by gcongr; omega
      _ = 6 * (B * s) * 2 ^ s := by ring
      _ ≤ 6 * (2 ^ k + s) * 2 ^ s := by gcongr
      _ ≤ 6 * (2 * n * 2 ^ d) := by nlinarith [hbank]
      _ = 12 * n * 2 ^ d := by ring
  have hmin : (2 ^ k + 2 ^ d) * (2 * n + 1) ≤ 3 * n ^ 4 + 3 * n * 2 ^ d := by
    calc
      (2 ^ k + 2 ^ d) * (2 * n + 1) ≤ (n ^ 3 + 2 ^ d) * (3 * n) := by gcongr; omega
      _ = 3 * n ^ 4 + 3 * n * 2 ^ d := by ring
  have hone : 1 ≤ n * 2 ^ d := Nat.mul_pos hn0 (pow_pos (by omega) _)
  change bound k d s ≤ B * 2 ^ d + 3 * n ^ 4 + 16 * n * 2 ^ d
  unfold bound
  rw [hkd]
  dsimp [B] at hpattern ⊢
  nlinarith

private theorem mainTerm_le (P n : ℕ)
    (hn : 5 * Nat.log 2 n < n) (hP : (P + 1) * (5 * Nat.log 2 n) ≤ n) :
    P * n * ((2 ^ (3 * Nat.log 2 n) / (n - 5 * Nat.log 2 n) + 1) *
      2 ^ (n - 3 * Nat.log 2 n)) ≤ (P + 1) * 2 ^ n +
        (P + 1) * n * 2 ^ (n - 3 * Nat.log 2 n) := by
  let k := 3 * Nat.log 2 n
  let s := n - 5 * Nat.log 2 n
  let d := n - k
  have hks : k + d = n := by dsimp [k, d]; omega
  have hPs : P * n ≤ (P + 1) * s := by
    dsimp [s]
    have := Nat.sub_add_cancel (by omega : 5 * Nat.log 2 n ≤ n)
    nlinarith
  have hB : (2 ^ k / s + 1) * s ≤ 2 ^ k + s := by
    nlinarith [Nat.div_mul_le_self (2 ^ k) s]
  calc
    P * n * ((2 ^ k / s + 1) * 2 ^ d) ≤
        (P + 1) * s * ((2 ^ k / s + 1) * 2 ^ d) := by gcongr
    _ = (P + 1) * ((2 ^ k / s + 1) * s) * 2 ^ d := by ring
    _ ≤ (P + 1) * (2 ^ k + s) * 2 ^ d := by gcongr
    _ = (P + 1) * 2 ^ n + (P + 1) * s * 2 ^ d := by
      rw [show 2 ^ n = 2 ^ k * 2 ^ d by rw [← pow_add, hks]]
      ring
    _ ≤ (P + 1) * 2 ^ n + (P + 1) * n * 2 ^ d := by gcongr; exact Nat.sub_le _ _

private theorem error_le (c n : ℕ) (hc : 8 * c ≤ n) (hn : 3 * Nat.log 2 n ≤ n) :
    c * n ^ 2 * 2 ^ (n - 3 * Nat.log 2 n) ≤ 2 ^ n := by
  let q := 2 ^ Nat.log 2 n
  have hq : n < 2 * q := by
    simpa [q, pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
  have hcq : 4 * c ≤ q := by omega
  have hpoly : c * n ^ 2 ≤ q ^ 3 := by
    calc
      c * n ^ 2 ≤ c * (2 * q) ^ 2 := by gcongr
      _ = (4 * c) * q ^ 2 := by ring
      _ ≤ q * q ^ 2 := by gcongr
      _ = q ^ 3 := by ring
  calc
    c * n ^ 2 * 2 ^ (n - 3 * Nat.log 2 n) ≤ q ^ 3 * 2 ^ (n - 3 * Nat.log 2 n) := by gcongr
    _ = 2 ^ n := by
      dsimp [q]
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

private theorem eventually_bound_le (P : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      P * n * bound (3 * Nat.log 2 n) (n - 3 * Nat.log 2 n) (n - 5 * Nat.log 2 n) ≤
        (P + 1) * 2 ^ n := by
  let Q := 3 * P
  -- The polynomial and data terms each contribute at most `2 ^ n` after scaling by `Q * n`.
  filter_upwards [log_le (5 * (Q + 1) + 1), polynomial_le_pow (3 * Q) 5,
    eventually_ge_atTop (max 2 (8 * (17 * Q + 1)))] with n hlog hpoly hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hl : 0 < Nat.log 2 n := Nat.log_pos (by omega) hn2
  have hstrict : 5 * Nat.log 2 n < n := by nlinarith
  have hremoved : (Q + 1) * (5 * Nat.log 2 n) ≤ n := by nlinarith
  have hmain := mainTerm_le Q n hstrict hremoved
  have herr := error_le (17 * Q + 1) n ((le_max_right _ _).trans hn) (by omega)
  have hbound := Nat.mul_le_mul_left (Q * n) (bound_le n hstrict)
  have hsquare : n ≤ n ^ 2 := by nlinarith
  have hmerge : (Q + 1) * n * 2 ^ (n - 3 * Nat.log 2 n) ≤
      (Q + 1) * n ^ 2 * 2 ^ (n - 3 * Nat.log 2 n) := by gcongr
  have htotal : Q * n * bound (3 * Nat.log 2 n) (n - 3 * Nat.log 2 n)
      (n - 5 * Nat.log 2 n) ≤ (Q + 3) * 2 ^ n := by
    nlinarith only [hmain, herr, hpoly, hbound, hmerge]
  dsimp [Q] at htotal
  nlinarith only [htotal]

private theorem exists_circuit_of_split {n k d s : ℕ} (h : k + d = n) (hs : 0 < s)
    (f : BooleanFunction n) : ∃ g ≤ bound k d s, ∃ c : Circuit signature n g 1,
      c.Computes f := by
  subst n
  exact (synthesis f hs).exists_circuit

/-- Lupanov's upper bound: every Boolean function on `n` inputs has a De Morgan circuit
with at most `(1 + ε) 2ⁿ/n` gates, uniformly for sufficiently large `n`. -/
theorem exists_circuit (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f : BooleanFunction n,
      ∃ g, ∃ c : Circuit signature n g 1,
        c.Computes f ∧ (c.size : ℝ) ≤ (1 + ε) * 2 ^ n / n := by
  apply eventually_atTop.mp
  obtain ⟨P, hP⟩ := exists_nat_gt (1 / ε)
  have hP0 : (0 : ℝ) < P := lt_trans (by positivity) hP
  have hcoefficient : (P : ℝ) + 1 ≤ (1 + ε) * P := by
    have := (div_lt_iff₀ hε).mp hP
    nlinarith
  filter_upwards [eventually_bound_le P, log_le 6, eventually_ge_atTop 2] with n hb hl hn
  intro f
  have hlog : 0 < Nat.log 2 n := Nat.log_pos (by omega) hn
  have hsplit : 3 * Nat.log 2 n + (n - 3 * Nat.log 2 n) = n := by omega
  obtain ⟨g, hg, c, hc⟩ := exists_circuit_of_split (s := n - 5 * Nat.log 2 n)
    hsplit (by omega) f
  refine ⟨g, c, hc, ?_⟩
  have hcost : (P : ℝ) * n * g ≤ (P + 1 : ℝ) * 2 ^ n := by
    exact_mod_cast (Nat.mul_le_mul_left (P * n) hg).trans hb
  apply (le_div_iff₀ (by exact_mod_cast (by omega : 0 < n) : (0 : ℝ) < n)).mpr
  apply (mul_le_mul_iff_right₀ hP0).mp
  calc
    (P : ℝ) * (g * n) = P * n * g := by ring
    _ ≤ (P + 1) * 2 ^ n := hcost
    _ ≤ P * ((1 + ε) * 2 ^ n) := by
      nlinarith [mul_le_mul_of_nonneg_right hcoefficient (by positivity : (0 : ℝ) ≤ 2 ^ n)]

end Cslib.Circuits.Boolean.Lupanov
