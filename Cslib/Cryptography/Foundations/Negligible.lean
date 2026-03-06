/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Negligible and Polynomial Functions

This file defines the asymptotic notions that underpin cryptographic
security: **negligible** functions (decrease faster than any inverse
polynomial) and **polynomially bounded** functions.

These notions are used throughout modern cryptography to formalize
"the adversary's advantage is negligible in the security parameter."

## Main Definitions

* `Negligible` — `f : ℕ → ℝ` eventually smaller than `1/n^c` for all `c`
* `PolynomiallyBounded` — `|f(n)| ≤ p(n)` for some polynomial `p`

## Main Results

* `Negligible.zero` — the zero function is negligible
* `Negligible.neg` — negligible is closed under negation
* `Negligible.mono` — eventually dominated by negligible implies negligible
* `Negligible.add` — negligible is closed under addition
* `Negligible.mul_polyBounded` — negligible · polynomially bounded is negligible

## References

* [O. Goldreich, *Foundations of Cryptography, Vol. 1*][Goldreich2001]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2014]
-/

open Polynomial

/-- A function `f : ℕ → ℝ` is **negligible** if for every positive exponent `c`,
there exists `N` such that `|f(n)| < 1/n^c` for all `n ≥ N`.

This is the standard definition from modern cryptography. A negligible
function decreases faster than the inverse of any polynomial. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ (c : ℕ), c > 0 → ∃ N : ℕ, ∀ n ≥ N, |f n| < (1 : ℝ) / (n : ℝ) ^ c

/-- A function `f : ℕ → ℝ` is **polynomially bounded** if there exists a
polynomial `p` such that `|f(n)| ≤ p(n)` for all `n`. -/
def PolynomiallyBounded (f : ℕ → ℝ) : Prop :=
  ∃ (p : Polynomial ℕ), ∀ n, |f n| ≤ ↑(p.eval n)

/-- A function `f : ℕ → ℝ` is **non-negligible** if it is not negligible:
there exists a positive exponent `c` such that `|f(n)| ≥ 1/n^c`
infinitely often. -/
def NonNegligible (f : ℕ → ℝ) : Prop := ¬Negligible f

/-- A function `f : ℕ → ℝ` is **noticeable** (or **non-negligible with a
polynomial lower bound**) if there exist `c > 0` and `N` such that
`|f(n)| ≥ 1/n^c` for all `n ≥ N`. -/
def Noticeable (f : ℕ → ℝ) : Prop :=
  ∃ (c : ℕ), c > 0 ∧ ∃ N : ℕ, ∀ n ≥ N, |f n| ≥ (1 : ℝ) / (n : ℝ) ^ c

/-! ### Basic negligible functions -/

/-- The zero function is negligible. -/
theorem Negligible.zero : Negligible (fun _ => 0) := by
  intro c _
  refine ⟨1, fun n hn => ?_⟩
  simp only [abs_zero]
  exact div_pos one_pos (pow_pos (by exact_mod_cast (show 0 < n by omega)) c)

/-- A function that is eventually zero is negligible. -/
theorem Negligible.eventuallyZero {f : ℕ → ℝ} (hf : ∃ N, ∀ n ≥ N, f n = 0) :
    Negligible f := by
  intro c _
  obtain ⟨N, hN⟩ := hf
  refine ⟨max N 1, fun n hn => ?_⟩
  have hfn : f n = 0 := hN n (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [hfn, abs_zero]
  exact div_pos one_pos (pow_pos hn_pos c)

/-! ### Closure properties -/

/-- If `f` is negligible, so is `-f`. -/
theorem Negligible.neg {f : ℕ → ℝ} (hf : Negligible f) :
    Negligible (fun n => -f n) := by
  intro c hc
  obtain ⟨N, hN⟩ := hf c hc
  exact ⟨N, fun n hn => by rw [abs_neg]; exact hN n hn⟩

/-- If `f` is negligible, so is `|f|`. -/
theorem Negligible.abs {f : ℕ → ℝ} (hf : Negligible f) :
    Negligible (fun n => |f n|) := by
  intro c hc
  obtain ⟨N, hN⟩ := hf c hc
  exact ⟨N, fun n hn => by rw [abs_abs]; exact hN n hn⟩

/-- If `g` is negligible and `|f n| ≤ |g n|` eventually, then `f` is negligible. -/
theorem Negligible.mono {f g : ℕ → ℝ}
    (hg : Negligible g) (hle : ∃ N, ∀ n ≥ N, |f n| ≤ |g n|) :
    Negligible f := by
  intro c hc
  obtain ⟨N_g, hN_g⟩ := hg c hc
  obtain ⟨N_h, hN_h⟩ := hle
  refine ⟨max N_g N_h, fun n hn => ?_⟩
  calc |f n| ≤ |g n| := hN_h n (by omega)
    _ < 1 / (n : ℝ) ^ c := hN_g n (by omega)

/-- The sum of two negligible functions is negligible.

*Proof sketch*: Use exponent `c+1` for each summand; then
`|f n| + |g n| < 2/n^(c+1) = 2/(n · n^c) ≤ 1/n^c` for `n ≥ 2`. -/
theorem Negligible.add {f g : ℕ → ℝ} (hf : Negligible f) (hg : Negligible g) :
    Negligible (fun n => f n + g n) := by
  intro c hc
  obtain ⟨Nf, hNf⟩ := hf (c + 1) (by omega)
  obtain ⟨Ng, hNg⟩ := hg (c + 1) (by omega)
  refine ⟨max (max Nf Ng) 2, fun n hn => ?_⟩
  have hn_ge : n ≥ 2 := by omega
  have hNf' := hNf n (by omega)
  have hNg' := hNg n (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
  have hnc_pos := pow_pos hn_pos c
  calc |f n + g n|
      ≤ |f n| + |g n| := abs_add_le _ _
    _ < 1 / (n : ℝ) ^ (c + 1) + 1 / (n : ℝ) ^ (c + 1) := add_lt_add hNf' hNg'
    _ = 2 / ((n : ℝ) ^ c * (n : ℝ)) := by rw [pow_succ]; ring
    _ ≤ 1 / (n : ℝ) ^ c := by
        rw [div_le_div_iff₀ (mul_pos hnc_pos hn_pos) hnc_pos]
        nlinarith

/-- A natural number polynomial evaluated at `n` is eventually at most `n^(natDegree + 1)`.

The bound holds for `n ≥ max 1 (p.eval 1 + 1)`: since
`p.eval n = ∑ coeff_i · n^i ≤ (∑ coeff_i) · n^d = p.eval(1) · n^d ≤ n^(d+1)`. -/
private theorem nat_poly_eval_le_pow (p : Polynomial ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, p.eval n ≤ n ^ (p.natDegree + 1) := by
  refine ⟨max 1 (p.eval 1 + 1), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hn_eval : p.eval 1 ≤ n := by omega
  rw [Polynomial.eval_eq_sum_range]
  calc ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * n ^ i
      ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
          p.coeff i * n ^ p.natDegree := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hn0
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    _ = (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) *
          n ^ p.natDegree := by
        rw [← Finset.sum_mul]
    _ ≤ n * n ^ p.natDegree := by
        apply Nat.mul_le_mul_right
        -- ∑ coeff i = p.eval 1
        have heval1 : ∑ i ∈ Finset.range (p.natDegree + 1),
            p.coeff i = p.eval 1 := by
          rw [Polynomial.eval_eq_sum_range]
          congr 1; ext i; simp
        omega
    _ = n ^ (p.natDegree + 1) := by ring

/-- If `f` is negligible and `g` is polynomially bounded, then `f · g` is negligible.

This is the key lemma for security reductions: a negligible advantage
composed with a polynomial-time reduction remains negligible.

*Proof*: Pick exponent `c + natDegree(p) + 1` for `f`'s negligibility;
then `|f(n)| · |g(n)| < n^d / n^{c+d} = 1/n^c` for large `n`. -/
theorem Negligible.mul_polyBounded {f g : ℕ → ℝ}
    (hf : Negligible f) (hg : PolynomiallyBounded g) :
    Negligible (fun n => f n * g n) := by
  obtain ⟨p, hp⟩ := hg
  intro c hc
  let d := p.natDegree + 1
  obtain ⟨Nf, hNf⟩ := hf (c + d) (by omega)
  obtain ⟨Np, hNp⟩ := nat_poly_eval_le_pow p
  refine ⟨max (max Nf Np) 1, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have h_f := hNf n (by omega)
  have h_p : (↑(p.eval n) : ℝ) ≤ (n : ℝ) ^ d := by
    exact_mod_cast hNp n (by omega)
  have h_g := hp n
  calc |f n * g n|
      = |f n| * |g n| := abs_mul _ _
    _ ≤ |f n| * ↑(p.eval n) :=
        mul_le_mul_of_nonneg_left h_g (abs_nonneg _)
    _ ≤ |f n| * (n : ℝ) ^ d :=
        mul_le_mul_of_nonneg_left h_p (abs_nonneg _)
    _ < (1 / (n : ℝ) ^ (c + d)) * (n : ℝ) ^ d :=
        mul_lt_mul_of_pos_right h_f (pow_pos hn_pos d)
    _ = 1 / (n : ℝ) ^ c := by
        have hnd : (n : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos hn_pos d)
        rw [pow_add, one_div, mul_inv, mul_assoc,
          inv_mul_cancel₀ hnd, mul_one, ← one_div]

/-- The product of two polynomially bounded functions is polynomially bounded.

If `|f(n)| ≤ p(n)` and `|g(n)| ≤ q(n)` for natural-number polynomials `p, q`,
then `|f(n) · g(n)| ≤ (p · q)(n)`. -/
theorem PolynomiallyBounded.mul {f g : ℕ → ℝ}
    (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n * g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨p * q, fun n => ?_⟩
  calc |f n * g n|
      = |f n| * |g n| := abs_mul _ _
    _ ≤ ↑(p.eval n) * ↑(q.eval n) :=
        mul_le_mul (hp n) (hq n) (abs_nonneg _) (by exact_mod_cast Nat.zero_le _)
    _ = ↑((p * q).eval n) := by rw [Polynomial.eval_mul, Nat.cast_mul]

/-- The square of a polynomially bounded function is polynomially bounded. -/
theorem PolynomiallyBounded.sq {f : ℕ → ℝ}
    (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun n => f n ^ 2) := by
  have : (fun n => f n ^ 2) = (fun n => f n * f n) :=
    funext fun n => _root_.sq (f n)
  rw [this]
  exact hf.mul hf

/-- A noticeable function is non-negligible. -/
theorem Noticeable.nonNegligible {f : ℕ → ℝ} (hf : Noticeable f) :
    NonNegligible f := by
  intro hnegl
  obtain ⟨c, hc, N, hN⟩ := hf
  obtain ⟨N', hN'⟩ := hnegl c hc
  have := hN (max N N') (le_max_left _ _)
  have := hN' (max N N') (le_max_right _ _)
  linarith

/-- If `f` is negligible and nonneg, then `fun n => Real.sqrt (f n)` is negligible.

For any target exponent `c`, use `2c` for `f`'s negligibility:
`f n < 1/n^{2c}` implies `√(f n) < 1/n^c`. -/
theorem Negligible.sqrt_nonneg {f : ℕ → ℝ} (hf : Negligible f)
    (hnn : ∀ n, 0 ≤ f n) :
    Negligible (fun n => Real.sqrt (f n)) := by
  intro c hc
  obtain ⟨N, hN⟩ := hf (2 * c) (by omega)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hfn := hN n (by omega)
  rw [abs_of_nonneg (hnn n)] at hfn
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt (f n)
      < Real.sqrt (1 / (n : ℝ) ^ (2 * c)) :=
        Real.sqrt_lt_sqrt (hnn n) hfn
    _ = 1 / (n : ℝ) ^ c := by
        rw [show (n : ℝ) ^ (2 * c) = ((n : ℝ) ^ c) ^ 2 from by ring,
          Real.sqrt_div (le_of_lt one_pos),
          Real.sqrt_one, Real.sqrt_sq (le_of_lt (pow_pos hn_pos c))]

end
