/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Polynomial bounds on natural-valued functions

`PolynomiallyBounded f` means that `f n ≤ n ^ d` eventually, for some fixed degree `d`.
This is equivalent to a real-valued `IsBigO` bound and to a bound `c * (n + 1) ^ d`
at every input. It is a growth condition and does not assert computability.
-/

@[expose] public section

namespace Cslib

open Asymptotics Filter

/-- A function is polynomially bounded if a fixed power eventually bounds its values. -/
def PolynomiallyBounded (f : ℕ → ℕ) : Prop :=
  ∃ d : ℕ, ∀ᶠ n in atTop, f n ≤ n ^ d

/-- Polynomial growth is equivalent to a big-O bound after casting to the reals. -/
theorem polynomiallyBounded_iff_isBigO {f : ℕ → ℕ} :
    PolynomiallyBounded f ↔
      ∃ d : ℕ, (fun n => (f n : ℝ)) =O[atTop] (fun n => (n : ℝ) ^ d) := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, .of_bound' ?_⟩
    filter_upwards [hd] with n hn
    simpa using (show (f n : ℝ) ≤ (n : ℝ) ^ d by exact_mod_cast hn)
  · rintro ⟨d, hd⟩
    obtain ⟨c, _, hc⟩ := hd.exists_pos
    refine ⟨d + 1, ?_⟩
    filter_upwards [hc.bound, eventually_ge_atTop ⌈c⌉₊] with n hn hcn
    have hc' : c ≤ (n : ℝ) := (Nat.le_ceil c).trans (by exact_mod_cast hcn)
    have hn' : (f n : ℝ) ≤ c * (n : ℝ) ^ d := by simpa using hn
    have hpow : c * (n : ℝ) ^ d ≤ (n : ℝ) ^ (d + 1) := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_right hc' (pow_nonneg (Nat.cast_nonneg n) d)
    exact_mod_cast hn'.trans hpow

/-- A polynomial bound can absorb every finite prefix into its constant factor. -/
theorem polynomiallyBounded_iff_le {f : ℕ → ℕ} :
    PolynomiallyBounded f ↔ ∃ c d : ℕ, ∀ n, f n ≤ c * (n + 1) ^ d := by
  constructor
  · intro hf
    obtain ⟨d, hd⟩ := polynomiallyBounded_iff_isBigO.mp hf
    have hshift : (fun n => (f n : ℝ)) =O[atTop] (fun n => ((n + 1 : ℕ) : ℝ) ^ d) :=
      hd.trans (.of_bound' (Eventually.of_forall fun n => by
        simp only [norm_pow, Real.norm_natCast]
        exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ n) d))
    obtain ⟨c, _, hc⟩ := bound_of_isBigO_nat_atTop hshift
    refine ⟨⌈c⌉₊, d, fun n => ?_⟩
    have hn : (f n : ℝ) ≤ c * ((n + 1 : ℕ) : ℝ) ^ d := by
      simpa only [norm_pow, Real.norm_natCast] using hc (x := n) (by positivity)
    exact_mod_cast hn.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil c) (by positivity))
  · rintro ⟨c, d, hf⟩
    refine ⟨d + 1, ?_⟩
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (c * 2 ^ d)] with n hn hc
    calc
      f n ≤ c * (n + 1) ^ d := hf n
      _ ≤ c * (2 * n) ^ d := by gcongr; lia
      _ = (c * 2 ^ d) * n ^ d := by rw [mul_pow, mul_assoc]
      _ ≤ n * n ^ d := Nat.mul_le_mul_right _ hc
      _ = n ^ (d + 1) := (pow_succ' n d).symm

end Cslib
