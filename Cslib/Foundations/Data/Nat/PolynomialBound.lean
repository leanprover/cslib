/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Order

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
    grw [Nat.le_ceil c, Real.norm_natCast, norm_pow, Real.norm_natCast, hcn] at hn
    have hn' : f n ≤ n * n ^ d := by exact_mod_cast hn
    rwa [pow_succ']

/-- A polynomial bound can absorb every finite prefix into its constant factor. -/
theorem polynomiallyBounded_iff_le {f : ℕ → ℕ} :
    PolynomiallyBounded f ↔ ∃ c d : ℕ, ∀ n, f n ≤ c * (n + 1) ^ d := by
  constructor
  · simp_rw [PolynomiallyBounded, eventually_atTop]
    intro ⟨d, m, h⟩
    have ⟨c, hc⟩ := (Set.finite_Iio m).image f |>.exists_le
    use c + 1, d
    intro n
    obtain (hn | hn) := n.lt_or_ge m
    · grw [hc _ ⟨n, hn, rfl⟩, c.le_add_right 1, ← d.one_le_pow' n, mul_one]
    · grw [h n hn, n.le_add_right 1, ← Nat.le_add_left 1 c, one_mul]
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
