/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-!
# Negligible functions

Negligible bounds are nonnegative real-valued functions with Mathlib's superpolynomial decay at
natural security parameters. This module supplies zero, addition, fixed finite sums, eventual
comparison, and polynomial-loss bounds for security games. Changing finitely many values preserves
negligibility.

The decay bound may depend on the whole algorithm. Security definitions quantify over that
algorithm before asserting negligibility; this module does not change that quantifier order.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped NNReal

/-- An advantage is negligible when it decays faster than every inverse polynomial in the
security parameter. The nonnegative codomain records that advantages are magnitudes;
the decay condition is Mathlib's superpolynomial decay after coercion to the reals. -/
def Negligible (ε : ℕ → ℝ≥0) : Prop :=
  Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ)) (fun n => (ε n : ℝ))

/-- The zero advantage is negligible. -/
@[simp] theorem negligible_zero : Negligible (fun _ => 0) :=
  Asymptotics.superpolynomialDecay_zero _ _

/-- Changing finitely many security parameters preserves negligibility. -/
theorem Negligible.congr' {ε δ : ℕ → ℝ≥0} (hε : Negligible ε)
    (h : ε =ᶠ[Filter.atTop] δ) : Negligible δ :=
  Asymptotics.SuperpolynomialDecay.congr' hε
    (h.mono fun _ hn => congrArg (fun x : ℝ≥0 => (x : ℝ)) hn)

/-- The sum of two negligible bounds is negligible. -/
theorem Negligible.add {ε δ : ℕ → ℝ≥0} (hε : Negligible ε) (hδ : Negligible δ) :
    Negligible (fun n => ε n + δ n) :=
  Asymptotics.SuperpolynomialDecay.add hε hδ

/-- A sum over a fixed finite set of negligible bounds is negligible. -/
theorem Negligible.sum {ι : Type*} (s : Finset ι) {ε : ι → ℕ → ℝ≥0}
    (hε : ∀ i ∈ s, Negligible (ε i)) : Negligible (fun n => ∑ i ∈ s, ε i n) := by
  simpa only [Negligible, Finset.sum_apply] using
    Finset.sum_induction ε Negligible (fun _ _ => Negligible.add) negligible_zero hε

/-- An eventually smaller advantage is negligible. -/
theorem negligible_of_eventually_le {ε δ : ℕ → ℝ≥0} (hδ : Negligible δ)
    (hle : ε ≤ᶠ[Filter.atTop] δ) : Negligible ε :=
  hδ.trans_eventually_abs_le (hle.mono fun n hn =>
    abs_le_abs_of_nonneg (ε n).coe_nonneg (NNReal.coe_le_coe.mpr hn))

/-- A pointwise smaller advantage is negligible. -/
theorem negligible_of_le {ε δ : ℕ → ℝ≥0} (hδ : Negligible δ)
    (hle : ∀ n, ε n ≤ δ n) : Negligible ε :=
  negligible_of_eventually_le hδ (Filter.Eventually.of_forall hle)

/-- Polynomially bounded factors preserve negligible decay. -/
theorem Negligible.polynomiallyBounded_mul {ε : ℕ → ℝ≥0} {p : ℕ → ℕ}
    (hε : Negligible ε) (hp : PolynomiallyBounded p) :
    Negligible (fun n => (p n : ℝ≥0) * ε n) := by
  obtain ⟨d, hd⟩ := hp
  apply (hε.param_pow_mul d).trans_eventually_abs_le
  filter_upwards [hd] with n hn
  simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply, NNReal.coe_mul, NNReal.coe_natCast,
    abs_mul, abs_pow, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (abs_nonneg _)

end Cslib.Crypto
