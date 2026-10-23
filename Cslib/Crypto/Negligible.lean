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
natural security parameters. This module supplies zero, addition, multiplication, fixed finite
sums, eventual comparison, and polynomial-loss bounds for security games. Changing finitely many
values preserves negligibility.

The decay bound may depend on the whole algorithm. Security definitions quantify over that
algorithm before asserting negligibility; this module does not change that quantifier order.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped NNReal

/-- An advantage is negligible when it decays faster than every inverse polynomial in the
security parameter. The nonnegative codomain records that advantages are magnitudes;
the decay condition is Mathlib's superpolynomial decay in the nonnegative reals. -/
def Negligible (ε : ℕ → ℝ≥0) : Prop :=
  Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ≥0)) ε

theorem negligible_iff (ε : ℕ → ℝ≥0) :
    Negligible ε ↔ ∀ k : ℕ, ∀ δ > (0 : ℝ≥0), ∃ m : ℕ, ∀ n ≥ m, n ^ k * ε n < δ := by
  simp [Negligible, Asymptotics.SuperpolynomialDecay, tendsto_order]

/-- The zero advantage is negligible. -/
@[simp] theorem negligible_zero : Negligible (fun _ => 0) :=
  Asymptotics.superpolynomialDecay_zero _ _

/-- Changing the value of a negligible bound at finitely many security parameters preserves
negligibility. -/
theorem Negligible.congr' {ε δ : ℕ → ℝ≥0} (hε : Negligible ε)
    (h : ε =ᶠ[Filter.atTop] δ) : Negligible δ :=
  Asymptotics.SuperpolynomialDecay.congr' hε h

/-- The sum of two negligible bounds is negligible. -/
theorem Negligible.add {ε δ : ℕ → ℝ≥0} (hε : Negligible ε) (hδ : Negligible δ) :
    Negligible (ε + δ) :=
  Asymptotics.SuperpolynomialDecay.add hε hδ

/-- The product of two negligible bounds is negligible. -/
theorem Negligible.mul {ε δ : ℕ → ℝ≥0} (hε : Negligible ε) (hδ : Negligible δ) :
    Negligible (ε * δ) :=
  Asymptotics.SuperpolynomialDecay.mul hε hδ

/-- A sum over a fixed finite set of negligible bounds is negligible. -/
theorem Negligible.sum {ι : Type*} (s : Finset ι) {ε : ι → ℕ → ℝ≥0}
    (hε : ∀ i ∈ s, Negligible (ε i)) : Negligible (∑ i ∈ s, ε i) :=
  Finset.sum_induction ε Negligible @Negligible.add negligible_zero hε

/-- An eventually smaller advantage is negligible. -/
theorem negligible_of_eventually_le {ε δ : ℕ → ℝ≥0} (hδ : Negligible δ)
    (hle : ε ≤ᶠ[Filter.atTop] δ) : Negligible ε :=
  .trans_eventuallyLE (.of_le zero_le) negligible_zero hδ (.of_le zero_le) hle

/-- A pointwise smaller advantage is negligible. -/
theorem negligible_of_le {ε δ : ℕ → ℝ≥0} (hδ : Negligible δ)
    (hle : ∀ n, ε n ≤ δ n) : Negligible ε :=
  negligible_of_eventually_le hδ (Filter.Eventually.of_forall hle)

/-- Polynomially bounded factors preserve negligible decay. -/
theorem Negligible.polynomiallyBounded_mul {ε : ℕ → ℝ≥0} {p : ℕ → ℕ}
    (hε : Negligible ε) (hp : PolynomiallyBounded p) :
    Negligible (fun n => (p n : ℝ≥0) * ε n) := by
  obtain ⟨d, hd⟩ := hp
  refine .trans_eventuallyLE (.of_le zero_le) negligible_zero (hε.param_pow_mul d)
    (.of_le zero_le) ?_
  filter_upwards [hd] with n hn
  exact mul_le_mul' (by rw [Pi.pow_apply]; exact_mod_cast hn) le_rfl

end Cslib.Crypto
