/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Jennings, Bolton Bailey
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Monotonicity of polynomial evaluation

Over a canonically ordered semiring (such as `ℕ`), every coefficient of a polynomial is
nonnegative, so evaluation of the polynomial is a monotone function. This is useful for
reasoning about polynomial time bounds.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
  [CanonicallyOrderedAdd R] (p : R[X])

/-- Over a canonically ordered semiring, evaluation of a polynomial is monotone. -/
theorem monotone_eval : Monotone (fun x : R => p.eval x) := by
  intro a b hab
  simp only [eval_eq_sum, sum_def]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le (a := a)) hab i) (zero_le (a := _))

/-- Over a canonically ordered semiring, evaluation of a polynomial preserves `≤`. -/
theorem eval_le_eval_of_le {a b : R} (hab : a ≤ b) : p.eval a ≤ p.eval b :=
  p.monotone_eval hab

end Polynomial
