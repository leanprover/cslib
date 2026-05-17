/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Real.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Random timed computations

`RandomTimeM T α` is a probability distribution over timed computations returning `α`. Keeping this
wrapper outside `TimeM.lean` lets deterministic timed algorithms avoid probability-theory imports.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

/-- A randomized timed computation is a probability mass function over timed outputs. -/
abbrev RandomTimeM (T : Type*) (α : Type*) := PMF (TimeM T α)

namespace RandomTimeM

variable {α : Type}

/-- The real-valued probability masses of a PMF are summable. -/
private theorem summable_pmf_toReal (p : PMF α) : Summable fun x => (p x).toReal :=
  ENNReal.summable_toReal p.tsum_coe_ne_top

/-- The real-valued probability masses of a PMF sum to one. -/
private theorem tsum_pmf_toReal_eq_one (p : PMF α) : ∑' x, (p x).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq]
  · simp
  · intro x
    exact ne_of_lt ((p.coe_le_one x).trans_lt ENNReal.one_lt_top)

/-- Weighted average of a real-valued quantity over a PMF. -/
noncomputable def expectedValue (p : PMF α) (value : α → ℝ) : ℝ :=
  ∑' x, (p x).toReal * value x

/-- A weighted average of nonnegative values is nonnegative. -/
theorem expectedValue_nonneg {p : PMF α} {value : α → ℝ} (hvalue : ∀ x, 0 ≤ value x) :
    0 ≤ expectedValue p value := by
  unfold expectedValue
  exact tsum_nonneg fun x => mul_nonneg ENNReal.toReal_nonneg (hvalue x)

/--
If a nonnegative quantity is bounded on every possible outcome, then its weighted average satisfies
the same bound.
-/
theorem expectedValue_le_of_nonneg_le_on_support {p : PMF α} {value : α → ℝ} {bound : ℝ}
    (hvalue : ∀ x, 0 ≤ value x) (hbound : ∀ x ∈ p.support, value x ≤ bound) :
    expectedValue p value ≤ bound := by
  unfold expectedValue
  let probability : α → ℝ := fun x => (p x).toReal
  let weightedBound : α → ℝ := fun x => probability x * bound
  have hweightedBound : Summable weightedBound := by
    dsimp [weightedBound, probability]
    exact (summable_pmf_toReal p).mul_right bound
  have hterm_le : ∀ x : α, probability x * value x ≤ weightedBound x := by
    intro x
    by_cases hx : x ∈ p.support
    · dsimp [probability, weightedBound]
      exact mul_le_mul_of_nonneg_left (hbound x hx) ENNReal.toReal_nonneg
    · have hp : p x = 0 := by
        rw [PMF.apply_eq_zero_iff]
        exact hx
      simp [probability, weightedBound, hp]
  have hterm_summable : Summable fun x : α => probability x * value x :=
    Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (hvalue x)) hterm_le hweightedBound
  calc
    ∑' x : α, probability x * value x
        ≤ ∑' x : α, weightedBound x := by
          exact Summable.tsum_le_tsum hterm_le hterm_summable hweightedBound
    _ = (∑' x : α, probability x) * bound := by
          dsimp [weightedBound]
          rw [tsum_mul_right]
    _ = bound := by simp [probability, tsum_pmf_toReal_eq_one]

/-- Expected running time is the weighted average of the time component of each result. -/
noncomputable def expectedTime (p : RandomTimeM ℕ α) : ℝ :=
  expectedValue p fun result => result.time

/-- Expected running time is nonnegative. -/
theorem expectedTime_nonneg (p : RandomTimeM ℕ α) : 0 ≤ p.expectedTime := by
  exact expectedValue_nonneg fun result => by exact_mod_cast Nat.zero_le result.time

/--
If every supported run has cost at most `bound`, then the expected cost is at most `bound`. This is
the basic bridge from pointwise `TimeM` bounds to randomized timed computations.
-/
theorem expectedTime_le_of_time_le_on_support {p : RandomTimeM ℕ α} {bound : ℕ}
    (hbound : ∀ result ∈ p.support, result.time ≤ bound) :
    p.expectedTime ≤ (bound : ℝ) := by
  exact expectedValue_le_of_nonneg_le_on_support
    (fun result => by exact_mod_cast Nat.zero_le result.time)
    (fun result hresult => by exact_mod_cast hbound result hresult)

end RandomTimeM
end Cslib.Algorithms.Lean
