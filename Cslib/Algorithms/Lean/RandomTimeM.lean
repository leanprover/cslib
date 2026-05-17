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

/--
Expectation of a natural-number-valued quantity, kept in `ENNReal`. This version has the clean monad
law, so randomized algorithms can do the algebra there and convert back to `ℝ` once a finite bound
is known.
-/
noncomputable def expectedNat (p : PMF α) (value : α → ℕ) : ENNReal :=
  ∑' x, p x * value x

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

/-- A pure distribution has the obvious expectation. -/
@[simp]
theorem expectedNat_pure (x : α) (value : α → ℕ) :
    expectedNat (PMF.pure x) value = value x := by
  unfold expectedNat
  rw [tsum_eq_single x]
  · simp
  · intro y hy
    simp [PMF.pure_apply_of_ne _ _ hy]

/-- The `ENNReal` expectation satisfies the monad law without any finiteness side condition. -/
theorem expectedNat_bind {β : Type} (p : PMF α) (f : α → PMF β) (value : β → ℕ) :
    expectedNat (p.bind f) value =
      ∑' x, p x * expectedNat (f x) value := by
  unfold expectedNat
  calc
    ∑' y, (p.bind f) y * value y
        = ∑' y, (∑' x, p x * f x y) * value y := by
          simp
    _ = ∑' y, ∑' x, p x * f x y * value y := by
          simp_rw [ENNReal.tsum_mul_right]
    _ = ∑' x, ∑' y, p x * f x y * value y := by
          exact ENNReal.tsum_comm
    _ = ∑' x, p x * ∑' y, f x y * value y := by
          simp_rw [mul_assoc, ENNReal.tsum_mul_left]

/-- Expectation distributes over addition for natural-number-valued quantities. -/
theorem expectedNat_add (p : PMF α) (value₁ value₂ : α → ℕ) :
    expectedNat p (fun x => value₁ x + value₂ x) =
      expectedNat p value₁ + expectedNat p value₂ := by
  unfold expectedNat
  simp_rw [Nat.cast_add, mul_add]
  rw [ENNReal.tsum_add]

/-- The expectation of a constant natural-number-valued quantity is that constant. -/
theorem expectedNat_const (p : PMF α) (value : ℕ) :
    expectedNat p (fun _ => value) = value := by
  unfold expectedNat
  rw [ENNReal.tsum_mul_right]
  simp

/-- A finite pointwise bound keeps the natural-number expectation finite. -/
theorem expectedNat_le_of_le_on_support {p : PMF α} {value : α → ℕ} {bound : ℕ}
    (hbound : ∀ x ∈ p.support, value x ≤ bound) :
    expectedNat p value ≤ bound := by
  unfold expectedNat
  calc
    ∑' x, p x * value x
        ≤ ∑' x, p x * bound := by
          exact ENNReal.tsum_le_tsum fun x => by
            by_cases hx : x ∈ p.support
            · exact mul_le_mul_right (by exact_mod_cast hbound x hx) (p x)
            · have hp : p x = 0 := by
                rw [PMF.apply_eq_zero_iff]
                exact hx
              simp [hp]
    _ = (∑' x, p x) * bound := by
          rw [ENNReal.tsum_mul_right]
    _ = bound := by simp

/-- Expected running time is the weighted average of the time component of each result. -/
noncomputable def expectedTime (p : RandomTimeM ℕ α) : ℝ :=
  expectedValue p fun result => result.time

/-- Expected running time as an extended nonnegative real. -/
noncomputable def expectedTimeENNReal (p : RandomTimeM ℕ α) : ENNReal :=
  expectedNat p fun result => result.time

/-- The real and `ENNReal` expected-time views agree after converting back to `ℝ`. -/
theorem expectedTime_eq_toReal_expectedTimeENNReal (p : RandomTimeM ℕ α) :
    p.expectedTime = p.expectedTimeENNReal.toReal := by
  unfold expectedTime expectedTimeENNReal expectedValue expectedNat
  rw [ENNReal.tsum_toReal_eq]
  · simp [ENNReal.toReal_mul]
  · intro result
    exact ENNReal.mul_ne_top
      (ne_of_lt ((p.coe_le_one result).trans_lt ENNReal.one_lt_top))
      (by exact_mod_cast (WithTop.coe_ne_top : (result.time : ENNReal) ≠ ⊤))

/-- Expected running time is nonnegative. -/
theorem expectedTime_nonneg (p : RandomTimeM ℕ α) : 0 ≤ p.expectedTime := by
  exact expectedValue_nonneg fun result => by exact_mod_cast Nat.zero_le result.time

/-- The extended expected time satisfies the monad law. -/
theorem expectedTimeENNReal_bind {β : Type} (p : PMF α) (f : α → RandomTimeM ℕ β) :
    expectedTimeENNReal (p.bind f) =
      ∑' x, p x * expectedTimeENNReal (f x) := by
  exact expectedNat_bind p f fun result => result.time

/-- Binding to a pure timed result with a fixed extra cost adds that cost to expected time. -/
theorem expectedTimeENNReal_bind_pure_add {β : Type} (p : RandomTimeM ℕ α) (base : ℕ)
    (ret : TimeM ℕ α → β) :
    expectedTimeENNReal (p.bind fun result => PMF.pure ⟨ret result, base + result.time⟩) =
      (base : ENNReal) + p.expectedTimeENNReal := by
  rw [expectedTimeENNReal_bind]
  simp only [expectedTimeENNReal, expectedNat_pure]
  rw [← expectedNat]
  calc
    expectedNat p (fun result => base + result.time)
        = expectedNat p (fun _ => base) + expectedNat p fun result => result.time := by
          exact expectedNat_add p (fun _ => base) fun result => result.time
    _ = (base : ENNReal) + expectedTimeENNReal p := by
          rw [expectedNat_const]
          rfl

/--
Expected time for two independent randomized timed computations followed by a pure recombination.
This is the algebraic shape used by divide-and-conquer algorithms such as randomized quicksort.
-/
theorem expectedTimeENNReal_bind_pure_add_pair {β γ : Type} (left : RandomTimeM ℕ α)
    (right : RandomTimeM ℕ β) (base : ℕ) (ret : TimeM ℕ α → TimeM ℕ β → γ) :
    expectedTimeENNReal
        (left.bind fun leftResult =>
          right.bind fun rightResult =>
            PMF.pure ⟨ret leftResult rightResult, base + leftResult.time + rightResult.time⟩) =
      (base : ENNReal) + left.expectedTimeENNReal + right.expectedTimeENNReal := by
  rw [expectedTimeENNReal_bind]
  simp only [expectedTimeENNReal_bind_pure_add]
  simp_rw [Nat.cast_add]
  unfold expectedTimeENNReal expectedNat
  have hleft :
      (∑' leftResult : TimeM ℕ α, left leftResult * (↑base + ↑leftResult.time)) =
        (base : ENNReal) + ∑' leftResult : TimeM ℕ α, left leftResult * ↑leftResult.time := by
    have hbase : (∑' leftResult : TimeM ℕ α, left leftResult * (base : ENNReal)) = base := by
      rw [ENNReal.tsum_mul_right]
      simp
    have hadd := expectedNat_add left (fun _ => base) fun leftResult => leftResult.time
    unfold expectedNat at hadd
    simp_rw [Nat.cast_add] at hadd
    rw [hadd, hbase]
  calc
    ∑' leftResult, left leftResult * ((base : ENNReal) + ↑leftResult.time +
        (∑' rightResult, right rightResult * ↑rightResult.time))
        = (∑' leftResult, left leftResult * ((base : ENNReal) + ↑leftResult.time)) +
            ∑' leftResult, left leftResult *
              (∑' rightResult, right rightResult * ↑rightResult.time) := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add]
    _ = (∑' leftResult, left leftResult * ((base : ENNReal) + ↑leftResult.time)) +
            (∑' rightResult, right rightResult * ↑rightResult.time) := by
          rw [ENNReal.tsum_mul_right]
          simp
    _ = (base : ENNReal) + (∑' leftResult, left leftResult * ↑leftResult.time) +
            (∑' rightResult, right rightResult * ↑rightResult.time) := by
          rw [hleft]

/-- A pointwise time bound also bounds the extended expected time. -/
theorem expectedTimeENNReal_le_of_time_le_on_support {p : RandomTimeM ℕ α} {bound : ℕ}
    (hbound : ∀ result ∈ p.support, result.time ≤ bound) :
    p.expectedTimeENNReal ≤ bound := by
  exact expectedNat_le_of_le_on_support hbound

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
