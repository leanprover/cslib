/-
Copyright (c) 2026 Juan Bono. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Bono
-/

module

public import Cslib.Init
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Monotone.Basic

@[expose] public section

/-!
# Ackermann Function (CLRS Parameterization)

This file defines the iterated Ackermann function used in the amortized analysis
of union-find with path compression and union by rank.

We use the CLRS parameterization:
- `A 0 j = j + 1`
- `A (k+1) j = (A k)^{j+1}(j)` (apply `A k` to `j`, `j+1` times)

This differs from the standard Peter-Robinson Ackermann function.

## References
- [CLRS] Cormen, Leiserson, Rivest, Stein, *Introduction to Algorithms* (4th ed.), Chapter 19
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

/-- Iterate function `f` on input `j`, a total of `i` times. `iterFn f 0 j = j`. -/
def iterFn (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, j => j
  | i + 1, j => f (iterFn f i j)

@[simp] theorem iterFn_zero (f : ℕ → ℕ) (j : ℕ) : iterFn f 0 j = j := rfl
@[simp] theorem iterFn_succ (f : ℕ → ℕ) (i j : ℕ) :
    iterFn f (i + 1) j = f (iterFn f i j) := rfl

/-- Ackermann function (CLRS parameterization).
`A 0 j = j + 1` and `A (k+1) j = iterFn (A k) (j+1) j`. -/
def A : ℕ → ℕ → ℕ
  | 0, j => j + 1
  | k + 1, j => iterFn (A k) (j + 1) j

@[simp] theorem A_zero (j : ℕ) : A 0 j = j + 1 := rfl
theorem A_succ (k j : ℕ) : A (k + 1) j = iterFn (A k) (j + 1) j := rfl

/-! ### Concrete values -/

theorem A_one (j : ℕ) : A 1 j = 2 * j + 1 := by
  sorry

theorem A_two (j : ℕ) : A 2 j = 2 ^ (j + 1) * (j + 1) - 1 := by
  sorry

/-! ### Monotonicity and growth -/

/-- `iterFn` of a strictly monotone function is monotone in the iteration count. -/
theorem iterFn_mono_left {f : ℕ → ℕ} (hf : StrictMono f) (hfj : ∀ j, j < f j) (j : ℕ) :
    ∀ i₁ i₂, i₁ ≤ i₂ → iterFn f i₁ j ≤ iterFn f i₂ j := by
  sorry

/-- `iterFn` of a strictly monotone function is strictly monotone in the input. -/
theorem iterFn_strictMono_right {f : ℕ → ℕ} (hf : StrictMono f) (i : ℕ) :
    StrictMono (iterFn f i) := by
  sorry

/-- `A k` is strictly monotone in `j`. -/
theorem A_strictMono_right (k : ℕ) : StrictMono (A k) := by
  sorry

/-- `A k j > j` for all `k, j`. -/
theorem A_gt (k j : ℕ) : j < A k j := by
  sorry

/-- `A k j ≥ j + 1` for all `k, j`. -/
theorem A_ge_succ (k j : ℕ) : j + 1 ≤ A k j :=
  A_gt k j

/-- `A` is monotone in `k` for `j ≥ 1`. -/
theorem A_mono_left (j : ℕ) (hj : 1 ≤ j) : ∀ k₁ k₂, k₁ ≤ k₂ → A k₁ j ≤ A k₂ j := by
  sorry

/-- `A k 1 ≥ k + 2` — used to prove `alpha` is well-defined. -/
theorem A_one_ge (k : ℕ) : k + 2 ≤ A k 1 := by
  sorry

/-! ### Inverse Ackermann function -/

/-- Existence witness for `alpha`: for any `n`, there exists `k` with `n ≤ A k 1`. -/
theorem exists_alpha (n : ℕ) : ∃ k, n ≤ A k 1 :=
  ⟨n, le_trans (by omega) (A_one_ge n)⟩

/-- The inverse Ackermann function. `alpha n = min { k : n ≤ A k 1 }`. -/
def alpha (n : ℕ) : ℕ := Nat.find (exists_alpha n)

/-- Defining property: `A (alpha n) 1 ≥ n`. -/
theorem A_alpha_ge (n : ℕ) : n ≤ A (alpha n) 1 :=
  Nat.find_spec (exists_alpha n)

/-- `alpha` is monotone. -/
theorem alpha_mono : Monotone alpha := by
  sorry

/-- `alpha n ≤ n` for all `n`. -/
theorem alpha_le (n : ℕ) : alpha n ≤ n := by
  sorry

end Cslib.Algorithms.Lean.UnionFind
