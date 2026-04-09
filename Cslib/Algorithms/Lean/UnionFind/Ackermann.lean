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

private theorem iterFn_succ_add (n j : ℕ) : iterFn (· + 1) n j = j + n := by
  induction n with
  | zero => simp [iterFn]
  | succ n ih => simp [iterFn, ih]; omega

theorem A_one (j : ℕ) : A 1 j = 2 * j + 1 := by
  show iterFn (A 0) (j + 1) j = 2 * j + 1
  have : ∀ n m, iterFn (A 0) n m = iterFn (· + 1) n m := by
    intro n m; induction n with
    | zero => simp
    | succ n ih => simp [iterFn_succ, ih]
  rw [this]; rw [iterFn_succ_add]; omega

private theorem iterFn_A_one_aux (n j : ℕ) : iterFn (A 1) n j + 1 = 2 ^ n * (j + 1) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    simp only [iterFn_succ, A_one]
    have h := ih j
    -- h: iterFn (A 1) n j + 1 = 2 ^ n * (j + 1)
    -- Goal: 2 * iterFn (A 1) n j + 1 + 1 = 2 ^ (n + 1) * (j + 1)
    have key : 2 ^ (n + 1) * (j + 1) = 2 * (2 ^ n * (j + 1)) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
    rw [key]
    omega

private theorem iterFn_A_one (n j : ℕ) : iterFn (A 1) n j = 2 ^ n * (j + 1) - 1 := by
  have h := iterFn_A_one_aux n j
  omega

theorem A_two (j : ℕ) : A 2 j = 2 ^ (j + 1) * (j + 1) - 1 := by
  show iterFn (A 1) (j + 1) j = 2 ^ (j + 1) * (j + 1) - 1
  exact iterFn_A_one (j + 1) j

/-! ### Monotonicity and growth -/

/-- `iterFn` of a strictly monotone function is monotone in the iteration count. -/
theorem iterFn_mono_left {f : ℕ → ℕ} (hfj : ∀ j, j < f j) (j : ℕ) :
    ∀ i₁ i₂, i₁ ≤ i₂ → iterFn f i₁ j ≤ iterFn f i₂ j := by
  intro i₁ i₂ h
  induction i₂ with
  | zero =>
    have := Nat.le_zero.mp h
    subst this
    exact le_refl _
  | succ i₂ ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · exact le_refl _
    · have h'' : i₁ ≤ i₂ := Nat.lt_succ_iff.mp h'
      exact le_of_lt (calc
        iterFn f i₁ j ≤ iterFn f i₂ j := ih h''
        _ < f (iterFn f i₂ j) := hfj _
        _ = iterFn f (i₂ + 1) j := by simp)

/-- `iterFn` of a strictly monotone function is strictly monotone in the input. -/
theorem iterFn_strictMono_right {f : ℕ → ℕ} (hf : StrictMono f) (i : ℕ) :
    StrictMono (iterFn f i) := by
  induction i with
  | zero => exact strictMono_id
  | succ i ih =>
    intro a b hab
    simp only [iterFn_succ]
    exact hf (ih hab)

private theorem A_strictMono_and_gt (k : ℕ) : StrictMono (A k) ∧ ∀ j, j < A k j := by
  induction k with
  | zero =>
    constructor
    · intro a b hab; simp; omega
    · intro j; simp
  | succ k ih =>
    obtain ⟨hm, hgt⟩ := ih
    constructor
    · intro a b hab
      show iterFn (A k) (a + 1) a < iterFn (A k) (b + 1) b
      calc iterFn (A k) (a + 1) a
          < iterFn (A k) (a + 1) b :=
            iterFn_strictMono_right hm (a + 1) hab
        _ ≤ iterFn (A k) (b + 1) b :=
            iterFn_mono_left hgt b (a + 1) (b + 1) (by omega)
    · intro j
      show j < iterFn (A k) (j + 1) j
      calc j < A k j := hgt j
        _ = iterFn (A k) 1 j := by simp
        _ ≤ iterFn (A k) (j + 1) j :=
            iterFn_mono_left hgt j 1 (j + 1) (by omega)

/-- `A k` is strictly monotone in `j`. -/
theorem A_strictMono_right (k : ℕ) : StrictMono (A k) :=
  (A_strictMono_and_gt k).1

/-- `A k j > j` for all `k, j`. -/
theorem A_gt (k j : ℕ) : j < A k j :=
  (A_strictMono_and_gt k).2 j

/-- `A k j ≥ j + 1` for all `k, j`. -/
theorem A_ge_succ (k j : ℕ) : j + 1 ≤ A k j :=
  A_gt k j

/-- `A` is monotone in `k`: `A k j ≤ A (k+1) j`. -/
private theorem A_succ_ge (k j : ℕ) : A k j ≤ A (k + 1) j := by
  show A k j ≤ iterFn (A k) (j + 1) j
  calc A k j = iterFn (A k) 1 j := by simp
    _ ≤ iterFn (A k) (j + 1) j :=
        iterFn_mono_left (fun j => A_gt k j) j 1 (j + 1) (by omega)

theorem A_mono_left (j : ℕ) : ∀ k₁ k₂, k₁ ≤ k₂ → A k₁ j ≤ A k₂ j := by
  intro k₁ k₂ h
  induction k₂ with
  | zero =>
    have := Nat.le_zero.mp h
    subst this
    exact le_refl _
  | succ k₂ ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · exact le_refl _
    · have h'' : k₁ ≤ k₂ := Nat.lt_succ_iff.mp h'
      exact le_trans (ih h'') (A_succ_ge k₂ j)

/-- `A k 1 ≥ k + 2` — used to prove `alpha` is well-defined. -/
theorem A_one_ge (k : ℕ) : k + 2 ≤ A k 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- A (k+1) 1 = iterFn (A k) 2 1 = A k (A k 1)
    show k + 3 ≤ iterFn (A k) 2 1
    simp only [iterFn_succ, iterFn_zero]
    -- Need: k + 3 ≤ A k (A k 1)
    -- By ih: A k 1 ≥ k + 2
    -- By A_gt: A k (A k 1) > A k 1 ≥ k + 2
    -- So A k (A k 1) ≥ k + 3
    have h1 : k + 2 ≤ A k 1 := ih
    have h2 : 1 < A k 1 := by omega
    have h3 : A k 1 < A k (A k 1) := A_strictMono_right k h2
    omega

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
  intro n₁ n₂ h
  exact Nat.find_mono (fun k hk => le_trans h hk)

/-- `alpha n ≤ n` for all `n`. -/
theorem alpha_le (n : ℕ) : alpha n ≤ n :=
  Nat.find_le (le_trans (by omega) (A_one_ge n))

end Cslib.Algorithms.Lean.UnionFind
