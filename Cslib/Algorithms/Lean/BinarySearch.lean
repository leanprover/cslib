/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CSLib Contributors
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Log

/-!
# Verified Binary Search with Exact Logarithmic Time Complexity

This module formalizes classic half-open interval (`[lo, hi)`) binary search algorithms over
`Array α` instrumented in the `TimeM ℕ` monad, charging 1 tick (`✓`) per element comparison:

- `lowerBound`: first index `i` with `target ≤ xs[i]` (or `xs.size` if none exists).
- `upperBound`: first index `i` with `target < xs[i]` (or `xs.size` if none exists).
- `binarySearch`: returns `some idx` for the leftmost occurrence of `target`, or `none` if absent.
- `equalRangeCount`: counts occurrences of `target` in `O(log n)` comparisons via
  `upperBound - lowerBound`.

## Cost Model

- Each comparison between an array element `xs[i]` and `target` (`<`, `≤`, or `=`) costs 1 tick.
- Index arithmetic (`lo + (hi - lo) / 2`, bounds checks `lo < hi` and `idx < xs.size`) is free.

## Main Results

- `sorted_iff_toList_pairwise`: `Sorted xs ↔ xs.toList.Pairwise (· ≤ ·)`.
- `lowerBound_lt`, `target_le_lowerBound`, `lowerBound_unique`: exact partition specification and
  uniqueness of `lowerBound` on sorted arrays.
- `upperBound_le`, `target_lt_upperBound`, `upperBound_unique`, `lowerBound_le_upperBound`: exact
  partition specification and uniqueness of `upperBound` on sorted arrays.
- `binarySearch_some_iff`, `binarySearch_isSome_iff_mem`, `binarySearch_none_iff_not_mem`:
  `binarySearch` finds the leftmost occurrence of `target` iff `target ∈ xs.toList`.
- `ret_equalRangeCount_eq_count`: `equalRangeCount` computes `xs.toList.count target`.
- `lowerBound_time_le`, `upperBound_time_le`, `binarySearch_time_le`, `lowerBound_replicate_time`:
  tight worst-case comparison bounds `⌈log₂ (n + 1)⌉` and `⌈log₂ (n + 1)⌉ + 1`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

open TimeM

section Sorted

/-- An array `xs` is sorted in non-decreasing order if `i ≤ j` implies `xs[i] ≤ xs[j]` for all
valid indices `i, j < xs.size`. -/
def Sorted {α : Type*} [LE α] (xs : Array α) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hi : i < xs.size) (hj : j < xs.size), i ≤ j → xs[i] ≤ xs[j]

/-- The empty array is sorted. -/
@[simp]
theorem sorted_empty {α : Type*} [LE α] : Sorted (#[] : Array α) :=
  fun _ _ hi => False.elim (Nat.not_lt_zero _ hi)

/-- A replicated array is sorted for any preorder. -/
@[simp]
theorem sorted_replicate {α : Type*} [Preorder α] (n : ℕ) (x : α) :
    Sorted (Array.replicate n x) := by
  intro i j hi hj _
  simp only [Array.getElem_replicate]
  exact le_rfl

/-- `Sorted xs` is equivalent to `xs.toList.Pairwise (· ≤ ·)` for any preorder. -/
theorem sorted_iff_toList_pairwise {α : Type*} [Preorder α] (xs : Array α) :
    Sorted xs ↔ xs.toList.Pairwise (· ≤ ·) := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij
    rw [Array.length_toList] at hi hj
    simpa only [Array.getElem_toList] using h hi hj (Nat.le_of_lt hij)
  · intro h i j hi hj hij
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · have hi' : i < xs.toList.length := by simpa only [Array.length_toList] using hi
      have hj' : j < xs.toList.length := by simpa only [Array.length_toList] using hj
      simpa only [Array.getElem_toList] using h i j hi' hj' hlt

end Sorted

section Algorithms

variable {α : Type*} [LinearOrder α]

/-- Auxiliary half-open interval `[lo, hi)` search for the lower bound of `target` in `xs`.
Charges 1 tick per comparison `xs[mid] < target`. -/
def lowerBoundAux (xs : Array α) (target : α) (lo hi : ℕ) (hhi : hi ≤ xs.size) : TimeM ℕ ℕ :=
  if h : lo < hi then
    let mid := lo + (hi - lo) / 2
    if xs[mid] < target then do
      ✓ lowerBoundAux xs target (mid + 1) hi hhi
    else do
      ✓ lowerBoundAux xs target lo mid (by omega)
  else
    pure lo
termination_by hi - lo

/-- Returns the first index `i ≤ xs.size` such that `target ≤ xs[i]` (when `xs` is sorted),
charging 1 tick per element comparison. -/
def lowerBound (xs : Array α) (target : α) : TimeM ℕ ℕ :=
  lowerBoundAux xs target 0 xs.size (le_refl _)

/-- Auxiliary half-open interval `[lo, hi)` search for the upper bound of `target` in `xs`.
Charges 1 tick per comparison `xs[mid] ≤ target`. -/
def upperBoundAux (xs : Array α) (target : α) (lo hi : ℕ) (hhi : hi ≤ xs.size) : TimeM ℕ ℕ :=
  if h : lo < hi then
    let mid := lo + (hi - lo) / 2
    if xs[mid] ≤ target then do
      ✓ upperBoundAux xs target (mid + 1) hi hhi
    else do
      ✓ upperBoundAux xs target lo mid (by omega)
  else
    pure lo
termination_by hi - lo

/-- Returns the first index `i ≤ xs.size` such that `target < xs[i]` (when `xs` is sorted),
charging 1 tick per element comparison. -/
def upperBound (xs : Array α) (target : α) : TimeM ℕ ℕ :=
  upperBoundAux xs target 0 xs.size (le_refl _)

/-- Searches for `target` in `xs` using `lowerBound`, followed by at most one equality check.
On a sorted array, returns `some idx` for the leftmost occurrence of `target`, or `none` if
`target` is not present. -/
def binarySearch (xs : Array α) (target : α) : TimeM ℕ (Option ℕ) := do
  let idx ← lowerBound xs target
  if h : idx < xs.size then
    ✓ if xs[idx] = target then
        return some idx
      else
        return none
  else
    return none

/-- Counts the number of elements in the equal range `[lowerBound, upperBound)` of `target`,
performing only `O(log n)` comparisons. -/
def equalRangeCount (xs : Array α) (target : α) : TimeM ℕ ℕ := do
  let lo ← lowerBound xs target
  let hi ← upperBound xs target
  return hi - lo

end Algorithms

section Correctness

variable {α : Type*} [LinearOrder α]

/-! ### `lowerBound` Specification -/

/-- `lowerBoundAux` always returns an index at least `lo`. -/
theorem lo_le_ret_lowerBoundAux (xs : Array α) (target : α) (lo hi : ℕ) (hhi : hi ≤ xs.size) :
    lo ≤ ⟪lowerBoundAux xs target lo hi hhi⟫ := by
  fun_induction lowerBoundAux xs target lo hi hhi with
  | case1 lo hi hhi h mid hlt ih =>
    simp only [ret_bind]
    omega
  | case2 lo hi hhi h mid hnlt ih =>
    simp only [ret_bind]
    exact ih
  | case3 lo hi hhi h =>
    simp only [ret_pure]
    exact le_rfl

/-- When `lo ≤ hi`, `lowerBoundAux` returns an index at most `hi`. -/
theorem ret_lowerBoundAux_le (xs : Array α) (target : α) {lo hi : ℕ} (hhi : hi ≤ xs.size)
    (hlo : lo ≤ hi) : ⟪lowerBoundAux xs target lo hi hhi⟫ ≤ hi := by
  fun_induction lowerBoundAux xs target lo hi hhi with
  | case1 lo hi hhi h mid hlt ih =>
    simp only [ret_bind]
    exact ih (by omega)
  | case2 lo hi hhi h mid hnlt ih =>
    simp only [ret_bind]
    have h1 : ⟪lowerBoundAux xs target lo mid (by omega)⟫ ≤ mid := ih (by omega)
    omega
  | case3 lo hi hhi h =>
    simp only [ret_pure]
    exact hlo

/-- `lowerBound` always returns an index in `[0, xs.size]`. -/
theorem ret_lowerBound_le (xs : Array α) (target : α) :
    ⟪lowerBound xs target⟫ ≤ xs.size :=
  ret_lowerBoundAux_le xs target (le_refl _) (Nat.zero_le _)

/-- Every element in `[lo, ⟪lowerBoundAux ...⟫)` is strictly less than `target`. -/
theorem lowerBoundAux_lt_of_lt {xs : Array α} {target : α} (hsorted : Sorted xs)
    {lo hi : ℕ} (hhi : hi ≤ xs.size) :
    ∀ i (hi_size : i < xs.size), lo ≤ i → i < ⟪lowerBoundAux xs target lo hi hhi⟫ →
      xs[i] < target := by
  fun_induction lowerBoundAux xs target lo hi hhi with
  | case1 lo hi hhi h mid hlt ih =>
    intro i hi_size hlo_i hi_ret
    simp only [ret_bind] at hi_ret
    by_cases h_le : i ≤ mid
    · exact lt_of_le_of_lt (hsorted hi_size (by omega) h_le) hlt
    · exact ih i hi_size (by omega) hi_ret
  | case2 lo hi hhi h mid hnlt ih =>
    intro i hi_size hlo_i hi_ret
    simp only [ret_bind] at hi_ret
    exact ih i hi_size hlo_i hi_ret
  | case3 lo hi hhi h =>
    intro i _ hlo_i hi_ret
    simp only [ret_pure] at hi_ret
    omega

/-- Every element in `[⟪lowerBoundAux ...⟫, hi)` is at least `target`. -/
theorem target_le_lowerBoundAux {xs : Array α} {target : α} (hsorted : Sorted xs)
    {lo hi : ℕ} (hhi : hi ≤ xs.size) :
    ∀ i (hi_size : i < xs.size), i < hi → ⟪lowerBoundAux xs target lo hi hhi⟫ ≤ i →
      target ≤ xs[i] := by
  fun_induction lowerBoundAux xs target lo hi hhi with
  | case1 lo hi hhi h mid hlt ih =>
    intro i hi_size hi_lt hi_ret
    simp only [ret_bind] at hi_ret
    exact ih i hi_size hi_lt hi_ret
  | case2 lo hi hhi h mid hnlt ih =>
    intro i hi_size hi_lt hi_ret
    simp only [ret_bind] at hi_ret
    by_cases h_lt : i < mid
    · exact ih i hi_size h_lt hi_ret
    · exact le_trans (not_lt.mp hnlt) (hsorted (by omega) hi_size (by omega))
  | case3 lo hi hhi h =>
    intro i _ hi_lt hi_ret
    simp only [ret_pure] at hi_ret
    omega

/-- On a sorted array, every element before `⟪lowerBound xs target⟫` is strictly less than
`target`. -/
theorem lowerBound_lt {xs : Array α} {target : α} (hsorted : Sorted xs) :
    ∀ i (hi : i < ⟪lowerBound xs target⟫),
      xs[i]'(Nat.lt_of_lt_of_le hi (ret_lowerBound_le xs target)) < target :=
  fun i hi => lowerBoundAux_lt_of_lt hsorted (le_refl _) i
    (Nat.lt_of_lt_of_le hi (ret_lowerBound_le xs target)) (Nat.zero_le _) hi

/-- On a sorted array, every element from `⟪lowerBound xs target⟫` onwards is at least
`target`. -/
theorem target_le_lowerBound {xs : Array α} {target : α} (hsorted : Sorted xs) :
    ∀ i (hi : i < xs.size), ⟪lowerBound xs target⟫ ≤ i → target ≤ xs[i] :=
  fun i hi hle => target_le_lowerBoundAux hsorted (le_refl _) i hi hi hle

/-- Uniqueness of `lowerBound`: on a sorted array, any index `k ≤ xs.size` partitioning `xs` into
`< target` and `≥ target` equals `⟪lowerBound xs target⟫`. -/
theorem lowerBound_unique {xs : Array α} {target : α} {k : ℕ} (hsorted : Sorted xs)
    (hk : k ≤ xs.size)
    (hlt : ∀ i (hi : i < k), xs[i]'(Nat.lt_of_lt_of_le hi hk) < target)
    (hle : ∀ i (hi : i < xs.size), k ≤ i → target ≤ xs[i]) :
    k = ⟪lowerBound xs target⟫ := by
  have hlb_le : ⟪lowerBound xs target⟫ ≤ xs.size := ret_lowerBound_le xs target
  rcases lt_trichotomy k ⟪lowerBound xs target⟫ with hk_lt | rfl | hlb_lt
  · have h1 := lowerBound_lt hsorted k hk_lt
    have h2 := hle k (Nat.lt_of_lt_of_le hk_lt hlb_le) le_rfl
    exact absurd h1 (not_lt_of_ge h2)
  · rfl
  · have h1 := hlt ⟪lowerBound xs target⟫ hlb_lt
    have h2 := target_le_lowerBound hsorted ⟪lowerBound xs target⟫
      (Nat.lt_of_lt_of_le hlb_lt hk) le_rfl
    exact absurd h1 (not_lt_of_ge h2)

/-- Complete characterization of `⟪lowerBound xs target⟫ = k` on a sorted array. -/
theorem lowerBound_eq_iff {xs : Array α} {target : α} {k : ℕ} (hsorted : Sorted xs) :
    ⟪lowerBound xs target⟫ = k ↔
      ∃ hk : k ≤ xs.size,
        (∀ i (hi : i < k), xs[i]'(Nat.lt_of_lt_of_le hi hk) < target) ∧
        (∀ i (hi : i < xs.size), k ≤ i → target ≤ xs[i]) := by
  constructor
  · rintro rfl
    exact ⟨ret_lowerBound_le xs target, lowerBound_lt hsorted, target_le_lowerBound hsorted⟩
  · rintro ⟨hk, hlt, hle⟩
    exact (lowerBound_unique hsorted hk hlt hle).symm

/-! ### `upperBound` Specification -/

/-- `upperBoundAux` always returns an index at least `lo`. -/
theorem lo_le_ret_upperBoundAux (xs : Array α) (target : α) (lo hi : ℕ) (hhi : hi ≤ xs.size) :
    lo ≤ ⟪upperBoundAux xs target lo hi hhi⟫ := by
  fun_induction upperBoundAux xs target lo hi hhi with
  | case1 lo hi hhi h mid hle ih =>
    simp only [ret_bind]
    omega
  | case2 lo hi hhi h mid hnle ih =>
    simp only [ret_bind]
    exact ih
  | case3 lo hi hhi h =>
    simp only [ret_pure]
    exact le_rfl

/-- When `lo ≤ hi`, `upperBoundAux` returns an index at most `hi`. -/
theorem ret_upperBoundAux_le (xs : Array α) (target : α) {lo hi : ℕ} (hhi : hi ≤ xs.size)
    (hlo : lo ≤ hi) : ⟪upperBoundAux xs target lo hi hhi⟫ ≤ hi := by
  fun_induction upperBoundAux xs target lo hi hhi with
  | case1 lo hi hhi h mid hle ih =>
    simp only [ret_bind]
    exact ih (by omega)
  | case2 lo hi hhi h mid hnle ih =>
    simp only [ret_bind]
    have h1 : ⟪upperBoundAux xs target lo mid (by omega)⟫ ≤ mid := ih (by omega)
    omega
  | case3 lo hi hhi h =>
    simp only [ret_pure]
    exact hlo

/-- `upperBound` always returns an index in `[0, xs.size]`. -/
theorem ret_upperBound_le (xs : Array α) (target : α) :
    ⟪upperBound xs target⟫ ≤ xs.size :=
  ret_upperBoundAux_le xs target (le_refl _) (Nat.zero_le _)

/-- Every element in `[lo, ⟪upperBoundAux ...⟫)` is at most `target`. -/
theorem upperBoundAux_le_of_lt {xs : Array α} {target : α} (hsorted : Sorted xs)
    {lo hi : ℕ} (hhi : hi ≤ xs.size) :
    ∀ i (hi_size : i < xs.size), lo ≤ i → i < ⟪upperBoundAux xs target lo hi hhi⟫ →
      xs[i] ≤ target := by
  fun_induction upperBoundAux xs target lo hi hhi with
  | case1 lo hi hhi h mid hle ih =>
    intro i hi_size hlo_i hi_ret
    simp only [ret_bind] at hi_ret
    by_cases h_le : i ≤ mid
    · exact le_trans (hsorted hi_size (by omega) h_le) hle
    · exact ih i hi_size (by omega) hi_ret
  | case2 lo hi hhi h mid hnle ih =>
    intro i hi_size hlo_i hi_ret
    simp only [ret_bind] at hi_ret
    exact ih i hi_size hlo_i hi_ret
  | case3 lo hi hhi h =>
    intro i _ hlo_i hi_ret
    simp only [ret_pure] at hi_ret
    omega

/-- Every element in `[⟪upperBoundAux ...⟫, hi)` is strictly greater than `target`. -/
theorem target_lt_upperBoundAux {xs : Array α} {target : α} (hsorted : Sorted xs)
    {lo hi : ℕ} (hhi : hi ≤ xs.size) :
    ∀ i (hi_size : i < xs.size), i < hi → ⟪upperBoundAux xs target lo hi hhi⟫ ≤ i →
      target < xs[i] := by
  fun_induction upperBoundAux xs target lo hi hhi with
  | case1 lo hi hhi h mid hle ih =>
    intro i hi_size hi_lt hi_ret
    simp only [ret_bind] at hi_ret
    exact ih i hi_size hi_lt hi_ret
  | case2 lo hi hhi h mid hnle ih =>
    intro i hi_size hi_lt hi_ret
    simp only [ret_bind] at hi_ret
    by_cases h_lt : i < mid
    · exact ih i hi_size h_lt hi_ret
    · exact lt_of_lt_of_le (not_le.mp hnle) (hsorted (by omega) hi_size (by omega))
  | case3 lo hi hhi h =>
    intro i _ hi_lt hi_ret
    simp only [ret_pure] at hi_ret
    omega

/-- On a sorted array, every element before `⟪upperBound xs target⟫` is at most `target`. -/
theorem upperBound_le {xs : Array α} {target : α} (hsorted : Sorted xs) :
    ∀ i (hi : i < ⟪upperBound xs target⟫),
      xs[i]'(Nat.lt_of_lt_of_le hi (ret_upperBound_le xs target)) ≤ target :=
  fun i hi => upperBoundAux_le_of_lt hsorted (le_refl _) i
    (Nat.lt_of_lt_of_le hi (ret_upperBound_le xs target)) (Nat.zero_le _) hi

/-- On a sorted array, every element from `⟪upperBound xs target⟫` onwards is strictly greater than
`target`. -/
theorem target_lt_upperBound {xs : Array α} {target : α} (hsorted : Sorted xs) :
    ∀ i (hi : i < xs.size), ⟪upperBound xs target⟫ ≤ i → target < xs[i] :=
  fun i hi hle => target_lt_upperBoundAux hsorted (le_refl _) i hi hi hle

/-- Uniqueness of `upperBound`: on a sorted array, any index `k ≤ xs.size` partitioning `xs` into
`≤ target` and `> target` equals `⟪upperBound xs target⟫`. -/
theorem upperBound_unique {xs : Array α} {target : α} {k : ℕ} (hsorted : Sorted xs)
    (hk : k ≤ xs.size)
    (hle : ∀ i (hi : i < k), xs[i]'(Nat.lt_of_lt_of_le hi hk) ≤ target)
    (hlt : ∀ i (hi : i < xs.size), k ≤ i → target < xs[i]) :
    k = ⟪upperBound xs target⟫ := by
  have hub_le : ⟪upperBound xs target⟫ ≤ xs.size := ret_upperBound_le xs target
  rcases lt_trichotomy k ⟪upperBound xs target⟫ with hk_lt | rfl | hub_lt
  · have h1 := upperBound_le hsorted k hk_lt
    have h2 := hlt k (Nat.lt_of_lt_of_le hk_lt hub_le) le_rfl
    exact absurd h2 (not_lt_of_ge h1)
  · rfl
  · have h1 := hle ⟪upperBound xs target⟫ hub_lt
    have h2 := target_lt_upperBound hsorted ⟪upperBound xs target⟫
      (Nat.lt_of_lt_of_le hub_lt hk) le_rfl
    exact absurd h2 (not_lt_of_ge h1)

/-- Complete characterization of `⟪upperBound xs target⟫ = k` on a sorted array. -/
theorem upperBound_eq_iff {xs : Array α} {target : α} {k : ℕ} (hsorted : Sorted xs) :
    ⟪upperBound xs target⟫ = k ↔
      ∃ hk : k ≤ xs.size,
        (∀ i (hi : i < k), xs[i]'(Nat.lt_of_lt_of_le hi hk) ≤ target) ∧
        (∀ i (hi : i < xs.size), k ≤ i → target < xs[i]) := by
  constructor
  · rintro rfl
    exact ⟨ret_upperBound_le xs target, upperBound_le hsorted, target_lt_upperBound hsorted⟩
  · rintro ⟨hk, hle, hlt⟩
    exact (upperBound_unique hsorted hk hle hlt).symm

/-- On a sorted array, `lowerBound` never exceeds `upperBound`. -/
theorem lowerBound_le_upperBound {xs : Array α} {target : α} (hsorted : Sorted xs) :
    ⟪lowerBound xs target⟫ ≤ ⟪upperBound xs target⟫ := by
  by_contra hlt
  replace hlt : ⟪upperBound xs target⟫ < ⟪lowerBound xs target⟫ := Nat.lt_of_not_ge hlt
  have hub_size : ⟪upperBound xs target⟫ < xs.size :=
    Nat.lt_of_lt_of_le hlt (ret_lowerBound_le xs target)
  have h1 := lowerBound_lt hsorted ⟪upperBound xs target⟫ hlt
  have h2 := target_lt_upperBound hsorted ⟪upperBound xs target⟫ hub_size le_rfl
  exact lt_asymm h1 h2

/-- On a sorted array, the indices `i < xs.size` with `xs[i] = target` are precisely the half-open
range `[⟪lowerBound xs target⟫, ⟪upperBound xs target⟫)`. -/
theorem getElem_eq_target_iff {xs : Array α} {target : α} (hsorted : Sorted xs)
    (i : ℕ) (hi : i < xs.size) :
    xs[i] = target ↔ ⟪lowerBound xs target⟫ ≤ i ∧ i < ⟪upperBound xs target⟫ := by
  constructor
  · intro heq
    constructor
    · by_contra hlt
      have h := lowerBound_lt hsorted i (Nat.lt_of_not_ge hlt)
      exact ne_of_lt h heq
    · by_contra hge
      have h := target_lt_upperBound hsorted i hi (Nat.le_of_not_lt hge)
      exact ne_of_gt h heq
  · rintro ⟨hlb, hub⟩
    exact le_antisymm (upperBound_le hsorted i hub) (target_le_lowerBound hsorted i hi hlb)

/-! ### `binarySearch` and `equalRangeCount` Specifications -/

/-- `binarySearch` returns `some idx` iff `idx` is the leftmost occurrence of `target` in `xs`. -/
theorem binarySearch_some_iff {xs : Array α} {target : α} {idx : ℕ} (hsorted : Sorted xs) :
    ⟪binarySearch xs target⟫ = some idx ↔
      ∃ h : idx < xs.size, xs[idx] = target ∧
        ∀ j (hj : j < idx), xs[j]'(Nat.lt_of_lt_of_le hj (Nat.le_of_lt h)) < target := by
  unfold binarySearch
  simp only [ret_bind]
  constructor
  · intro hbs
    split_ifs at hbs with hlt heq
    · simp only [ret_bind, ret_pure, Option.some.injEq] at hbs
      subst hbs
      exact ⟨hlt, heq, lowerBound_lt hsorted⟩
    · simp only [ret_bind, ret_pure] at hbs
      nomatch hbs
    · simp only [ret_pure] at hbs
      nomatch hbs
  · rintro ⟨hidx, heq, hj_lt⟩
    have hk_eq : idx = ⟪lowerBound xs target⟫ := by
      apply lowerBound_unique hsorted (Nat.le_of_lt hidx) hj_lt
      intro j hj hle
      exact le_of_eq_of_le heq.symm (hsorted hidx hj hle)
    subst hk_eq
    simp [hidx, heq]

/-- `binarySearch` succeeds (`isSome`) iff `target ∈ xs.toList`. -/
theorem binarySearch_isSome_iff_mem {xs : Array α} {target : α} (hsorted : Sorted xs) :
    ⟪binarySearch xs target⟫.isSome ↔ target ∈ xs.toList := by
  constructor
  · intro his
    obtain ⟨idx, hidx⟩ := Option.isSome_iff_exists.mp his
    obtain ⟨hlt, heq, _⟩ := (binarySearch_some_iff hsorted).mp hidx
    rw [← heq, ← Array.getElem_toList (xs := xs) (i := idx) (by simpa using hlt)]
    exact List.getElem_mem _
  · intro hmem
    obtain ⟨k, hk_len, hk_eq⟩ := List.mem_iff_getElem.mp hmem
    have hk_size : k < xs.size := by simpa only [Array.length_toList] using hk_len
    rw [Array.getElem_toList] at hk_eq
    have hlb_le_k : ⟪lowerBound xs target⟫ ≤ k := by
      by_contra hlt
      have h := lowerBound_lt hsorted k (Nat.lt_of_not_ge hlt)
      exact ne_of_lt h hk_eq
    have hlb_size : ⟪lowerBound xs target⟫ < xs.size := Nat.lt_of_le_of_lt hlb_le_k hk_size
    have hlb_eq : xs[⟪lowerBound xs target⟫] = target := by
      apply le_antisymm
      · exact le_of_le_of_eq (hsorted hlb_size hk_size hlb_le_k) hk_eq
      · exact target_le_lowerBound hsorted ⟪lowerBound xs target⟫ hlb_size le_rfl
    have hsome : ⟪binarySearch xs target⟫ = some ⟪lowerBound xs target⟫ :=
      (binarySearch_some_iff hsorted).mpr ⟨hlb_size, hlb_eq, lowerBound_lt hsorted⟩
    rw [hsome]
    rfl

/-- `binarySearch` returns `none` iff `target ∉ xs.toList`. -/
theorem binarySearch_none_iff_not_mem {xs : Array α} {target : α} (hsorted : Sorted xs) :
    ⟪binarySearch xs target⟫ = none ↔ target ∉ xs.toList := by
  rw [← binarySearch_isSome_iff_mem hsorted]
  cases ⟪binarySearch xs target⟫ <;> simp

/-- `equalRangeCount` returns `⟪upperBound xs target⟫ - ⟪lowerBound xs target⟫`. -/
@[simp]
theorem ret_equalRangeCount (xs : Array α) (target : α) :
    ⟪equalRangeCount xs target⟫ = ⟪upperBound xs target⟫ - ⟪lowerBound xs target⟫ :=
  rfl

/-- On a sorted array, `equalRangeCount` computes `xs.toList.count target`. -/
theorem ret_equalRangeCount_eq_count {xs : Array α} {target : α} (hsorted : Sorted xs) :
    ⟪equalRangeCount xs target⟫ = xs.toList.count target := by
  let l := xs.toList
  let lb := ⟪lowerBound xs target⟫
  let ub := ⟪upperBound xs target⟫
  have hlb_ub : lb ≤ ub := lowerBound_le_upperBound hsorted
  have hub_len : ub ≤ l.length := by
    simpa only [l, Array.length_toList] using ret_upperBound_le xs target
  have hsplit1 : l = l.take ub ++ l.drop ub := (List.take_append_drop ub l).symm
  have hsplit2 : l.take ub = l.take lb ++ (l.take ub).drop lb := by
    have h := (List.take_append_drop lb (l.take ub)).symm
    rwa [List.take_take, Nat.min_eq_left hlb_ub] at h
  have hc1 : (l.take lb).count target = 0 := by
    rw [List.count_eq_zero, List.mem_iff_getElem]
    rintro ⟨i, hi, heq⟩
    rw [List.length_take] at hi
    have hi_lb : i < lb := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
    rw [List.getElem_take] at heq
    have hxs_eq : xs[i]'(Nat.lt_of_lt_of_le hi_lb (ret_lowerBound_le xs target)) = target := by
      simpa only [l, Array.getElem_toList] using heq
    exact ne_of_lt (lowerBound_lt hsorted i hi_lb) hxs_eq
  have hc3 : (l.drop ub).count target = 0 := by
    rw [List.count_eq_zero, List.mem_iff_getElem]
    rintro ⟨i, hi, heq⟩
    rw [List.length_drop] at hi
    rw [List.getElem_drop] at heq
    have hub_i : ub + i < xs.size := by
      have : ub + i < l.length := by omega
      simpa only [l, Array.length_toList] using this
    have hxs_eq : xs[ub + i] = target := by simpa only [l, Array.getElem_toList] using heq
    exact ne_of_gt (target_lt_upperBound hsorted (ub + i) hub_i (by omega)) hxs_eq
  have hc2 : ((l.take ub).drop lb).count target = ub - lb := by
    have hlen : ((l.take ub).drop lb).length = ub - lb := by
      rw [List.length_drop, List.length_take, Nat.min_eq_left hub_len]
    rw [← hlen, List.count_eq_length]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [hlen] at hi
    rw [List.getElem_drop, List.getElem_take]
    have h_idx_ub : lb + i < ub := by omega
    have h_idx_size : lb + i < xs.size :=
      Nat.lt_of_lt_of_le h_idx_ub (ret_upperBound_le xs target)
    have hxs_eq : xs[lb + i] = target :=
      (getElem_eq_target_iff hsorted (lb + i) h_idx_size).mpr ⟨by omega, h_idx_ub⟩
    simpa only [l, Array.getElem_toList, beq_iff_eq] using hxs_eq.symm
  change ub - lb = l.count target
  rw [hsplit1, hsplit2, List.count_append, List.count_append, hc1, hc2, hc3]
  omega

end Correctness

section TimeComplexity

variable {α : Type*} [LinearOrder α]

/-- Key recurrence step for binary search interval halving: if `m ≤ (N + 1) / 2` and `1 < N`,
then `1 + Nat.clog 2 m ≤ Nat.clog 2 N`. -/
private theorem one_add_clog2_le (m N : ℕ) (hN : 1 < N) (hm : m ≤ (N + 1) / 2) :
    1 + Nat.clog 2 m ≤ Nat.clog 2 N := by
  rw [Nat.clog_of_one_lt Nat.one_lt_two hN, Nat.add_comm 1]
  exact Nat.add_le_add_right (Nat.clog_monotone 2 hm) 1

/-- `lowerBoundAux` performs at most `⌈log₂ (hi - lo + 1)⌉` comparisons on `[lo, hi)`. -/
theorem lowerBoundAux_time_le (xs : Array α) (target : α) {lo hi : ℕ} (hhi : hi ≤ xs.size)
    (hlo : lo ≤ hi) :
    (lowerBoundAux xs target lo hi hhi).time ≤ Nat.clog 2 (hi - lo + 1) := by
  fun_induction lowerBoundAux xs target lo hi hhi with
  | case1 lo hi hhi h mid hlt ih =>
    simp only [time_bind, time_tick]
    exact le_trans (Nat.add_le_add_left (ih (by omega)) 1)
      (one_add_clog2_le (hi - (mid + 1) + 1) (hi - lo + 1) (by omega) (by omega))
  | case2 lo hi hhi h mid hnlt ih =>
    simp only [time_bind, time_tick]
    exact le_trans (Nat.add_le_add_left (ih (by omega)) 1)
      (one_add_clog2_le (mid - lo + 1) (hi - lo + 1) (by omega) (by omega))
  | case3 lo hi hhi h =>
    have h_eq : lo = hi := Nat.le_antisymm hlo (Nat.le_of_not_lt h)
    subst h_eq
    simp

/-- `lowerBound` performs at most `⌈log₂ (xs.size + 1)⌉` element comparisons. -/
theorem lowerBound_time_le (xs : Array α) (target : α) :
    (lowerBound xs target).time ≤ Nat.clog 2 (xs.size + 1) := by
  simpa only [lowerBound, Nat.sub_zero] using
    lowerBoundAux_time_le xs target (le_refl _) (Nat.zero_le _)

/-- `upperBoundAux` performs at most `⌈log₂ (hi - lo + 1)⌉` comparisons on `[lo, hi)`. -/
theorem upperBoundAux_time_le (xs : Array α) (target : α) {lo hi : ℕ} (hhi : hi ≤ xs.size)
    (hlo : lo ≤ hi) :
    (upperBoundAux xs target lo hi hhi).time ≤ Nat.clog 2 (hi - lo + 1) := by
  fun_induction upperBoundAux xs target lo hi hhi with
  | case1 lo hi hhi h mid hle ih =>
    simp only [time_bind, time_tick]
    exact le_trans (Nat.add_le_add_left (ih (by omega)) 1)
      (one_add_clog2_le (hi - (mid + 1) + 1) (hi - lo + 1) (by omega) (by omega))
  | case2 lo hi hhi h mid hnle ih =>
    simp only [time_bind, time_tick]
    exact le_trans (Nat.add_le_add_left (ih (by omega)) 1)
      (one_add_clog2_le (mid - lo + 1) (hi - lo + 1) (by omega) (by omega))
  | case3 lo hi hhi h =>
    have h_eq : lo = hi := Nat.le_antisymm hlo (Nat.le_of_not_lt h)
    subst h_eq
    simp

/-- `upperBound` performs at most `⌈log₂ (xs.size + 1)⌉` element comparisons. -/
theorem upperBound_time_le (xs : Array α) (target : α) :
    (upperBound xs target).time ≤ Nat.clog 2 (xs.size + 1) := by
  simpa only [upperBound, Nat.sub_zero] using
    upperBoundAux_time_le xs target (le_refl _) (Nat.zero_le _)

/-- `binarySearch` performs at most `⌈log₂ (xs.size + 1)⌉ + 1` element comparisons. -/
theorem binarySearch_time_le (xs : Array α) (target : α) :
    (binarySearch xs target).time ≤ Nat.clog 2 (xs.size + 1) + 1 := by
  unfold binarySearch
  simp only [time_bind]
  have hlb : (lowerBound xs target).time ≤ Nat.clog 2 (xs.size + 1) :=
    lowerBound_time_le xs target
  split_ifs with hlt heq <;> simp only [time_bind, time_tick, time_pure] <;> omega

/-- `equalRangeCount` performs at most `2 * ⌈log₂ (xs.size + 1)⌉` element comparisons. -/
theorem equalRangeCount_time_le (xs : Array α) (target : α) :
    (equalRangeCount xs target).time ≤ 2 * Nat.clog 2 (xs.size + 1) := by
  unfold equalRangeCount
  simp only [time_bind, time_pure]
  have h1 := lowerBound_time_le xs target
  have h2 := upperBound_time_le xs target
  omega

/-! ### Tightness of Logarithmic Bounds -/

/-- Exact comparison count on `Array.replicate n x` over `[lo, hi)`: every comparison `x < x` is
false, so `lowerBoundAux` always takes the left sub-interval of length `(hi - lo) / 2`, achieving
`Nat.clog 2 (hi - lo + 1)` comparisons with equality. -/
theorem lowerBoundAux_replicate_time (n : ℕ) (x : α) {lo hi : ℕ}
    (hhi : hi ≤ (Array.replicate n x).size) (hlo : lo ≤ hi) :
    (lowerBoundAux (Array.replicate n x) x lo hi hhi).time = Nat.clog 2 (hi - lo + 1) := by
  fun_induction lowerBoundAux (Array.replicate n x) x lo hi hhi with
  | case1 lo hi hhi h mid hlt _ =>
    simp only [Array.getElem_replicate, lt_irrefl] at hlt
  | case2 lo hi hhi h mid hnlt ih =>
    simp only [time_bind, time_tick]
    rw [ih (by omega)]
    have hlen : mid - lo + 1 = ((hi - lo + 1) + 2 - 1) / 2 := by omega
    rw [hlen, Nat.add_comm 1, ← Nat.clog_of_one_lt Nat.one_lt_two (by omega)]
  | case3 lo hi hhi h =>
    have h_eq : lo = hi := Nat.le_antisymm hlo (Nat.le_of_not_lt h)
    subst h_eq
    simp

/-- Worst-case tightness for `lowerBound`: on `Array.replicate n x`, `lowerBound` performs
*exactly* `⌈log₂ (n + 1)⌉` comparisons. -/
theorem lowerBound_replicate_time (n : ℕ) (x : α) :
    (lowerBound (Array.replicate n x) x).time = Nat.clog 2 (n + 1) := by
  have h := lowerBoundAux_replicate_time n x (lo := 0) (hi := (Array.replicate n x).size)
    (le_refl _) (Nat.zero_le _)
  simpa only [lowerBound, Array.size_replicate, Nat.sub_zero] using h

/-- Worst-case tightness for `binarySearch`: on a non-empty `Array.replicate n x`, `binarySearch`
performs *exactly* `⌈log₂ (n + 1)⌉ + 1` comparisons. -/
theorem binarySearch_replicate_time {n : ℕ} (hn : 0 < n) (x : α) :
    (binarySearch (Array.replicate n x) x).time = Nat.clog 2 (n + 1) + 1 := by
  have hlb_zero : ⟪lowerBound (Array.replicate n x) x⟫ = 0 := by
    symm
    apply lowerBound_unique (sorted_replicate n x) (Nat.zero_le _)
    · intro i hi
      exact False.elim (Nat.not_lt_zero i hi)
    · intro i hi _
      simp only [Array.getElem_replicate]
      exact le_rfl
  unfold binarySearch
  simp only [time_bind, hlb_zero, Array.size_replicate, hn, ↓reduceDIte, Array.getElem_replicate,
    ↓reduceIte, time_tick, time_pure, lowerBound_replicate_time]
  omega

end TimeComplexity

end Cslib.Algorithms.Lean
