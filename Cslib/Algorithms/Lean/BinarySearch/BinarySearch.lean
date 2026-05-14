/-
Copyright (c) 2025 Zac Nwokeafor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zac Nwokeafor
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Log

@[expose] public section

/-!
# Binary Search on a sorted array

In this file we introduce a `binarySearch` algorithm that returns a time
monad over an optional index `TimeM ℕ (Option ℕ)`. The time complexity
of `binarySearch` is the number of comparisons.

## Main results

- `binarySearch_found`: If `binarySearch` returns `some mid`,
  then `arr[mid] = target`.
- `binarySearch_not_found`: If `binarySearch` returns `none` on a sorted
  array, then the target is not in the array.
- `binarySearch_time`: The number of comparisons of `binarySearch` is at
  most `⌈log₂(n + 1)⌉`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type} [LinearOrder α]

/-- An array is sorted if `i ≤ j → arr[i] ≤ arr[j]`. -/
def Sorted (arr : Array α) : Prop :=
  ∀ (i j : ℕ) (hi : i < arr.size) (hj : j < arr.size),
    i ≤ j → arr[i] ≤ arr[j]

/-- Binary search auxiliary: searches `arr[lo..hi)` for `target`,
counting comparisons. Returns `some mid` where `arr[mid] = target`,
or `none` if not found. -/
def binarySearchAux (arr : Array α) (target : α)
    (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ arr.size) :
    TimeM ℕ (Option ℕ) :=
  if h : lo = hi then
    pure none
  else
    have hlt : lo < hi := Nat.lt_of_le_of_ne hlo h
    let mid := lo + (hi - lo) / 2
    have hmid_hi : mid < hi := by omega
    have hmid_size : mid < arr.size := by omega
    if hlt_mid : arr[mid] < target then
      ⟨(binarySearchAux arr target (mid + 1) hi
         (by omega) hhi).ret,
       1 + (binarySearchAux arr target (mid + 1) hi
         (by omega) hhi).time⟩
    else if hgt_mid : target < arr[mid] then
      ⟨(binarySearchAux arr target lo mid
         (by omega) (by omega)).ret,
       1 + (binarySearchAux arr target lo mid
         (by omega) (by omega)).time⟩
    else
      ⟨some mid, 1⟩
termination_by hi - lo

/-- Searches a sorted array for `target`, counting comparisons as
time cost. Returns a `TimeM ℕ (Option ℕ)` where the time represents
the number of comparisons. -/
def binarySearch (arr : Array α) (target : α) :
    TimeM ℕ (Option ℕ) :=
  binarySearchAux arr target 0 arr.size
    (Nat.zero_le _) (Nat.le_refl _)

section Correctness

/-- The result index of `binarySearchAux` lies within
`[lo, hi)`. -/
theorem binarySearchAux_bounds (arr : Array α) (target : α)
    (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ arr.size)
    {mid : ℕ}
    (hresult : ⟪binarySearchAux arr target lo hi hlo hhi⟫ =
      some mid) :
    lo ≤ mid ∧ mid < hi := by
  unfold binarySearchAux at hresult
  split at hresult
  · exact absurd hresult nofun
  · rename_i h
    have hlt : lo < hi := Nat.lt_of_le_of_ne hlo h
    let m := lo + (hi - lo) / 2
    have hm_hi : m < hi := by omega
    simp only [show lo + (hi - lo) / 2 = m from rfl]
      at hresult
    split at hresult
    · have ih := binarySearchAux_bounds arr target
        (m + 1) hi (by omega) hhi hresult
      exact ⟨by omega, ih.2⟩
    · split at hresult
      · have ih := binarySearchAux_bounds arr target
          lo m (by omega) (by omega) hresult
        exact ⟨ih.1, by omega⟩
      · simp only [Option.some.injEq] at hresult
        subst hresult
        exact ⟨by omega, hm_hi⟩
termination_by hi - lo

/-- If `binarySearchAux` returns `some mid`, then
`arr[mid] = target`. -/
theorem binarySearchAux_found (arr : Array α) (target : α)
    (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ arr.size)
    {mid : ℕ}
    (hresult : ⟪binarySearchAux arr target lo hi hlo hhi⟫ =
      some mid) :
    have : mid < arr.size := by
      have := binarySearchAux_bounds arr target lo hi
        hlo hhi hresult; omega
    arr[mid] = target := by
  unfold binarySearchAux at hresult
  split at hresult
  · exact absurd hresult nofun
  · rename_i h
    have hlt : lo < hi := Nat.lt_of_le_of_ne hlo h
    let m := lo + (hi - lo) / 2
    have hm_hi : m < hi := by omega
    have hm_size : m < arr.size := by omega
    simp only [show lo + (hi - lo) / 2 = m from rfl]
      at hresult
    split at hresult
    · exact binarySearchAux_found arr target (m + 1) hi
        (by omega) hhi hresult
    · split at hresult
      · exact binarySearchAux_found arr target lo m
          (by omega) (by omega) hresult
      · rename_i hlt_mid hgt_mid
        simp only [Option.some.injEq] at hresult
        subst hresult
        exact le_antisymm (not_lt.mp hgt_mid)
          (not_lt.mp hlt_mid)
termination_by hi - lo

/-- If `binarySearchAux` returns `none` on a sorted array,
the target is not in `arr[lo..hi)`. -/
theorem binarySearchAux_not_found (arr : Array α)
    (target : α) (lo hi : ℕ)
    (hlo : lo ≤ hi) (hhi : hi ≤ arr.size)
    (hsorted : Sorted arr)
    (hresult : ⟪binarySearchAux arr target lo hi hlo hhi⟫ =
      none) :
    ∀ (i : ℕ) (h : i < arr.size),
      lo ≤ i → i < hi → arr[i] ≠ target := by
  unfold binarySearchAux at hresult
  split at hresult
  · rename_i heq; intro i _ hge hlt; omega
  · rename_i h
    have hlt : lo < hi := Nat.lt_of_le_of_ne hlo h
    let m := lo + (hi - lo) / 2
    have hm_hi : m < hi := by omega
    have hm_size : m < arr.size := by omega
    simp only [show lo + (hi - lo) / 2 = m from rfl]
      at hresult
    split at hresult
    · rename_i hlt_mid
      intro i hi_bound hge hlt_i
      have ih := binarySearchAux_not_found arr target
        (m + 1) hi (by omega) hhi hsorted hresult
      by_cases him : i ≤ m
      · intro heq
        have hsle : arr[i] ≤ arr[m] :=
          hsorted i m hi_bound hm_size him
        rw [heq] at hsle
        exact absurd (lt_of_le_of_lt hsle hlt_mid)
          (lt_irrefl _)
      · exact ih i hi_bound (by omega) hlt_i
    · split at hresult
      · rename_i _ hgt_mid
        intro i hi_bound hge hlt_i
        have ih := binarySearchAux_not_found arr target
          lo m (by omega) (by omega) hsorted hresult
        by_cases him : i < m
        · exact ih i hi_bound hge him
        · intro heq
          have hsle : arr[m] ≤ arr[i] :=
            hsorted m i hm_size hi_bound (by omega)
          rw [heq] at hsle
          exact absurd (lt_of_le_of_lt hsle hgt_mid)
            (lt_irrefl _)
      · exact absurd hresult nofun
termination_by hi - lo

/-- If `binarySearch` returns `some mid`,
then `arr[mid] = target`. -/
theorem binarySearch_found (arr : Array α) (target : α)
    {mid : ℕ}
    (hresult : ⟪binarySearch arr target⟫ = some mid) :
    ∃ (h : mid < arr.size), arr[mid] = target := by
  unfold binarySearch at hresult
  have hbounds := binarySearchAux_bounds arr target
    0 arr.size (Nat.zero_le _) (Nat.le_refl _) hresult
  have hmid_size : mid < arr.size := by omega
  exact ⟨hmid_size, binarySearchAux_found arr target
    0 arr.size _ _ hresult⟩

/-- If `binarySearch` returns `none` on a sorted array,
the target is not in the array. -/
theorem binarySearch_not_found (arr : Array α) (target : α)
    (hsorted : Sorted arr)
    (hresult : ⟪binarySearch arr target⟫ = none) :
    ∀ (i : ℕ) (h : i < arr.size),
      arr[i] ≠ target := by
  unfold binarySearch at hresult
  intro i h
  exact binarySearchAux_not_found arr target
    0 arr.size _ _ hsorted hresult i h
    (Nat.zero_le _) h

end Correctness

section TimeComplexity

open Nat (clog)

/-- Recurrence relation for the time complexity of binary search.
For an interval of size `n`, this counts the total number of
comparisons:
- Base case: 0 comparisons for an empty interval
- Recursive case: compare the midpoint, then recurse on the
  appropriate half -/
def timeBinarySearchRec : ℕ → ℕ
  | 0 => 0
  | n@(_+1) => timeBinarySearchRec (n / 2) + 1

/-- `timeBinarySearchRec` is monotone. -/
theorem timeBinarySearchRec_mono {m n : ℕ} (h : m ≤ n) :
    timeBinarySearchRec m ≤ timeBinarySearchRec n := by
  suffices ∀ n, ∀ m ≤ n,
      timeBinarySearchRec m ≤ timeBinarySearchRec n from
    this n m h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hm
    match m, n, hm with
    | 0, _, _ => simp [timeBinarySearchRec]
    | _ + 1, 0, hm => omega
    | m + 1, n + 1, hm =>
      simp only [timeBinarySearchRec]
      have hdiv : (m + 1) / 2 ≤ (n + 1) / 2 :=
        Nat.div_le_div_right (by omega)
      have hlt : (n + 1) / 2 < n + 1 :=
        Nat.div_lt_self (by omega) (by omega)
      exact Nat.add_le_add_right (ih _ hlt _ hdiv) 1

/-- Upper bound: `T(n) ≤ ⌈log₂(n + 1)⌉` -/
theorem timeBinarySearchRec_le (n : ℕ) :
    timeBinarySearchRec n ≤ clog 2 (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [timeBinarySearchRec]
    | n + 1 =>
      simp only [timeBinarySearchRec]
      have hlt : (n + 1) / 2 < n + 1 :=
        Nat.div_lt_self (by omega) (by omega)
      have ih_half := ih _ hlt
      rw [show n + 1 + 1 = n + 2 from rfl]
      rw [Nat.clog_of_one_lt (by omega : (1 : ℕ) < 2)
        (by omega : 1 < n + 2)]
      apply Nat.add_le_add_right
      have hceil :
          (n + 1) / 2 + 1 ≤ (n + 2 + 2 - 1) / 2 := by
        omega
      exact le_trans ih_half
        (Nat.clog_mono_right 2 hceil)

/-- Time of `binarySearchAux` is at most the recurrence on
`hi - lo`. -/
theorem binarySearchAux_time (arr : Array α) (target : α)
    (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ arr.size) :
    (binarySearchAux arr target lo hi hlo hhi).time ≤
      timeBinarySearchRec (hi - lo) := by
  unfold binarySearchAux
  split
  · simp only [time_pure, Nat.zero_le]
  · rename_i h
    have hlt : lo < hi := Nat.lt_of_le_of_ne hlo h
    let m := lo + (hi - lo) / 2
    have hm_hi : m < hi := by omega
    simp only [show lo + (hi - lo) / 2 = m from rfl]
    have hpos : 0 < hi - lo := by omega
    split
    · have ih := binarySearchAux_time arr target
        (m + 1) hi (by omega) hhi
      have hle : hi - (m + 1) ≤ (hi - lo) / 2 := by
        omega
      calc 1 + (binarySearchAux arr target
            (m + 1) hi _ hhi).time
          ≤ 1 + timeBinarySearchRec (hi - (m + 1)) :=
            by omega
        _ ≤ 1 + timeBinarySearchRec ((hi - lo) / 2) :=
            Nat.add_le_add_left
              (timeBinarySearchRec_mono hle) 1
        _ ≤ timeBinarySearchRec (hi - lo) := by
            match hi - lo, hpos with
            | n + 1, _ =>
              simp [timeBinarySearchRec]; omega
    · split
      · have ih := binarySearchAux_time arr target
          lo m (by omega) (by omega)
        have hle : m - lo ≤ (hi - lo) / 2 := by omega
        calc 1 + (binarySearchAux arr target
              lo m _ _).time
            ≤ 1 + timeBinarySearchRec (m - lo) :=
              by omega
          _ ≤ 1 + timeBinarySearchRec
                ((hi - lo) / 2) :=
              Nat.add_le_add_left
                (timeBinarySearchRec_mono hle) 1
          _ ≤ timeBinarySearchRec (hi - lo) := by
              match hi - lo, hpos with
              | n + 1, _ =>
                simp [timeBinarySearchRec]; omega
      · have : 0 < hi - lo := by omega
        match hi - lo, this with
        | n + 1, _ =>
          simp [timeBinarySearchRec]
termination_by hi - lo

/-- Time complexity of binarySearch: at most `⌈log₂(n + 1)⌉`
comparisons. -/
theorem binarySearch_time (arr : Array α) (target : α) :
    let n := arr.size
    (binarySearch arr target).time ≤ clog 2 (n + 1) := by
  unfold binarySearch
  have h1 := binarySearchAux_time arr target
    0 arr.size (Nat.zero_le _) (Nat.le_refl _)
  simp only [Nat.sub_zero] at h1
  exact le_trans h1 (timeBinarySearchRec_le _)

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
