/-
Copyright (c) 2026 Robert Joseph George. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph George
-/

module

public import Cslib.Algorithms.Lean.RandomTimeM
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Basic
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Tactic.Linarith

/-!
# Randomized quicksort on lists

The algorithm samples a pivot index uniformly, removes that occurrence, and partitions the remaining
items into elements below, equal to, and above the pivot. The equal bucket is not recursively
sorted, which is the usual duplicate-safe randomized quicksort.

The cost model counts the two order tests used by the three-way partition. The theorems prove a
quadratic worst-case bound for every random run and the corresponding bound on
`RandomTimeM.expectedTime`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type}

/-- Chooses an index uniformly from a nonempty list. -/
noncomputable def randomPivotIndex (xs : List α) (hxs : 0 < xs.length) : PMF (Fin xs.length) := by
  letI : Nonempty (Fin xs.length) := ⟨⟨0, hxs⟩⟩
  exact PMF.uniformOfFintype (Fin xs.length)

/-- Removing a valid pivot occurrence strictly shortens the list. -/
private theorem eraseIdx_length_lt (xs : List α) (i : Fin xs.length) :
    (xs.eraseIdx i).length < xs.length := by
  have h : (xs.eraseIdx i).length + 1 = xs.length := by
    simpa using List.length_eraseIdx_add_one (l := xs) (i := (i : ℕ)) i.isLt
  omega

variable [LinearOrder α]

/--
Three-way partition around a pivot. It costs two comparisons per scanned element: one test for
`x < pivot`, and if needed one test for `pivot < x`.
-/
def partition3 (pivot : α) : List α → TimeM ℕ (List α × List α × List α)
  | [] => return ([], [], [])
  | x :: xs => do
    ✓ let less := x < pivot
    ✓ let greater := pivot < x
    let rest ← partition3 pivot xs
    if less then
      return (x :: rest.1, rest.2.1, rest.2.2)
    else if greater then
      return (rest.1, rest.2.1, x :: rest.2.2)
    else
      return (rest.1, x :: rest.2.1, rest.2.2)

/-- The three buckets contain exactly the scanned elements. -/
@[simp, grind =]
theorem partition3_length_sum (pivot : α) (xs : List α) :
    (partition3 pivot xs).ret.1.length + (partition3 pivot xs).ret.2.1.length +
        (partition3 pivot xs).ret.2.2.length = xs.length := by
  induction xs with
  | nil => simp [partition3]
  | cons x xs ih =>
    by_cases hlt : x < pivot
      <;> by_cases hgt : pivot < x
      <;> simp [partition3, hlt, hgt, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The low bucket is no longer than the input. -/
theorem partition3_length_left_le (pivot : α) (xs : List α) :
    (partition3 pivot xs).ret.1.length ≤ xs.length := by
  have h := partition3_length_sum pivot xs
  omega

/-- The high bucket is no longer than the input. -/
theorem partition3_length_right_le (pivot : α) (xs : List α) :
    (partition3 pivot xs).ret.2.2.length ≤ xs.length := by
  have h := partition3_length_sum pivot xs
  omega

/-- After removing a pivot, both recursive buckets fit in one less unit of fuel. -/
private theorem partition3_fuel_bounds {fuel : ℕ} {full : List α} (pivot : α)
    (pivotIndex : Fin full.length) (hfuel : full.length ≤ fuel + 1) :
    (partition3 pivot (full.eraseIdx pivotIndex)).ret.1.length ≤ fuel ∧
      (partition3 pivot (full.eraseIdx pivotIndex)).ret.2.2.length ≤ fuel := by
  have hrest : (full.eraseIdx pivotIndex).length < full.length :=
    eraseIdx_length_lt full pivotIndex
  constructor
  · have hleft := partition3_length_left_le pivot (full.eraseIdx pivotIndex)
    omega
  · have hright := partition3_length_right_le pivot (full.eraseIdx pivotIndex)
    omega

/-- A three-way partition performs two order tests for each scanned element. -/
@[simp, grind =]
theorem partition3_time (pivot : α) (xs : List α) :
    (partition3 pivot xs).time = 2 * xs.length := by
  induction xs with
  | nil => simp [partition3]
  | cons x xs ih =>
    by_cases hlt : x < pivot
      <;> by_cases hgt : pivot < x
      <;> simp [partition3, hlt, hgt, ih, Nat.mul_succ]
      <;> omega

/-- Randomized quicksort with explicit recursion fuel. -/
noncomputable def randomizedQuickSortFuel : ℕ → List α → RandomTimeM ℕ (List α)
  | 0, xs => PMF.pure ⟨xs, 0⟩
  | _ + 1, [] => PMF.pure (return [])
  | fuel + 1, x :: xs =>
    let full := x :: xs
    have hxs : 0 < full.length := by simp [full]
    (randomPivotIndex full hxs).bind fun pivotIndex =>
      let pivot := full[pivotIndex]
      let rest := full.eraseIdx pivotIndex
      let parts := partition3 pivot rest
      (randomizedQuickSortFuel fuel parts.ret.1).bind fun sortedLeft =>
        (randomizedQuickSortFuel fuel parts.ret.2.2).bind fun sortedRight =>
          PMF.pure ⟨(sortedLeft.ret ++ (pivot :: parts.ret.2.1)) ++ sortedRight.ret,
            parts.time + sortedLeft.time + sortedRight.time⟩

/-- Sorts a list with duplicate-safe randomized quicksort. -/
noncomputable def randomizedQuickSort (xs : List α) : RandomTimeM ℕ (List α) :=
  randomizedQuickSortFuel xs.length xs

/--
The zero-fuel branch returns the input unchanged. This small support eliminator keeps the recursive
correctness proofs from repeating `PMF.pure` bookkeeping.
-/
private theorem randomizedQuickSortFuel_support_zero {xs : List α} {result : TimeM ℕ (List α)}
    (hresult : result ∈ (randomizedQuickSortFuel 0 xs).support) :
    result = ⟨xs, 0⟩ := by
  simpa [randomizedQuickSortFuel] using hresult

/--
Sorting the empty list has only one possible timed result, regardless of the remaining fuel.
-/
private theorem randomizedQuickSortFuel_support_nil {fuel : ℕ} {result : TimeM ℕ (List α)}
    (hresult : result ∈ (randomizedQuickSortFuel fuel ([] : List α)).support) :
    result = ⟨[], 0⟩ := by
  cases fuel with
  | zero => exact randomizedQuickSortFuel_support_zero hresult
  | succ fuel => simpa [randomizedQuickSortFuel] using hresult

/--
Unpacks one nonempty randomized quicksort step. Every support point comes from a sampled pivot
index, a possible left-recursive run, and a possible right-recursive run.
-/
private theorem randomizedQuickSortFuel_support_cons {fuel : ℕ} {x : α} {xs : List α}
    {result : TimeM ℕ (List α)}
    (hresult : result ∈ (randomizedQuickSortFuel (fuel + 1) (x :: xs)).support) :
    ∃ pivotIndex : Fin (x :: xs).length,
      ∃ sortedLeft ∈
        (randomizedQuickSortFuel fuel
          (partition3 (x :: xs)[pivotIndex] ((x :: xs).eraseIdx pivotIndex)).ret.1).support,
      ∃ sortedRight ∈
        (randomizedQuickSortFuel fuel
          (partition3 (x :: xs)[pivotIndex] ((x :: xs).eraseIdx pivotIndex)).ret.2.2).support,
        result = ⟨(sortedLeft.ret ++ ((x :: xs)[pivotIndex] ::
            (partition3 (x :: xs)[pivotIndex] ((x :: xs).eraseIdx pivotIndex)).ret.2.1)) ++
            sortedRight.ret,
          (partition3 (x :: xs)[pivotIndex] ((x :: xs).eraseIdx pivotIndex)).time +
            sortedLeft.time + sortedRight.time⟩ := by
  simp only [randomizedQuickSortFuel, PMF.mem_support_bind_iff] at hresult
  rcases hresult with ⟨pivotIndex, _, sortedLeft, hleft, sortedRight, hright, hresult⟩
  rw [PMF.mem_support_pure_iff] at hresult
  exact ⟨pivotIndex, sortedLeft, hleft, sortedRight, hright, hresult⟩

section Correctness

/-- Every low-bucket element is below the pivot. -/
@[simp]
theorem lt_pivot_of_mem_partition3_left (pivot : α) (xs : List α) :
    ∀ z ∈ (partition3 pivot xs).ret.1, z < pivot := by
  induction xs with
  | nil => simp [partition3]
  | cons x xs ih =>
    intro z hz
    by_cases hlt : x < pivot
      <;> by_cases hgt : pivot < x
      <;> simp only [partition3, hlt, hgt, ↓reduceIte, ret_bind, ret_pure, List.mem_cons] at hz
      <;> grind

/-- Every middle-bucket element is equal to the pivot. -/
@[simp]
theorem eq_pivot_of_mem_partition3_middle (pivot : α) (xs : List α) :
    ∀ z ∈ (partition3 pivot xs).ret.2.1, z = pivot := by
  induction xs with
  | nil => simp [partition3]
  | cons x xs ih =>
    intro z hz
    by_cases hlt : x < pivot
      <;> by_cases hgt : pivot < x
      <;> simp only [partition3, hlt, hgt, ↓reduceIte, ret_bind, ret_pure, List.mem_cons] at hz
      <;> grind

/-- Every high-bucket element is above the pivot. -/
@[simp]
theorem pivot_lt_of_mem_partition3_right (pivot : α) (xs : List α) :
    ∀ z ∈ (partition3 pivot xs).ret.2.2, pivot < z := by
  induction xs with
  | nil => simp [partition3]
  | cons x xs ih =>
    intro z hz
    by_cases hlt : x < pivot
      <;> by_cases hgt : pivot < x
      <;> simp only [partition3, hlt, hgt, ↓reduceIte, ret_bind, ret_pure, List.mem_cons] at hz
      <;> grind

/-- Partitioning only rearranges elements into the three buckets. -/
@[simp]
theorem partition3_perm (pivot : α) (xs : List α) :
    ((partition3 pivot xs).ret.1 ++ (partition3 pivot xs).ret.2.1 ++
        (partition3 pivot xs).ret.2.2).Perm xs := by
  induction xs with
  | nil => simp [partition3]
  | cons x xs ih =>
    by_cases hlt : x < pivot
    · simpa only [partition3, hlt, ↓reduceIte, ret_bind, ret_pure, List.cons_append] using
        List.Perm.cons x ih
    · by_cases hgt : pivot < x
      · simp only [partition3, hlt, hgt, ↓reduceIte, ret_bind, ret_pure]
        exact (List.perm_middle (a := x)
          (l₁ := (partition3 pivot xs).ret.1 ++ (partition3 pivot xs).ret.2.1)
          (l₂ := (partition3 pivot xs).ret.2.2)).trans (List.Perm.cons x ih)
      · simp only [partition3, hlt, hgt, ↓reduceIte, ret_bind, ret_pure, List.append_assoc]
        simpa [List.append_assoc] using
          (((List.perm_middle (a := x) (l₁ := (partition3 pivot xs).ret.1)
            (l₂ := (partition3 pivot xs).ret.2.1)).append_right
            (partition3 pivot xs).ret.2.2).trans (List.Perm.cons x ih))

/--
If the recursive calls return permutations of the low and high buckets, adding back the pivot and
middle bucket gives a permutation of `pivot :: rest`.
-/
private theorem partition3_recombine_perm (pivot : α) (rest sortedLeft sortedRight : List α)
    (hleft : sortedLeft.Perm (partition3 pivot rest).ret.1)
    (hright : sortedRight.Perm (partition3 pivot rest).ret.2.2) :
    ((sortedLeft ++ (pivot :: (partition3 pivot rest).ret.2.1)) ++ sortedRight).Perm
      (pivot :: rest) := by
  let parts := partition3 pivot rest
  have hparts : (parts.ret.1 ++ parts.ret.2.1 ++ parts.ret.2.2).Perm rest := by
    simpa [parts] using partition3_perm pivot rest
  have hrecursive :
      ((sortedLeft ++ (pivot :: parts.ret.2.1)) ++ sortedRight).Perm
        ((parts.ret.1 ++ (pivot :: parts.ret.2.1)) ++ parts.ret.2.2) :=
    List.Perm.append (List.Perm.append hleft (List.Perm.refl _)) hright
  have hpivot :
      ((parts.ret.1 ++ (pivot :: parts.ret.2.1)) ++ parts.ret.2.2).Perm
        (pivot :: (parts.ret.1 ++ parts.ret.2.1 ++ parts.ret.2.2)) := by
    exact ((List.perm_middle (a := pivot) (l₁ := parts.ret.1)
      (l₂ := parts.ret.2.1)).append_right parts.ret.2.2)
  exact hrecursive.trans (hpivot.trans (List.Perm.cons pivot hparts))

/-- A list whose elements are all the same pivot is sorted. -/
private theorem pairwise_le_of_eq_pivot (pivot : α) (xs : List α) (hxs : ∀ z ∈ xs, z = pivot) :
    List.Pairwise (· ≤ ·) xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    refine List.Pairwise.cons ?_ (ih fun z hz => hxs z (List.mem_cons_of_mem _ hz))
    intro y hy
    rw [hxs x (by simp), hxs y (List.mem_cons_of_mem _ hy)]

/-- The pivot plus the middle bucket consists only of pivot-equal values. -/
private theorem eq_pivot_of_mem_pivot_middle (pivot : α) (xs : List α) :
    ∀ z ∈ pivot :: (partition3 pivot xs).ret.2.1, z = pivot := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · rfl
  · exact eq_pivot_of_mem_partition3_middle pivot xs z hz

/-- The pivot plus the middle bucket is sorted because all its values are equal. -/
private theorem pairwise_pivot_middle (pivot : α) (xs : List α) :
    List.Pairwise (· ≤ ·) (pivot :: (partition3 pivot xs).ret.2.1) := by
  exact pairwise_le_of_eq_pivot pivot (pivot :: (partition3 pivot xs).ret.2.1)
    (eq_pivot_of_mem_pivot_middle pivot xs)

/--
Combines the three sorted quicksort blocks. The low block is below the pivot, the middle block is
all pivot-equal values, and the high block is above the pivot.
-/
private theorem pairwise_three_way_append {pivot : α} {left middle right : List α}
    (hleftSorted : List.Pairwise (· ≤ ·) left)
    (hmiddleSorted : List.Pairwise (· ≤ ·) (pivot :: middle))
    (hrightSorted : List.Pairwise (· ≤ ·) right)
    (hleft : ∀ z ∈ left, z < pivot)
    (hmiddle : ∀ z ∈ pivot :: middle, z = pivot)
    (hright : ∀ z ∈ right, pivot < z) :
    List.Pairwise (· ≤ ·) ((left ++ (pivot :: middle)) ++ right) := by
  rw [List.pairwise_append]
  refine ⟨?_, hrightSorted, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨hleftSorted, hmiddleSorted, ?_⟩
    intro low hlow mid hmid
    rw [hmiddle mid hmid]
    exact le_of_lt (hleft low hlow)
  · intro lowOrMid hblock high hhigh
    rcases List.mem_append.mp hblock with hlow | hmid
    · exact le_trans (le_of_lt (hleft lowOrMid hlow)) (le_of_lt (hright high hhigh))
    · rw [hmiddle lowOrMid hmid]
      exact le_of_lt (hright high hhigh)

/-- Every possible randomized quicksort output is a permutation of its input. -/
theorem randomizedQuickSortFuel_perm (fuel : ℕ) (xs : List α) :
    ∀ result ∈ (randomizedQuickSortFuel fuel xs).support, result.ret.Perm xs := by
  induction fuel generalizing xs with
  | zero =>
    intro result hresult
    simp [randomizedQuickSortFuel_support_zero hresult]
  | succ fuel ih =>
    intro result hresult
    cases xs with
    | nil =>
      simp [randomizedQuickSortFuel_support_nil hresult]
    | cons x xs =>
      rcases randomizedQuickSortFuel_support_cons hresult with
        ⟨pivotIndex, sortedLeft, hleft, sortedRight, hright, rfl⟩
      let full := x :: xs
      let pivot := full[pivotIndex]
      let rest := full.eraseIdx pivotIndex
      let parts := partition3 pivot rest
      have hpermLeft := ih parts.ret.1 sortedLeft hleft
      have hpermRight := ih parts.ret.2.2 sortedRight hright
      have hsplit : (pivot :: rest).Perm full := by
        simpa [pivot, rest] using
          (List.getElem_cons_eraseIdx_perm (l := full) (n := (pivotIndex : ℕ)) pivotIndex.isLt)
      change ((sortedLeft.ret ++ (pivot :: parts.ret.2.1)) ++ sortedRight.ret).Perm full
      have hrecombined :
          ((sortedLeft.ret ++ (pivot :: parts.ret.2.1)) ++ sortedRight.ret).Perm
            (pivot :: rest) := by
        simpa [parts] using
          partition3_recombine_perm pivot rest sortedLeft.ret sortedRight.ret hpermLeft
            hpermRight
      exact hrecombined.trans hsplit

/-- Every possible randomized quicksort output is sorted when the fuel covers the input length. -/
theorem randomizedQuickSortFuel_sorted (fuel : ℕ) (xs : List α) (hfuel : xs.length ≤ fuel) :
    ∀ result ∈ (randomizedQuickSortFuel fuel xs).support, List.Pairwise (· ≤ ·) result.ret := by
  induction fuel generalizing xs with
  | zero =>
    intro result hresult
    cases xs with
    | nil =>
      simp [randomizedQuickSortFuel_support_zero hresult]
    | cons x xs => simp at hfuel
  | succ fuel ih =>
    intro result hresult
    cases xs with
    | nil =>
      simp [randomizedQuickSortFuel_support_nil hresult]
    | cons x xs =>
      rcases randomizedQuickSortFuel_support_cons hresult with
        ⟨pivotIndex, sortedLeft, hleft, sortedRight, hright, rfl⟩
      let full := x :: xs
      let pivot := full[pivotIndex]
      let rest := full.eraseIdx pivotIndex
      let parts := partition3 pivot rest
      change full.length ≤ fuel + 1 at hfuel
      have ⟨hleftFuel, hrightFuel⟩ :
          parts.ret.1.length ≤ fuel ∧ parts.ret.2.2.length ≤ fuel := by
        simpa [parts, rest] using partition3_fuel_bounds pivot pivotIndex hfuel
      have hleftSorted := ih parts.ret.1 hleftFuel sortedLeft hleft
      have hrightSorted := ih parts.ret.2.2 hrightFuel sortedRight hright
      have hpermLeft := randomizedQuickSortFuel_perm fuel parts.ret.1 sortedLeft hleft
      have hpermRight := randomizedQuickSortFuel_perm fuel parts.ret.2.2 sortedRight hright
      have hmiddle : ∀ z ∈ pivot :: parts.ret.2.1, z = pivot := by
        simpa [parts] using eq_pivot_of_mem_pivot_middle pivot rest
      have hmidSorted : List.Pairwise (· ≤ ·) (pivot :: parts.ret.2.1) := by
        simpa [parts] using pairwise_pivot_middle pivot rest
      have hleftAll : ∀ z ∈ sortedLeft.ret, z < pivot :=
        fun z hz => lt_pivot_of_mem_partition3_left pivot rest z (hpermLeft.mem_iff.mp hz)
      have hrightAll : ∀ z ∈ sortedRight.ret, pivot < z :=
        fun z hz => pivot_lt_of_mem_partition3_right pivot rest z (hpermRight.mem_iff.mp hz)
      change List.Pairwise (· ≤ ·) ((sortedLeft.ret ++ (pivot :: parts.ret.2.1)) ++
        sortedRight.ret)
      exact pairwise_three_way_append hleftSorted hmidSorted hrightSorted hleftAll hmiddle hrightAll

/-- Randomized quicksort is functionally correct for every possible run. -/
theorem randomizedQuickSort_correct (xs : List α) :
    ∀ result ∈ (randomizedQuickSort xs).support,
      List.Pairwise (· ≤ ·) result.ret ∧ result.ret.Perm xs := by
  intro result hresult
  exact ⟨randomizedQuickSortFuel_sorted xs.length xs le_rfl result hresult,
    randomizedQuickSortFuel_perm xs.length xs result hresult⟩

end Correctness

section TimeComplexity

/-- Every possible randomized quicksort run obeys a quadratic worst-case comparison bound. -/
theorem randomizedQuickSortFuel_time (fuel : ℕ) (xs : List α) (hfuel : xs.length ≤ fuel) :
    ∀ result ∈ (randomizedQuickSortFuel fuel xs).support,
      result.time ≤ 2 * xs.length * xs.length := by
  induction fuel generalizing xs with
  | zero =>
    intro result hresult
    cases xs with
    | nil =>
      simp [randomizedQuickSortFuel_support_zero hresult]
    | cons x xs => simp at hfuel
  | succ fuel ih =>
    intro result hresult
    cases xs with
    | nil =>
      simp [randomizedQuickSortFuel_support_nil hresult]
    | cons x xs =>
      rcases randomizedQuickSortFuel_support_cons hresult with
        ⟨pivotIndex, sortedLeft, hleft, sortedRight, hright, rfl⟩
      let full := x :: xs
      let pivot := full[pivotIndex]
      let rest := full.eraseIdx pivotIndex
      let parts := partition3 pivot rest
      change full.length ≤ fuel + 1 at hfuel
      have ⟨hleftFuel, hrightFuel⟩ :
          parts.ret.1.length ≤ fuel ∧ parts.ret.2.2.length ≤ fuel := by
        simpa [parts, rest] using partition3_fuel_bounds pivot pivotIndex hfuel
      have ihleft := ih parts.ret.1 hleftFuel sortedLeft hleft
      have ihright := ih parts.ret.2.2 hrightFuel sortedRight hright
      have hsum : parts.ret.1.length + parts.ret.2.1.length + parts.ret.2.2.length =
          rest.length := by
        simp [parts]
      have htime : parts.time = 2 * rest.length := by
        simp [parts]
      change parts.time + sortedLeft.time + sortedRight.time ≤ 2 * full.length * full.length
      calc
        parts.time + sortedLeft.time + sortedRight.time
            ≤ 2 * rest.length + 2 * (rest.length * rest.length) := by
              nlinarith
        _ = 2 * rest.length * (rest.length + 1) := by nlinarith
        _ ≤ 2 * full.length * full.length := by
              have hlen : rest.length + 1 = full.length := by
                simpa [rest] using
                  List.length_eraseIdx_add_one (l := full) (i := (pivotIndex : ℕ))
                    pivotIndex.isLt
              rw [← hlen]
              exact Nat.mul_le_mul_right (rest.length + 1)
                (Nat.mul_le_mul_left 2 (Nat.le_succ rest.length))

/-- Worst-case comparison bound for every possible randomized quicksort run. -/
theorem randomizedQuickSort_time (xs : List α) :
    ∀ result ∈ (randomizedQuickSort xs).support,
      result.time ≤ 2 * xs.length * xs.length := by
  exact randomizedQuickSortFuel_time xs.length xs le_rfl

/--
Expected-time bound for the actual PMF semantics of `randomizedQuickSort`. This follows from the
pointwise worst-case theorem, so it is quadratic rather than the sharper average-case recurrence.
-/
theorem randomizedQuickSort_expectedTime_le_quadratic (xs : List α) :
    RandomTimeM.expectedTime (randomizedQuickSort xs) ≤ (2 * xs.length * xs.length : ℕ) := by
  exact RandomTimeM.expectedTime_le_of_time_le_on_support (randomizedQuickSort_time xs)

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
