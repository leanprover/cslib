/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Cslib.Algorithms.Lean.Sort.Merge
import all Cslib.Algorithms.Lean.Sort.Merge
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Nat.Log

/-!
# MergeSort on a list

In this file we introduce `merge` and `mergeSort` algorithms that returns a time monad
over the list `TimeM ℕ (List α)`. The time complexity of `mergeSort` is the number of comparisons.

--
## Main results

- `mergeSort_correct`: `mergeSort` permutes the list into a sorted one.
- `mergeSortM_stable`: `List.mergeSortM` is stable for any total and transitive comparator.
- `mergeSortBy_stable`: Key-based `mergeSortBy` preserves the relative order of equal-key elements.
- `mergeSort_time`: The number of comparisons of `mergeSort` is at most `n*⌈log₂ n⌉`.

-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type}

open List in
/-- `TimeM.ret` passes through `List.mergeM` into the comparator. -/
@[simp, grind =]
theorem ret_mergeM {T} [AddMonoid T] (xs ys : List α) (le : α → α → TimeM T Bool) :
    ⟪List.mergeM xs ys le⟫ = List.merge xs ys (fun x y => ⟪le x y⟫) := by
  simpa using Id.ext_iff.1 <| isMonadHom_pure_ret.map_listMergeM xs ys le

open List in
/-- `TimeM.ret` passes through `List.mergeSortM` into the comparator. -/
@[simp]
theorem ret_mergeSortM {T} [AddMonoid T] (xs : List α) (le : α → α → TimeM T Bool) :
    ⟪List.mergeSortM xs le⟫ = List.mergeSort xs (fun x y => ⟪le x y⟫) := by
  simpa using Id.ext_iff.1 <| isMonadHom_pure_ret.map_listMergeSortM xs le

section GeneralStability

/-- Filtering the result of `List.mergeM` in `TimeM` by a predicate `p` whose satisfying elements
are pairwise related by the underlying comparator distributes over `++`. -/
theorem filter_ret_mergeM {T : Type} [AddMonoid T] {le : α → α → TimeM T Bool}
    [IsTrans α (fun x y => ⟪le x y⟫ = true)] {p : α → Bool} {xs ys : List α}
    (hxs : xs.Pairwise (fun x y => ⟪le x y⟫ = true))
    (hp : ∀ ⦃x y⦄, p x = true → p y = true → ⟪le x y⟫ = true) :
    ⟪List.mergeM xs ys le⟫.filter p = xs.filter p ++ ys.filter p := by
  simpa only [ret_mergeM] using List.filter_merge hxs hp

/-- Stability of `List.mergeM` in `TimeM` on equivalence classes for any transitive timed
comparator `le` and sorted left input `xs`. -/
theorem ret_mergeM_stable {T : Type} [AddMonoid T] {le : α → α → TimeM T Bool}
    [IsTrans α (fun x y => ⟪le x y⟫ = true)] {xs ys : List α}
    (hxs : xs.Pairwise (fun x y => ⟪le x y⟫ = true)) (k : α) :
    ⟪List.mergeM xs ys le⟫.filter (fun x => ⟪le x k⟫ && ⟪le k x⟫) =
      xs.filter (fun x => ⟪le x k⟫ && ⟪le k x⟫) ++
        ys.filter (fun x => ⟪le x k⟫ && ⟪le k x⟫) := by
  simpa only [ret_mergeM] using List.filter_merge_eqv hxs k

/-- Filtering the result of `List.mergeSortM` in `TimeM` by a predicate `p` whose satisfying
elements are pairwise related by the underlying comparator preserves `xs.filter p`. -/
theorem filter_ret_mergeSortM {T : Type} [AddMonoid T] (xs : List α)
    (le : α → α → TimeM T Bool) [Std.Total (fun x y => ⟪le x y⟫ = true)]
    [IsTrans α (fun x y => ⟪le x y⟫ = true)] {p : α → Bool}
    (hp : ∀ ⦃x y⦄, p x = true → p y = true → ⟪le x y⟫ = true) :
    ⟪List.mergeSortM xs le⟫.filter p = xs.filter p := by
  simpa only [ret_mergeSortM] using List.filter_mergeSort xs (fun x y => ⟪le x y⟫) hp

/-- `List.mergeSortM` in `TimeM` is stable for any total and transitive timed comparator `le`. -/
theorem ret_mergeSortM_stable {T : Type} [AddMonoid T] (xs : List α)
    (le : α → α → TimeM T Bool) [Std.Total (fun x y => ⟪le x y⟫ = true)]
    [IsTrans α (fun x y => ⟪le x y⟫ = true)] (k : α) :
    ⟪List.mergeSortM xs le⟫.filter (fun x => ⟪le x k⟫ && ⟪le k x⟫) =
      xs.filter (fun x => ⟪le x k⟫ && ⟪le k x⟫) := by
  simpa only [ret_mergeSortM] using List.mergeSort_stable xs (fun x y => ⟪le x y⟫) k

/-- Stability of `List.mergeM` with unit-cost comparisons `fun x y => do ✓ return le x y`. -/
theorem mergeM_stable {le : α → α → Bool} [IsTrans α (fun x y => le x y = true)]
    {xs ys : List α} (hxs : xs.Pairwise (fun x y => le x y = true)) (k : α) :
    (⟪List.mergeM xs ys (fun x y => do ✓ return le x y)⟫).filter
      (fun x => le x k && le k x) =
      xs.filter (fun x => le x k && le k x) ++ ys.filter (fun x => le x k && le k x) := by
  simpa using List.filter_merge_eqv hxs k

/-- `List.mergeSortM` with unit-cost comparisons is stable for any total and transitive comparator
`le`. -/
theorem mergeSortM_stable (xs : List α) (le : α → α → Bool)
    [Std.Total (fun x y => le x y = true)] [IsTrans α (fun x y => le x y = true)] (k : α) :
    (⟪List.mergeSortM xs (fun x y => do ✓ return le x y)⟫).filter
      (fun x => le x k && le k x) =
      xs.filter (fun x => le x k && le k x) := by
  simpa using List.mergeSort_stable xs le k

end GeneralStability

variable [LinearOrder α]

/-- Merges two lists into a single list, counting comparisons as time cost.
Returns a `TimeM ℕ (List α)` where the time represents the number of comparisons performed. -/
abbrev merge (xs ys : List α) : TimeM ℕ (List α) :=
  List.mergeM xs ys fun x y => do ✓ return x ≤ y

/-- Sorts a list using the merge sort algorithm, counting comparisons as time cost.
Returns a `TimeM ℕ (List α)` where the time represents the total number of comparisons. -/
abbrev mergeSort (xs : List α) : TimeM ℕ (List α) :=
  List.mergeSortM xs fun x y => do ✓ return x ≤ y

/-- Merges two lists of elements of `β` ordered by a key projection `key : β → α`,
counting key comparisons as time cost. -/
abbrev mergeBy {β : Type} (key : β → α) (xs ys : List β) : TimeM ℕ (List β) :=
  List.mergeM xs ys fun x y => do ✓ return decide (key x ≤ key y)

/-- Sorts a list of elements of `β` by a key projection `key : β → α` using merge sort,
counting key comparisons as time cost. -/
abbrev mergeSortBy {β : Type} (key : β → α) (xs : List β) : TimeM ℕ (List β) :=
  List.mergeSortM xs fun x y => do ✓ return decide (key x ≤ key y)

section Correctness

open List

/-- Our merge computes the one already in mathlib. -/
theorem ret_merge (xs ys : List α) : ⟪merge xs ys⟫ = xs.merge ys := by
  simp

/-- A list is sorted if it satisfies the `Pairwise (· ≤ ·)` predicate. -/
abbrev IsSorted (l : List α) : Prop := List.Pairwise (· ≤ ·) l

/-- `x` is a minimum element of list `l` if `x ≤ b` for all `b ∈ l`. -/
abbrev MinOfList (x : α) (l : List α) : Prop := ∀ b ∈ l, x ≤ b

@[grind →]
theorem mem_either_merge (xs ys : List α) (z : α) (hz : z ∈ ⟪merge xs ys⟫) : z ∈ xs ∨ z ∈ ys := by
  grind [List.mem_merge]

theorem min_all_merge (x : α) (xs ys : List α) (hxs : MinOfList x xs) (hys : MinOfList x ys) :
    MinOfList x ⟪merge xs ys⟫ := by
  grind

theorem sorted_merge {l1 l2 : List α} (hxs : IsSorted l1) (hys : IsSorted l2) :
    IsSorted ⟪merge l1 l2⟫ := by
  grind [hxs.merge hys]

theorem mergeSort_sorted (xs : List α) : IsSorted ⟪mergeSort xs⟫ := by
  simpa using List.pairwise_mergeSort' _ xs

lemma merge_perm (l₁ l₂ : List α) : ⟪merge l₁ l₂⟫ ~ l₁ ++ l₂ := by
  simpa using List.merge_perm_append _

theorem mergeSort_perm (xs : List α) : ⟪mergeSort xs⟫ ~ xs := by
  simpa using List.mergeSort_perm _ _

/-- MergeSort is functionally correct. -/
theorem mergeSort_correct (xs : List α) : IsSorted ⟪mergeSort xs⟫ ∧ ⟪mergeSort xs⟫ ~ xs :=
  ⟨mergeSort_sorted xs, mergeSort_perm xs⟩

/-- `merge` sums the occurrence counts of every element across both input lists. -/
theorem merge_count (xs ys : List α) (k : α) :
    ⟪merge xs ys⟫.count k = xs.count k + ys.count k := by
  rw [(merge_perm xs ys).count_eq, List.count_append]

/-- `mergeSort` preserves the occurrence count of every element. -/
theorem mergeSort_count (xs : List α) (k : α) :
    ⟪mergeSort xs⟫.count k = xs.count k :=
  (mergeSort_perm xs).count_eq k

/-- Filtering `⟪merge xs ys⟫` by a predicate whose satisfying elements are pairwise `≤`
distributes over `++` when `xs` is sorted. -/
theorem merge_filter_of_le {xs ys : List α} (hxs : IsSorted xs) {p : α → Bool}
    (hp : ∀ ⦃x y⦄, p x = true → p y = true → x ≤ y) :
    ⟪merge xs ys⟫.filter p = xs.filter p ++ ys.filter p := by
  simpa only [ret_merge] using List.filter_merge' hxs hp

/-- Filtering `⟪merge xs ys⟫` by a predicate selecting at most one value distributes over `++`
when `xs` is sorted. -/
theorem merge_filter_eq_of_eq {xs ys : List α} (hxs : IsSorted xs) {p : α → Bool}
    (hp : ∀ ⦃x y⦄, p x = true → p y = true → x = y) :
    ⟪merge xs ys⟫.filter p = xs.filter p ++ ys.filter p :=
  merge_filter_of_le hxs fun _ _ hx hy => (hp hx hy).le

/-- Filtering `⟪merge xs ys⟫` for elements equal to `k` distributes over `++` when `xs` is
sorted. -/
theorem merge_filter_eq {xs ys : List α} (hxs : IsSorted xs) (k : α) :
    ⟪merge xs ys⟫.filter (fun x => decide (x = k)) =
      xs.filter (fun x => decide (x = k)) ++ ys.filter (fun x => decide (x = k)) :=
  merge_filter_eq_of_eq hxs fun _ _ hx hy => by
    simp only [decide_eq_true_eq] at hx hy
    exact hx.trans hy.symm

/-- Filtering `⟪merge xs ys⟫` by `(· == k)` distributes over `++` when `xs` is sorted. -/
theorem merge_filter_beq [BEq α] [LawfulBEq α] {xs ys : List α} (hxs : IsSorted xs) (k : α) :
    ⟪merge xs ys⟫.filter (· == k) = xs.filter (· == k) ++ ys.filter (· == k) :=
  merge_filter_eq_of_eq hxs fun _ _ hx hy => by
    simp only [beq_iff_eq] at hx hy
    exact hx.trans hy.symm

/-- Filtering `⟪mergeSort xs⟫` by any predicate `p` selecting at most one value preserves
`xs.filter p`. -/
theorem mergeSort_filter_eq_of_eq (xs : List α) {p : α → Bool}
    (hp : ∀ ⦃x y⦄, p x = true → p y = true → x = y) :
    ⟪mergeSort xs⟫.filter p = xs.filter p := by
  simpa using List.filter_mergeSort' xs (· ≤ ·) fun _ _ hx hy => (hp hx hy).le

/-- Filtering `⟪mergeSort xs⟫` for elements equal to `k` agrees with `xs.filter`. -/
theorem mergeSort_filter_eq (xs : List α) (k : α) :
    ⟪mergeSort xs⟫.filter (fun x => decide (x = k)) =
      xs.filter (fun x => decide (x = k)) :=
  mergeSort_filter_eq_of_eq xs fun _ _ hx hy => by
    simp only [decide_eq_true_eq] at hx hy
    exact hx.trans hy.symm

/-- Filtering `⟪mergeSort xs⟫` by `(· == k)` agrees with `xs.filter (· == k)`. -/
theorem mergeSort_filter_beq [BEq α] [LawfulBEq α] (xs : List α) (k : α) :
    ⟪mergeSort xs⟫.filter (· == k) = xs.filter (· == k) :=
  mergeSort_filter_eq_of_eq xs fun _ _ hx hy => by
    simp only [beq_iff_eq] at hx hy
    exact hx.trans hy.symm

/-- `TimeM.ret` of `mergeBy` agrees with `List.merge` comparing keys. -/
theorem ret_mergeBy {β : Type} (key : β → α) (xs ys : List β) :
    ⟪mergeBy key xs ys⟫ = xs.merge ys (fun x y => decide (key x ≤ key y)) := by
  simp

/-- `TimeM.ret` of `mergeSortBy` agrees with `List.mergeSort` comparing keys. -/
theorem ret_mergeSortBy {β : Type} (key : β → α) (xs : List β) :
    ⟪mergeSortBy key xs⟫ = xs.mergeSort (fun x y => decide (key x ≤ key y)) := by
  simp

/-- `mergeSortBy` returns a permutation of the input list. -/
theorem mergeSortBy_perm {β : Type} (key : β → α) (xs : List β) :
    ⟪mergeSortBy key xs⟫ ~ xs := by
  simpa using List.mergeSort_perm xs (fun x y => decide (key x ≤ key y))

/-- `mergeSortBy` produces a list sorted with respect to `key`. -/
theorem mergeSortBy_sorted {β : Type} (key : β → α) (xs : List β) :
    List.Pairwise (fun x y => key x ≤ key y) ⟪mergeSortBy key xs⟫ := by
  have : IsTrans β (fun x y => key x ≤ key y) := ⟨fun _ _ _ => le_trans⟩
  have : Std.Total (fun x y => key x ≤ key y) := ⟨fun x y => le_total (key x) (key y)⟩
  simpa using List.pairwise_mergeSort' (fun x y => key x ≤ key y) xs

/-- Mapping `key` over `⟪mergeSortBy key xs⟫` agrees with `⟪mergeSort (xs.map key)⟫`. -/
theorem map_key_mergeSortBy {β : Type} (key : β → α) (xs : List β) :
    ⟪mergeSortBy key xs⟫.map key = ⟪mergeSort (xs.map key)⟫ := by
  simpa using List.map_mergeSort (r := fun x y => decide (key x ≤ key y))
    (s := fun x y => decide (x ≤ y)) (f := key) (l := xs) (fun _ _ _ _ => rfl)

/-- Stability of `mergeBy` for predicates whose satisfying elements satisfy `key x ≤ key y`. -/
theorem mergeBy_filter_of_key_le {β : Type} (key : β → α) {xs ys : List β}
    (hxs : List.Pairwise (fun x y => key x ≤ key y) xs) {p : β → Bool}
    (hp : ∀ ⦃x y⦄, p x = true → p y = true → key x ≤ key y) :
    ⟪mergeBy key xs ys⟫.filter p = xs.filter p ++ ys.filter p := by
  have : IsTrans β (fun x y => key x ≤ key y) := ⟨fun _ _ _ => le_trans⟩
  simpa using List.filter_merge' (r := fun x y => key x ≤ key y) hxs hp

/-- Key-based stability of `mergeBy`: elements with `key x = k` preserve their relative order
from `xs` followed by `ys`. -/
theorem mergeBy_stable {β : Type} (key : β → α) {xs ys : List β}
    (hxs : List.Pairwise (fun x y => key x ≤ key y) xs) (k : α) :
    ⟪mergeBy key xs ys⟫.filter (fun x => decide (key x = k)) =
      xs.filter (fun x => decide (key x = k)) ++
        ys.filter (fun x => decide (key x = k)) :=
  mergeBy_filter_of_key_le key hxs fun _ _ hx hy => by
    simp only [decide_eq_true_eq] at hx hy
    exact (hx.trans hy.symm).le

/-- Filtering `⟪mergeSortBy key xs⟫` by any predicate whose satisfying elements share the same
key preserves `xs.filter p`. -/
theorem mergeSortBy_filter_eq_of_key_eq {β : Type} (key : β → α) (xs : List β)
    {p : β → Bool} (hp : ∀ ⦃x y⦄, p x = true → p y = true → key x = key y) :
    ⟪mergeSortBy key xs⟫.filter p = xs.filter p := by
  have : IsTrans β (fun x y => key x ≤ key y) := ⟨fun _ _ _ => le_trans⟩
  have : Std.Total (fun x y => key x ≤ key y) := ⟨fun x y => le_total (key x) (key y)⟩
  simpa using List.filter_mergeSort' xs (fun x y => key x ≤ key y)
    fun _ _ hx hy => (hp hx hy).le

/-- Key-based stability of `mergeSortBy`: elements with key equal to `k` appear in
`⟪mergeSortBy key xs⟫` in the exact same relative order as in `xs`. -/
theorem mergeSortBy_stable {β : Type} (key : β → α) (xs : List β) (k : α) :
    ⟪mergeSortBy key xs⟫.filter (fun x => decide (key x = k)) =
      xs.filter (fun x => decide (key x = k)) :=
  mergeSortBy_filter_eq_of_key_eq key xs fun _ _ hx hy => by
    simp only [decide_eq_true_eq] at hx hy
    exact hx.trans hy.symm

/-- Key-based stability of `mergeSortBy` stated with `BEq` on keys. -/
theorem mergeSortBy_filter_beq {β : Type} [BEq α] [LawfulBEq α] (key : β → α)
    (xs : List β) (k : α) :
    ⟪mergeSortBy key xs⟫.filter (fun x => key x == k) =
      xs.filter (fun x => key x == k) :=
  mergeSortBy_filter_eq_of_key_eq key xs fun _ _ hx hy => by
    simp only [beq_iff_eq] at hx hy
    exact hx.trans hy.symm

end Correctness

section TimeComplexity

/-- Recurrence relation for the time complexity of merge sort.
For a list of length `n`, this counts the total number of comparisons:
- Base cases: 0 comparisons for lists of length 0 or 1
- Recursive case: split the list, sort both halves,
  then merge (which takes at most `n` comparisons) -/
def timeMergeSortRec : ℕ → ℕ
| 0 => 0
| 1 => 0
| n@(_+2) => timeMergeSortRec (n/2) + timeMergeSortRec ((n-1)/2 + 1) + n

open Nat (clog)

/-- Key Lemma: ⌈log2 ⌈n/2⌉⌉ ≤ ⌈log2 n⌉ - 1 -/
@[grind .]
lemma clog2_half_le (n : ℕ) : clog 2 ((n + 1) / 2) ≤ clog 2 n - 1 := by
  rcases n with _ | _ | n
  · simp
  · simp
  · grind [Nat.clog_of_one_lt one_lt_two (by omega : 1 < n + 2)]

/-- Same logic for the floor half: ⌈log2 ⌊n/2⌋⌉ ≤ ⌈log2 n⌉ - 1 -/
@[grind .]
lemma clog2_floor_half_le (n : ℕ) : clog 2 (n / 2) ≤ clog 2 n - 1 := by
  apply Nat.le_trans _ (clog2_half_le n)
  apply Nat.clog_monotone
  grind

private lemma some_algebra (n : ℕ) :
    (n / 2 + 1) * clog 2 (n / 2 + 1) + ((n + 1) / 2 + 1) * clog 2 ((n + 1) / 2 + 1) + (n + 2) ≤
    (n + 2) * clog 2 (n + 2) := by
  -- 1. Substitution: Let N = n_1 + 2 to clean up the expression
  let N := n + 2
  have hN : 2 ≤ N := by omega
  -- 2. Rewrite the terms using N
  have t1 : n / 2 + 1 = N / 2 := by omega
  have t2 : (n + 1) / 2 + 1 = (N + 1) / 2 := by omega
  have t3 : n + 1 + 1 = N := by omega
  let k := clog 2 N
  have h_bound_l : clog 2 (N / 2) ≤ k - 1 := clog2_floor_half_le N
  have h_bound_r : clog 2 ((N + 1) / 2) ≤ k - 1 := clog2_half_le N
  have h_split : N / 2 + (N + 1) / 2 = N := by omega
  grw [t1, t2, t3, h_bound_l, h_bound_r, ←Nat.add_mul, h_split]
  exact Nat.le_refl (N * (k - 1) + N)

/-- Upper bound function for merge sort time complexity: `T(n) = n * ⌈log₂ n⌉` -/
abbrev T (n : ℕ) : ℕ := n * clog 2 n

/-- Solve the recurrence -/
theorem timeMergeSortRec_le (n : ℕ) : timeMergeSortRec n ≤ T n := by
  fun_induction timeMergeSortRec with
  | case1 => grind
  | case2 => grind
  | case3 n ih2 ih1 =>
    grw [ih1,ih2]
    have := some_algebra n
    grind [Nat.add_div_right]

theorem merge_ret_length_eq_sum (xs ys : List α) :
    ⟪merge xs ys⟫.length = xs.length + ys.length := by
  simp

theorem mergeSort_same_length (xs : List α) :
    ⟪mergeSort xs⟫.length = xs.length := by
  simp

@[simp] theorem merge_time (xs ys : List α) : (merge xs ys).time ≤ xs.length + ys.length := by
  unfold merge
  fun_induction List.mergeM with grind

theorem mergeSort_time_le (xs : List α) :
    (mergeSort xs).time ≤ timeMergeSortRec xs.length := by
  unfold mergeSort
  fun_induction List.mergeSortM with
  | case1 | case2 =>
    grind
  | case3 _ _ _ _ ih2 ih1 =>
    simp only [time_bind]
    grw [merge_time]
    simp only [mergeSort_same_length]
    unfold timeMergeSortRec
    grind

/-- Time complexity of mergeSort -/
theorem mergeSort_time (xs : List α) :
    let n := xs.length
    (mergeSort xs).time ≤ n * clog 2 n := by
  grind [mergeSort_time_le, timeMergeSortRec_le]

theorem mergeSortBy_same_length {β : Type} (key : β → α) (xs : List β) :
    ⟪mergeSortBy key xs⟫.length = xs.length := by
  simp

@[simp] theorem mergeBy_time {β : Type} (key : β → α) (xs ys : List β) :
    (mergeBy key xs ys).time ≤ xs.length + ys.length := by
  unfold mergeBy
  fun_induction List.mergeM with grind

theorem mergeSortBy_time_le {β : Type} (key : β → α) (xs : List β) :
    (mergeSortBy key xs).time ≤ timeMergeSortRec xs.length := by
  unfold mergeSortBy
  fun_induction List.mergeSortM with
  | case1 | case2 =>
    grind
  | case3 _ _ _ _ ih2 ih1 =>
    simp only [time_bind]
    grw [mergeBy_time]
    simp only [mergeSortBy_same_length]
    unfold timeMergeSortRec
    grind

/-- Time complexity of `mergeSortBy`: at most `n * ⌈log₂ n⌉` key comparisons. -/
theorem mergeSortBy_time {β : Type} (key : β → α) (xs : List β) :
    let n := xs.length
    (mergeSortBy key xs).time ≤ n * clog 2 n :=
  (mergeSortBy_time_le key xs).trans (timeMergeSortRec_le xs.length)

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
