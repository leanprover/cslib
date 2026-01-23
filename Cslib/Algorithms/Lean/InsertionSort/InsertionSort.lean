module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Data.Nat.Log

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type} [LinearOrder α]

def insert : α → List α → TimeM (List α)
| x, [] => return [x]
| x, y :: ys => do
  let c ← ✓ (x ≤ y : Bool)
  if c then
    return (x :: y :: ys)
  else
    let rest ← insert x ys
    return (y :: rest)

def insertionSort (xs : List α) : TimeM (List α) := do
  match xs with
  | [] => return []
  | x :: xs' => do
    let sortedTail ← insertionSort xs'
    insert x sortedTail

section Correctness

open List

@[grind →]
theorem mem_either_insert (xs : List α) (a b : α) (hz : a ∈ ⟪insert b xs⟫) : a = b ∨ a ∈ xs := by
  fun_induction insert with
  | case1 _ => simp only [Pure.pure, pure, mem_cons, not_mem_nil, or_false] at hz; exact Or.inl hz
  | case2 x y ys ih =>
    simp_all only [Bind.bind, Pure.pure]
    simp at hz
    grind

/-- A list is sorted if it satisfies the `Pairwise (· ≤ ·)` predicate. -/
abbrev IsSorted (l : List α) : Prop := List.Pairwise (· ≤ ·) l

theorem sorted_insert {x : α} {xs : List α} (hxs : IsSorted xs) :
  IsSorted ⟪insert x xs⟫ := by
  fun_induction insert x xs with
  | case1 _ => simp
  | case2 x y ys ih =>
    simp only [Bind.bind, Pure.pure]
    grind [pairwise_cons]

theorem insertionSort_sorted (xs : List α) : IsSorted ⟪insertionSort xs⟫ := by
  fun_induction insertionSort xs with
  | case1 => simp
  | case2 x xs ih =>
    simp only [Bind.bind]
    grind [sorted_insert]

lemma insert_perm x (xs : List α) : ⟪insert x xs⟫ ~ x :: xs := by
  fun_induction insert with
  | case1 x => simp
  | case2 x y ys ih =>
    simp only [Bind.bind, Pure.pure]
    grind

theorem insertionSort_perm (xs : List α) : ⟪insertionSort xs⟫ ~ xs := by
  fun_induction insertionSort xs with
  | case1 => simp
  | case2 x xs ih =>
    simp only [Bind.bind, ret_bind]
    refine (insert_perm x (insertionSort xs).ret).trans ?_
    grind [List.Perm.cons]

theorem insertionSort_correct (xs : List α) :
    IsSorted ⟪insertionSort xs⟫ ∧ ⟪insertionSort xs⟫ ~ xs :=
  ⟨insertionSort_sorted xs, insertionSort_perm xs⟩

end Correctness

section TimeComplexity

theorem insert_time (x : α) (xs : List α) :
    (insert x xs).time ≤ xs.length := by
  fun_induction insert with
  | case1 _ => simp
  | case2 x y ys ih =>
    simp [Bind.bind, Pure.pure]
    grind

theorem insert_length (x : α) (xs : List α) :
    (insert x xs).ret.length = xs.length + 1 := by
  fun_induction insert with
  | case1 _ => simp
  | case2 x y ys ih =>
    simp [Bind.bind, Pure.pure]
    grind

theorem insertionSort_length (xs : List α) :
    (insertionSort xs).ret.length = xs.length := by
  fun_induction insertionSort xs with
  | case1 => simp
  | case2 x xs ih =>
    simp [Bind.bind]
    grind [insert_length]


theorem insertionSort_time (xs : List α) :
    (insertionSort xs).time ≤ xs.length * xs.length:= by
  fun_induction insertionSort with
  | case1 => simp
  | case2 x xs ih =>
    simp [Bind.bind]
    grind [insert_time, insertionSort_length]

end TimeComplexity

end Cslib.Algorithms.Lean.TimeM
