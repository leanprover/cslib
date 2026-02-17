import Mathlib.Order.Basic
import Mathlib.Tactic.Order
import Aesop

import Cslib.Algorithms.Lean.TimeM

namespace Cslib.Algorithms.Lean.TimeM

open List

variable {α : Type} [LinearOrder α]

@[simp]
def insert (a : α) (l : List α) : TimeM (List α) :=
  match l with
  | nil => return [a]
  | x :: xs => do
    ✓ let c := (a ≤ x : Bool)
    if c then
      return a :: (x :: xs)
    else
      let rest ← insert a xs
      return x :: rest


#eval (insert 4 [1, 3, 5, 6])

def insertion_sort (l : List α) : TimeM (List α):=
  match l with
  | nil => return nil
  | x :: xs => do
    let rest ← insertion_sort xs
    insert x rest

#eval (insertion_sort [4,3,2,6, 7, 1, 10])
#eval (insertion_sort [1, 2, 3, 4])
#eval (insertion_sort [4, 3, 2, 1])

abbrev IsSorted (l : List α) : Prop := List.Pairwise (· ≤ ·) l

@[grind →]
lemma mem_either_insert (l : List α) (h : x ∈ ⟪insert y l⟫) :  x = y ∨ x ∈ l := by
  fun_induction insert with
  | case1 => grind
  | case2 z l ih =>
    by_cases h1 : y ≤ z
    · simp [decide_eq_true_eq] at h
      grind
    · simp only [decide_eq_true_eq, bind_pure_comp, ret_bind] at h
      grind


lemma insert_correct : ∀ a (l : List α) (_ : IsSorted l), IsSorted (⟪insert a l⟫) := by
  intros a l h
  fun_induction insert a l with
  | case1 => simp
  | case2 x l ih =>
    simp only [decide_eq_true_eq, bind_pure_comp, ret_bind]
    split_ifs with h1
    · grind
    · simp only [pairwise_cons] at h
      simp only [IsSorted] at ih
      rcases h with ⟨ ha, hb ⟩
      simp only [ret_map, pairwise_cons]
      apply And.intro
      · intros a' h2
        have h3 := mem_either_insert _ h2
        grind
      · grind

theorem insertionSort_sorted (l : List α) :
  IsSorted (⟪insertion_sort l⟫) := by
  induction l with
  | nil =>
    simp only [insertion_sort, ret_pure, Pairwise.nil]
  | cons x xs ih =>
    simp only [insertion_sort, ret_bind]
    exact insert_correct x ⟪(insertion_sort xs)⟫ ih


lemma permutation_insert : ∀ (l : List α) a,
  ⟪insert a l⟫ ~ (a :: l) := by
  intros l a
  fun_induction insert with
  | case1 => simp only [ret_pure, Perm.refl]
  | case2 b l' ih =>
    simp
    split_ifs with h1
    · simp
    · simp
      grind

lemma permutation_insert' : ∀ (l l' : List α) a,
  l ~ l' →
  ⟪insert a l⟫ ~ a :: l' := by
  intro l l' a h
  cases l' with
  | nil =>
    have h1 : l.isEmpty = [].isEmpty := Perm.isEmpty_eq h
    simp only [isEmpty_nil, List.isEmpty_iff] at h1
    rw [h1]
    simp
  | cons a' l' =>
    apply Perm.symm
    apply Perm.trans (l₂ := a :: l)
    · simp only [perm_cons]
      apply Perm.symm
      assumption
    apply Perm.symm
    apply permutation_insert

lemma insertionSort_perm (l : List α) : ⟪insertion_sort l⟫ ~ l := by
  fun_induction insertion_sort with
  | case1 => simp
  | case2 a l ih =>
    simp only [ret_bind]
    apply permutation_insert'
    assumption

theorem insertionSort_correct (l : List α) :
  IsSorted (⟪insertion_sort l⟫) ∧ ⟪insertion_sort l⟫ ~ l :=
    ⟨ insertionSort_sorted l, insertionSort_perm l⟩

lemma insert_time (l : List α) :
  (insert a l).time ≤ l.length := by
  fun_induction insert with
  | case1 => simp
  | case2 b l ih =>
    simp at *
    split_ifs with h1
    · simp
    · grind

lemma insertion_sort_len (l : List α) :
  ⟪insertion_sort l⟫.length = l.length := by
  have h := insertionSort_perm l
  apply Perm.length_eq at h
  exact h

theorem insertionSort_time (l : List α) :
  let n := l.length
  (insertion_sort l).time ≤ n^2 := by
  fun_induction insertion_sort with
  | case1 => simp
  | case2 a l ih =>
    simp only [time_bind, length_cons] at *
    have h : (insert a ⟪insertion_sort l⟫).time ≤ ⟪insertion_sort l⟫.length := by
      apply insert_time
    rw [insertion_sort_len] at h
    grind
