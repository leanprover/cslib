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

theorem insertion_sort_correct : ∀ (l : List α),
  IsSorted (⟪insertion_sort l⟫) := by
  intro l
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
  (a :: l) ~ ⟪insert a l'⟫ := by
  intro l l' a h
  cases l with
  | nil =>
    have h1 : [].isEmpty = l'.isEmpty := Perm.isEmpty_eq h
    simp only [isEmpty_nil, Bool.true_eq, List.isEmpty_iff] at h1
    rw [h1]
    simp
  | cons a' l =>
    apply Perm.trans (l₂ := a :: l')
    · simp only [perm_cons]
      assumption
    apply Perm.symm
    apply permutation_insert

theorem sorted_correct : ∀ (l : List α),
  ∃ l', Sorted l' ∧ Permutation l l' := by
  intro l
  exists (insertion_sort l)
  apply And.intro
  · apply insertion_sort_correct
  · induction l with
    | nil => simp [insertion_sort]
    | cons x xs ih =>
      simp only [insertion_sort]
      apply permutation_insert'
      assumption
