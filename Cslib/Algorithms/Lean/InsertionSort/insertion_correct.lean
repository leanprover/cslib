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
    exact insert_correct' x ⟪(insertion_sort xs)⟫ ih

inductive Permutation {α : Type} : List α → List α → Prop where
| perm_nil : Permutation [] []
| perm_skip x l l' : Permutation l l' → Permutation (x :: l) (x :: l')
| perm_swap x y l : Permutation (y :: x :: l) (x :: y :: l)
| perm_trans l l₁ l₂ :
  Permutation l l₁ → Permutation l₁ l₂ → Permutation l l₂

attribute [simp] Permutation.perm_nil Permutation.perm_skip Permutation.perm_swap

open Permutation

def permutation {α} (l l' : List α) :=
  ∀ (n : Nat) x, l[n]? = some x → ∃ (n' : Nat), l'[n']? = some x

example : Permutation [1] [1] := by
  aesop

example : Permutation [1,2] [2,1] := by
  aesop

lemma permutation_self {α} : forall (l : List α), Permutation l l := by
  intros l
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    apply perm_skip
    assumption


lemma permutation_insert : ∀ (l : List α) a,
  Permutation (a :: l) (insert a l) := by
  intros l a
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [_root_.insert]
    by_cases h : a <= x
    · simp only [h]
      apply perm_skip
      apply perm_skip
      apply permutation_self
    · simp only [h]
      apply perm_trans (l₁ := x :: a :: xs)
      · apply perm_swap
      apply perm_skip
      assumption

lemma permutation_length {α} : ∀ (l₁ l₂ : List α),
  Permutation l₁ l₂ -> length l₁ = length l₂ := by
  intros l₁ l₂ h
  induction h with
  | perm_nil => simp
  | perm_skip x l1 l2 h ih => simp only [length_cons, Nat.add_right_cancel_iff]; assumption
  | perm_swap x y l => simp
  | perm_trans l l1 l2 h1 h2 ih1 ih2 =>
    rw [ih1, ih2]


lemma permutation_empty {α} : ∀ (l : List α),
  Permutation [] l → l = [] := by
  intros l h
  have hlen : l.length = 0 := by
    apply Eq.symm
    apply permutation_length _ _ h
  -- now finish by cases on `l`
  cases l with
  | nil => rfl
  | cons _ _ =>
    simp [length] at hlen  -- hlen becomes `Nat.succ _ = 0`

lemma permutation_insert' : ∀ (l l' : List α) a,
  Permutation l l' →
  Permutation (a :: l) (insert a l') := by
  intro l l' a h
  induction l with
  | nil =>
    have h1 : l' = [] := by apply permutation_empty _ h
    rw [h1]
    simp
  | cons x xs ih =>
    simp only at *
    apply perm_trans (l₁ := a :: l')
    · apply perm_skip
      assumption
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
