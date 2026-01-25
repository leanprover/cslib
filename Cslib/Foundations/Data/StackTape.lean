/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# StackTape: Infinite, eventually-`none` lists of `Option`s

This file defines `StackTape`, a list of `Option` values where the list cannot end with `none`.
This represents a stack-like data structure
which treats the end of the list as an infinite sequence of `none` values.
This is useful as a data structure with a simple API for manipulation by Turing machines .

## TODO

- Make a `::`-like notation.

-/

namespace Turing

/--
List of `Option` values that don't end with `none`
-/
structure StackTape (α : Type) where
  (toList : List (Option α))
  -- The list can be empty (i.e. `none`),
  -- but if it is not empty, the last element is not (`some`) `none`
  (toList_getLast?_ne_some_none : toList.getLast? ≠ some none)

/-- The empty `StackTape` -/
def StackTape.empty {α} : StackTape α := ⟨[], by simp⟩

/-- Create a `StackTape` from a list by mapping all elements to `some` -/
def StackTape.map_some {α} (l : List α) : StackTape α := ⟨l.map some, by simp⟩

instance {α : Type} : Inhabited (StackTape α) where
  default := StackTape.empty

/-- The length of the `StackTape` is the number of elements up to the last non-`none` element -/
def StackTape.length {α} (l : StackTape α) : ℕ := l.toList.length

/-- Prepend an `Option` to the `StackTape` -/
def StackTape.cons {α} (x : Option α) (xs : StackTape α) : StackTape α :=
  match x, xs with
  | none, ⟨[], _⟩ => ⟨[], by simp⟩
  | none, ⟨hd :: tl, hl⟩ => ⟨none :: hd :: tl, by simp only [List.getLast?_cons_cons]; exact hl⟩
  | some a, ⟨l, hl⟩ => ⟨some a :: l, by
      cases hl' : l with
      | nil => simp
      | cons hd tl =>
        simp only [List.getLast?_cons_cons]
        exact ne_of_eq_of_ne (congrArg List.getLast? (id (Eq.symm hl'))) hl⟩

/-- Remove the first element of the `StackTape`, returning the rest -/
def StackTape.tail {α} (l : StackTape α) : StackTape α :=
  match hl : l.toList with
  | [] => StackTape.empty
  | hd :: t => ⟨t, by
      match t with
      | [] => simp
      | hd' :: t' =>
        have lh := l.toList_getLast?_ne_some_none
        rw [hl] at lh
        simp only [List.getLast?_cons_cons] at lh
        have := l.toList_getLast?_ne_some_none
        rw [hl, List.getLast?_cons_cons] at this
        exact this⟩

/-- Get the first element of the `StackTape`. -/
def StackTape.head {α} (l : StackTape α) : Option α :=
  match l.toList with
  | [] => none
  | h :: _ => h

lemma StackTape.eq_iff {α} (l1 l2 : StackTape α) :
    l1 = l2 ↔ l1.head = l2.head ∧ l1.tail = l2.tail := by
  constructor
  · intro h
    rw [h]
    simp
  · intro ⟨hhead, htail⟩
    cases l1 with | mk as1 h1 =>
    cases l2 with | mk as2 h2 =>
    simp only [mk.injEq]
    cases as1 with
    | nil =>
      cases as2 with
      | nil => rfl
      | cons hd2 tl2 =>
        simp only [head] at hhead
        simp only [tail, empty, mk.injEq] at htail
        subst htail hhead
        simp at h2
    | cons hd1 tl1 =>
      cases as2 with
      | nil =>
        simp only [head] at hhead
        simp only [tail, empty, mk.injEq] at htail
        subst htail hhead
        simp at h1
      | cons hd2 tl2 =>
        simp only [head] at hhead
        simp only [tail, mk.injEq] at htail
        rw [hhead, htail]

@[simp]
lemma StackTape.head_cons {α} (o : Option α) (l : StackTape α) :
    (StackTape.cons o l).head = o := by
  cases o with
  | none =>
    cases l with | mk toList hl =>
    cases toList with
    | nil => simp [cons, head]
    | cons hd tl => simp [cons, head]
  | some a => simp [cons, head]

@[simp]
lemma StackTape.tail_cons {α} (o : Option α) (l : StackTape α) :
    (StackTape.cons o l).tail = l := by
  cases o with
  | none =>
    cases l with | mk toList h =>
    cases toList with
    | nil => simp [cons, tail, empty]
    | cons hd tl => simp [cons, tail]
  | some a =>
    simp only [cons]
    unfold tail
    simp only

@[simp]
lemma StackTape.cons_head_tail {α} (l : StackTape α) :
    StackTape.cons (l.head) (l.tail) = l := by
  cases l with | mk toList h =>
  cases toList with
  | nil => simp [head, tail, cons, empty]
  | cons hd tl =>
    simp only [head, tail]
    cases hd with
    | none =>
      cases tl with
      | nil => simp at h
      | cons hd' tl' => simp [cons]
    | some a =>
      simp only [cons]

lemma StackTape.length_tail_le {α} (l : StackTape α) : l.tail.length ≤ l.length := by
  unfold tail length
  split
  · simp [empty]
  · next heq => simp [heq]

lemma StackTape.length_cons_none {α} (l : StackTape α) :
    (StackTape.cons none l).length = l.length + if l.length = 0 then 0 else 1 := by
  cases l with | mk toList h =>
  cases toList with
  | nil => simp [cons, length]
  | cons hd tl => simp [cons, length]

lemma StackTape.length_cons_some {α} (a : α) (l : StackTape α) :
    (StackTape.cons (some a) l).length = l.length + 1 := by
  simp [cons, length]

lemma StackTape.length_cons_le {α} (o : Option α) (l : StackTape α) :
    (StackTape.cons o l).length ≤ l.length + 1 := by
  cases o with
  | none =>
    simp only [length_cons_none]
    split <;> omega
  | some a => simp [length_cons_some]

lemma StackTape.length_map_some {α} (l : List α) : (StackTape.map_some l).length = l.length := by
  simp [map_some, length]

lemma StackTape.length_empty {α} : (StackTape.empty : StackTape α).length = 0 := by
  simp [empty, length]

end Turing
