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
This is useful as a data structure with a simple API for manipulation by Turing machines.

## TODO

- Make a `::`-like notation.

-/

namespace Turing

/--
An infinite tape representation using a list of `Option` values,
where the list is eventually `none`.

Represented as a `List (Option α)` that does not end with `none`.
-/
structure StackTape (α : Type) where
  /-- The underlying list representation -/
  toList : List (Option α)
  /--
  The list can be empty (i.e. `none`),
  but if it is not empty, the last element is not (`some`) `none`
  -/
  toList_getLast?_ne_some_none : toList.getLast? ≠ some none

attribute [scoped grind! .] StackTape.toList_getLast?_ne_some_none

namespace StackTape

/-- The empty `StackTape` -/
def nil {α} : StackTape α := ⟨[], by grind⟩

instance {α : Type} : Inhabited (StackTape α) where
  default := nil

instance {α : Type} : EmptyCollection (StackTape α) :=
  ⟨nil⟩

@[simp]
lemma empty_eq_nil {α} : (∅ : StackTape α) = nil := rfl

/-- Create a `StackTape` from a list by mapping all elements to `some` -/
def map_some {α} (l : List α) : StackTape α := ⟨l.map some, by simp⟩

/-- Prepend an `Option` to the `StackTape` -/
def cons {α} (x : Option α) (xs : StackTape α) : StackTape α :=
  match x, xs with
  | none, ⟨[], _⟩ => ⟨[], by grind⟩
  | none, ⟨hd :: tl, hl⟩ => ⟨none :: hd :: tl, by grind⟩
  | some a, ⟨l, hl⟩ => ⟨some a :: l, by grind⟩

/-- Remove the first element of the `StackTape`, returning the rest -/
def tail {α} (l : StackTape α) : StackTape α :=
  match hl : l.toList with
  | [] => nil
  | hd :: t => ⟨t, by grind⟩

/-- Get the first element of the `StackTape`. -/
def head {α} (l : StackTape α) : Option α :=
  match l.toList with
  | [] => none
  | h :: _ => h

lemma eq_iff {α} (l1 l2 : StackTape α) : l1 = l2 ↔ l1.head = l2.head ∧ l1.tail = l2.tail := by
  constructor
  · grind
  · intro ⟨hhead, htail⟩
    cases l1 with | mk as1 h1 =>
    cases l2 with | mk as2 h2 =>
    cases as1 <;> cases as2 <;> grind [tail, head, mk.injEq, nil, mk.injEq]

@[simp]
lemma head_cons {α} (o : Option α) (l : StackTape α) : (cons o l).head = o := by
  cases o with
  | none =>
    cases l with | mk toList hl =>
    cases toList <;> simp [cons, head]
  | some a => simp [cons, head]

@[simp]
lemma tail_cons {α} (o : Option α) (l : StackTape α) : (cons o l).tail = l := by
  cases o with
  | none =>
    cases l with | mk toList h =>
    cases toList with
    | nil => simp [cons, tail, nil]
    | cons hd tl => simp [cons, tail]
  | some a =>
    simp only [cons, tail]

@[simp]
lemma cons_head_tail {α} (l : StackTape α) :
    cons (l.head) (l.tail) = l := by
  rw [eq_iff]
  simp

section Length

/-- The length of the `StackTape` is the number of elements up to the last non-`none` element -/
def length {α} (l : StackTape α) : ℕ := l.toList.length

lemma length_tail_le {α} (l : StackTape α) : l.tail.length ≤ l.length := by
  grind [tail, length, nil]

lemma length_cons_none {α} (l : StackTape α) :
    (cons none l).length = l.length + if l.length = 0 then 0 else 1 := by
  cases l with | mk toList h =>
  cases toList <;> simp [cons, length]

lemma length_cons_some {α} (a : α) (l : StackTape α) : (cons (some a) l).length = l.length + 1 := by
  simp [cons, length]

lemma length_cons_le {α} (o : Option α) (l : StackTape α) : (cons o l).length ≤ l.length + 1 := by
  cases o <;> grind [length_cons_none, length_cons_some]

lemma length_map_some {α} (l : List α) : (map_some l).length = l.length := by
  simp [map_some, length]

lemma length_nil {α} : (nil : StackTape α).length = 0 := by simp [nil, length]

end Length

end StackTape

end Turing
