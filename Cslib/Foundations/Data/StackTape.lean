/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Cslib.Init

@[expose] public section

/-!
# StackTape: Infinite, eventually-`none` lists of `Option`s

This file defines `StackTape`, a stack-like data structure of `Option` values,
where the tape is considered to be infinite and eventually all `none`s.
This is useful as a data structure with a simple API for manipulation by Turing machines.

## Design

`StackTape` is represented as a list of `Option` values where the list cannot end with `none`.
The end of the list is then treated as the start of an infinite sequence of `none` values
by the low-level API.
This design makes it convenient to express the length of the tape in terms of the list length.

An alternative design would be to represent the tape as a `Stream' (Option Symbol)`,
with additional fields tracking the length and the fact that the stream eventually becomes `none`.
This design might complicate reasoning about the length of the tape, but could make other operations
more straightforward.

Future design work might explore this alternative representation and compare its
advantages and disadvantages.

## TODO

- Make a `::`-like notation.

-/

namespace Turing

/--
An infinite tape representation using a list of `Option` values,
where the list is eventually `none`.

Represented as a `List (Option Symbol)` that does not end with `none`.
-/
structure StackTape (Symbol : Type) where
  /-- The underlying list representation -/
  toList : List (Option Symbol)
  /--
  The list can be empty (i.e. `none`),
  but if it is not empty, the last element is not (`some`) `none`
  -/
  toList_getLast?_ne_some_none : toList.getLast? ≠ some none

attribute [scoped grind! .] StackTape.toList_getLast?_ne_some_none

namespace StackTape

variable {Symbol : Type}

/-- The empty `StackTape` -/
@[scoped grind]
def nil : StackTape Symbol := ⟨[], by grind⟩

instance : Inhabited (StackTape Symbol) where
  default := nil

instance : EmptyCollection (StackTape Symbol) :=
  ⟨nil⟩

@[simp]
lemma empty_eq_nil : (∅ : StackTape Symbol) = nil := rfl

@[simp, scoped grind =]
lemma nil_toList : (nil : StackTape Symbol).toList = [] := rfl

/-- Prepend an `Option` to the `StackTape` -/
@[scoped grind]
def cons (x : Option Symbol) (xs : StackTape Symbol) : StackTape Symbol :=
  match x, xs with
  | none, ⟨[], _⟩ => ⟨[], by grind⟩
  | none, ⟨hd :: tl, hl⟩ => ⟨none :: hd :: tl, by grind⟩
  | some a, ⟨l, hl⟩ => ⟨some a :: l, by grind⟩

@[simp, scoped grind =]
lemma cons_none_nil_toList : (cons none (nil : StackTape Symbol)).toList = [] := by grind

@[simp, scoped grind =]
lemma cons_some_toList (a : Symbol) (l : StackTape Symbol) :
    (cons (some a) l).toList = some a :: l.toList := by simp only [cons]

/-- Remove the first element of the `StackTape`, returning the rest -/
@[scoped grind]
def tail (l : StackTape Symbol) : StackTape Symbol :=
  match hl : l.toList with
  | [] => nil
  | hd :: t => ⟨t, by grind⟩

/-- Get the first element of the `StackTape`. -/
@[scoped grind]
def head (l : StackTape Symbol) : Option Symbol :=
  match l.toList with
  | [] => none
  | h :: _ => h

lemma eq_iff (l1 l2 : StackTape Symbol) :
    l1 = l2 ↔ l1.head = l2.head ∧ l1.tail = l2.tail := by
  constructor
  · grind
  · intro ⟨hhead, htail⟩
    cases l1 with | mk as1 h1 =>
    cases l2 with | mk as2 h2 =>
    cases as1 <;> cases as2 <;> grind

@[simp]
lemma head_cons (o : Option Symbol) (l : StackTape Symbol) : (cons o l).head = o := by
  cases o with
  | none =>
    cases l with | mk toList hl =>
    cases toList <;> grind
  | some a => grind

@[simp]
lemma tail_cons (o : Option Symbol) (l : StackTape Symbol) : (cons o l).tail = l := by
  cases o with
  | none =>
    cases l with | mk toList h =>
    cases toList <;> grind
  | some a =>
    simp only [cons, tail]

@[simp]
lemma cons_head_tail (l : StackTape Symbol) :
    cons (l.head) (l.tail) = l := by
  rw [eq_iff]
  simp

/-- Create a `StackTape` from a list by mapping all elements to `some` -/
@[scoped grind]
def map_some (l : List Symbol) : StackTape Symbol := ⟨l.map some, by simp⟩

section Length

/-- The length of the `StackTape` is the number of elements up to the last non-`none` element -/
@[scoped grind]
def length (l : StackTape Symbol) : ℕ := l.toList.length

lemma length_tail_le (l : StackTape Symbol) : l.tail.length ≤ l.length := by
  grind

grind_pattern length_tail_le => l.tail.length

@[scoped grind =]
lemma length_cons_none (l : StackTape Symbol) :
    (cons none l).length = l.length + if l.length = 0 then 0 else 1 := by
  cases l with | mk toList h =>
  cases toList <;> grind

@[scoped grind =]
lemma length_cons_some (a : Symbol) (l : StackTape Symbol) :
    (cons (some a) l).length = l.length + 1 := by
  grind

lemma length_cons_le (o : Option Symbol) (l : StackTape Symbol) :
    (cons o l).length ≤ l.length + 1 := by
  cases o <;> grind

@[simp, scoped grind =]
lemma length_map_some (l : List Symbol) : (map_some l).length = l.length := by grind

@[simp, scoped grind =]
lemma length_nil : (nil : StackTape Symbol).length = 0 := by grind

end Length

end StackTape

end Turing
