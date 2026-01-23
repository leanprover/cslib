/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# StackTape: Lists of Options that don't end with none

This file defines `StackTape`, a list of `Option` values where the list cannot end with `none`.
This is useful for representing tape contents where trailing blanks are not stored.

## TODO

- Can we make pattern matching syntax work?

-/

namespace Turing

/--
List of `Option` values that don't end with `none`
-/
structure StackTape (α : Type) where
  (asList : List (Option α))
  -- The list can be empty (i.e. `none`),
  -- but if it is not empty, the last element is not (`some`) `none`
  (h : asList.getLast? ≠ some none)

def StackTape.empty {α} : StackTape α := { asList := [], h := by simp }

def StackTape.map_some {α} (l : List α) : StackTape α := { asList := l.map some, h := by simp }

instance {α : Type} : Inhabited (StackTape α) where
  default := StackTape.empty

def StackTape.length {α} (l : StackTape α) : ℕ := l.asList.length

def StackTape.cons {α} : Option α -> StackTape α -> StackTape α
| none, l => { asList := [], h := by simp }
| some a, l => {
    asList := some a :: l.asList,
    h := by
      cases hl : l.asList with
      | nil => simp
      | cons hd tl =>
        simp only [List.getLast?_cons_cons]
        rw [← hl]
        exact l.h
       }

def StackTape.tail {α} (l : StackTape α) : StackTape α :=
  match hl : l.asList with
  | [] => StackTape.empty
  | hd :: t => { asList := t, h := by
                  match t with
                  | [] => simp
                  | hd' :: t' =>
                    have lh := l.h
                    rw [hl] at lh
                    simp only [List.getLast?_cons_cons] at lh
                    have := l.h
                    rw [hl, List.getLast?_cons_cons] at this
                    exact this
  }

def StackTape.head {α} (l : StackTape α) : Option α :=
  match l.asList with
  | [] => none
  | h :: _ => h

lemma StackTape.length_tail_le {α} (l : StackTape α) : l.tail.length ≤ l.length := by
  unfold tail length
  split
  · simp [empty]
  · next heq => simp [heq]

lemma StackTape.length_cons_none {α} (l : StackTape α) : (StackTape.cons none l).length = 0 := by
  simp [cons, length]

lemma StackTape.length_cons_some {α} (a : α) (l : StackTape α) :
    (StackTape.cons (some a) l).length = l.length + 1 := by
  simp [cons, length]

lemma StackTape.length_cons_le {α} (o : Option α) (l : StackTape α) :
    (StackTape.cons o l).length ≤ l.length + 1 := by
  cases o with
  | none => simp [length_cons_none]
  | some a => simp [length_cons_some]

lemma StackTape.length_map_some {α} (l : List α) : (StackTape.map_some l).length = l.length := by
  simp [map_some, length]

lemma StackTape.length_empty {α} : (StackTape.empty : StackTape α).length = 0 := by
  simp [empty, length]

end Turing
