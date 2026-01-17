/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# OList: Lists of Options that don't end with none

This file defines `OList`, a list of option values where the list cannot end with `none`.
This is useful for representing tape contents where trailing blanks are not stored.
-/

namespace Turing

/--
List of option values that don't end with none
-/
structure OList (α : Type) where
  (asList : List (Option α))
  -- The list can be empty (i.e. none), but if it is not empty, the last element is not (some) none
  (h : asList.getLast? ≠ some none)

def OList.empty {α} : OList α := { asList := [], h := by simp }

def OList.map_some {α} (l : List α) : OList α := { asList := l.map some, h := by simp }

instance {α : Type} : Inhabited (OList α) where
  default := OList.empty


def OList.length {α} (l : OList α) : ℕ := l.asList.length

def OList.cons {α} : Option α -> OList α -> OList α
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

def OList.tail {α} (l : OList α) : OList α :=
  match hl : l.asList with
  | [] => OList.empty
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

def OList.head {α} (l : OList α) : Option α :=
  match l.asList with
  | [] => none
  | h :: _ => h

lemma OList.length_tail_le {α} (l : OList α) : l.tail.length ≤ l.length := by
  unfold tail length
  split
  · simp [empty]
  · next heq => simp [heq]

lemma OList.length_cons_none {α} (l : OList α) : (OList.cons none l).length = 0 := by
  simp [cons, length]

lemma OList.length_cons_some {α} (a : α) (l : OList α) :
    (OList.cons (some a) l).length = l.length + 1 := by
  simp [cons, length]

lemma OList.length_cons_le {α} (o : Option α) (l : OList α) :
    (OList.cons o l).length ≤ l.length + 1 := by
  cases o with
  | none => simp [length_cons_none]
  | some a => simp [length_cons_some]

lemma OList.length_map_some {α} (l : List α) : (OList.map_some l).length = l.length := by
  simp [map_some, length]

lemma OList.length_empty {α} : (OList.empty : OList α).length = 0 := by
  simp [empty, length]

end Turing
