/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Cslib.Foundations.Data.StackTape
public import Mathlib.Computability.TuringMachine

@[expose] public section

/-!
# BiTape: Bidirectionally infinite TM tape representation using StackTape

This file defines `BiTape`, a tape representation for Turing machines
in the form of an `List` of `Option` values,
with the additional property that the list cannot end with `none`.

## Design

Note that Mathlib has a `Tape` type, but it requires the alphabet type to be inhabited,
and considers the ends of the tape to be filled with default values.

This design requires the tape elements to be `Option` values, and ensures that
`List`s of the base alphabet, rendered directly onto the tape by mapping over `some`,
will not collide.

## Main definitions

* `BiTape`: A tape with a head symbol and left/right contents stored as `StackTape`
* `BiTape.move`: Move the tape head left or right
* `BiTape.write`: Write a symbol at the current head position
* `BiTape.space_used`: The space used by the tape
-/

namespace Turing

/--
A structure for bidirectionally-infinite Turing machine tapes
that eventually take on blank `none` values
-/
structure BiTape (α : Type) where
  /-- The symbol currently under the tape head -/
  (head : Option α)
  /-- The contents to the left of the head -/
  (left : StackTape α)
  /-- The contents to the right of the head -/
  (right : StackTape α)

/-- The empty `BiTape` -/
def BiTape.nil {α} : BiTape α := ⟨none, StackTape.nil, StackTape.nil⟩

instance {α : Type} : Inhabited (BiTape α) where
  default := BiTape.nil

instance {α : Type} : EmptyCollection (BiTape α) :=
  ⟨BiTape.nil⟩

/--
Given a `List` of `α`, construct a `BiTape` by mapping the list to `some` elements
and laying them out to the right side,
with the head under the first element of the list if it exists.
-/
def BiTape.mk₁ {α} (l : List α) : BiTape α :=
  match l with
  | [] => BiTape.nil
  | h :: t => ⟨some h, StackTape.nil, StackTape.map_some t⟩

section Move

/--
Move the head left by shifting the left StackTape under the head.
-/
def BiTape.move_left {α} (t : Turing.BiTape α) : Turing.BiTape α :=
  ⟨t.left.head, t.left.tail, StackTape.cons t.head t.right⟩

/--
Move the head right by shifting the right StackTape under the head.
-/
def BiTape.move_right {α} (t : Turing.BiTape α) : Turing.BiTape α :=
  ⟨t.right.head, StackTape.cons t.head t.left, t.right.tail⟩

/--
Move the head to the left or right, shifting the tape underneath it.
-/
def BiTape.move {α} (t : Turing.BiTape α) : Dir → Turing.BiTape α
  | .left => t.move_left
  | .right => t.move_right

/--
Optionally perform a `BiTape.move`, or do nothing if `none`.
-/
def BiTape.optionMove {α} : Turing.BiTape α → Option Dir → Turing.BiTape α
  | t, none => t
  | t, some d => t.move d

@[simp]
lemma BiTape.move_left_move_right {α} (t : Turing.BiTape α) :
    t.move_left.move_right = t := by
  simp [move_right, move_left]

@[simp]
lemma BiTape.move_right_move_left {α} (t : Turing.BiTape α) :
    t.move_right.move_left = t := by
  simp [move_left, move_right]

end Move

/--
Write a value under the head of the `BiTape`.
-/
def BiTape.write {α} (t : Turing.BiTape α) (a : Option α) : Turing.BiTape α := { t with head := a }

/--
The space used by a `BiTape` is the number of symbols
between and including the head, and leftmost and rightmost non-blank symbols on the `BiTape`.
-/
def BiTape.space_used {α} (t : Turing.BiTape α) : ℕ := 1 + t.left.length + t.right.length

lemma BiTape.space_used_write {α} (t : Turing.BiTape α) (a : Option α) :
    (t.write a).space_used = t.space_used := by rfl

lemma BiTape.space_used_mk₁ {α} (l : List α) :
    (BiTape.mk₁ l).space_used = max 1 l.length := by
  cases l with
  | nil => simp [mk₁, space_used, nil, StackTape.length_nil]
  | cons h t => simp [mk₁, space_used, StackTape.length_nil, StackTape.length_map_some]; omega

lemma BiTape.space_used_move {α} (t : Turing.BiTape α) (d : Dir) :
    (t.move d).space_used ≤ t.space_used + 1 := by
  cases d <;> grind [move_left, move_right, move,
    space_used, StackTape.length_tail_le, StackTape.length_cons_le]

end Turing
