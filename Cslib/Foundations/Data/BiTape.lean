/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Cslib.Foundations.Data.StackTape
public import Mathlib.Computability.TuringMachine.Tape
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Algebra.Order.Group.Nat

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
* `BiTape.spaceUsed`: The space used by the tape
-/

@[expose] public section

namespace Turing

/--
A structure for bidirectionally-infinite Turing machine tapes
that eventually take on blank `none` values
-/
structure BiTape (Symbol : Type) where
  /-- The symbol currently under the tape head -/
  head : Option Symbol
  /-- The contents to the left of the head -/
  left : StackTape Symbol
  /-- The contents to the right of the head -/
  right : StackTape Symbol

namespace BiTape

variable {Symbol : Type}

/-- The empty `BiTape` -/
def nil : BiTape Symbol := ⟨none, ∅, ∅⟩

instance : Inhabited (BiTape Symbol) where
  default := nil

instance : EmptyCollection (BiTape Symbol) :=
  ⟨nil⟩

@[simp]
lemma empty_eq_nil : (∅ : BiTape Symbol) = nil := rfl

/--
Given a `List` of `Symbol`s, construct a `BiTape` by mapping the list to `some` elements
and laying them out to the right side,
with the head under the first element of the list if it exists.
-/
def mk₁ (l : List Symbol) : BiTape Symbol :=
  match l with
  | [] => ∅
  | h :: t => { head := some h, left := ∅, right := StackTape.mapSome t }

section Move

/--
Move the head left by shifting the left StackTape under the head.
-/
def moveLeft (t : BiTape Symbol) : BiTape Symbol :=
  ⟨t.left.head, t.left.tail, StackTape.cons t.head t.right⟩

/--
Move the head right by shifting the right StackTape under the head.
-/
def moveRight (t : BiTape Symbol) : BiTape Symbol :=
  ⟨t.right.head, StackTape.cons t.head t.left, t.right.tail⟩

/--
Move the head to the left or right, shifting the tape underneath it.
-/
def move (t : BiTape Symbol) : Dir → BiTape Symbol
  | .left => t.moveLeft
  | .right => t.moveRight

/--
Optionally perform a `move`, or do nothing if `none`.
-/
def optionMove : BiTape Symbol → Option Dir → BiTape Symbol
  | t, none => t
  | t, some d => t.move d

@[simp]
lemma moveLeft_moveRight (t : BiTape Symbol) : t.moveLeft.moveRight = t := by
  simp [moveRight, moveLeft]

@[simp]
lemma moveRight_moveLeft (t : BiTape Symbol) : t.moveRight.moveLeft = t := by
  simp [moveLeft, moveRight]

end Move

/--
Write a value under the head of the `BiTape`.
-/
def write (t : BiTape Symbol) (a : Option Symbol) : BiTape Symbol := { t with head := a }

/--
The space used by a `BiTape` is the number of symbols
between and including the head, and leftmost and rightmost non-blank symbols on the `BiTape`.
-/
@[scoped grind]
def spaceUsed (t : BiTape Symbol) : ℕ := 1 + t.left.length + t.right.length

@[simp, grind =]
lemma spaceUsed_write (t : BiTape Symbol) (a : Option Symbol) :
    (t.write a).spaceUsed = t.spaceUsed := by rfl

lemma spaceUsed_mk₁ (l : List Symbol) :
    (mk₁ l).spaceUsed = max 1 l.length := by
  cases l with
  | nil => simp [mk₁, spaceUsed, nil, StackTape.length_nil]
  | cons h t => simp [mk₁, spaceUsed, StackTape.length_nil, StackTape.length_mapSome]; omega

lemma spaceUsed_move (t : BiTape Symbol) (d : Dir) :
    (t.move d).spaceUsed ≤ t.spaceUsed + 1 := by
  cases d <;> grind [moveLeft, moveRight, move,
    spaceUsed, StackTape.length_tail_le, StackTape.length_cons_le]

end BiTape

end Turing
