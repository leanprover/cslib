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
  (head : Option α)
  (left : StackTape α)
  (right : StackTape α)
deriving Inhabited

/--
Given a `List` of `α`, construct a `BiTape` by mapping the list to `some` elements
and laying them out to the right side,
with the head under the first element of the list if it exists.
-/
def BiTape.mk₁ {α} (l : List α) : BiTape α :=
  match l with
  | [] => { head := none, left := StackTape.empty, right := StackTape.empty }
  | h :: t => { head := some h, left := StackTape.empty, right := StackTape.map_some t }

/--
Move the head to the left or right, shifting the tape underneath it.
-/
def BiTape.move {α} : Turing.BiTape α → Dir → Turing.BiTape α
  | t, .left =>
    match t.left, t.head, t.right with
    | l, h, r => { head := l.head, left := l.tail, right := StackTape.cons h r }
  | t, .right =>
    match t.left, t.head, t.right with
    | l, h, r => { head := r.head, left := StackTape.cons h l, right := r.tail }

/--
Optionally perform a `BiTape.move`, or do nothing if `none`.
-/
def BiTape.optionMove {α} : Turing.BiTape α → Option Dir → Turing.BiTape α
  | t, none => t
  | t, some d => t.move d

/--
Write a value under the head of the `BiTape`.
-/
def BiTape.write {α} : Turing.BiTape α → Option α → Turing.BiTape α
  | t, a => { t with head := a }

/--
The space used by a `BiTape` is the number of symbols
between and including the head, and leftmost and rightmost non-blank symbols on the `BiTape`.
-/
def BiTape.space_used {α} (t : Turing.BiTape α) : ℕ :=
  1 + t.left.length + t.right.length

lemma BiTape.space_used_write {α} (t : Turing.BiTape α) (a : Option α) :
    (t.write a).space_used = t.space_used := by
  rfl

lemma BiTape.space_used_mk₁ {α} (l : List α) :
    (BiTape.mk₁ l).space_used = max 1 l.length := by
  cases l <;> grind [mk₁, space_used, StackTape.length_empty, StackTape.length_map_some]

lemma BiTape.space_used_move {α} (t : Turing.BiTape α) (d : Dir) :
    (t.move d).space_used ≤ t.space_used + 1 := by
  cases d <;> grind [move, space_used, StackTape.length_tail_le, StackTape.length_cons_le]

end Turing
