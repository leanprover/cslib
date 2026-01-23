/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Cslib.Foundations.Data.StackTape
public import Mathlib.Computability.TuringMachine

@[expose] public section

/-!
# BiTape: Tape representation using StackTape

This file defines `BiTape`, a tape representation for Turing machines
in the form of an `List` of `Option` values,
with the additional property that the list cannot end with `none`.

## Design

Note that Mathlib has a `Tape` type, but it requires the alphabet type to be inhabited,
and considers the ends of the tape to be filled with default values.

The design that requires the tape elements to be `Option` values ensures that
Lists of the base alphabet, rendered directly onto the tape by mapping over `some`,
will not collide.

## Main definitions

* `BiTape`: A tape with a head symbol and left/right contents stored as `StackTape`
* `BiTape.move`: Move the tape head left or right
* `BiTape.write`: Write a symbol at the current head position
* `BiTape.space_used`: The space used by the tape
-/

namespace Turing

/--
I find this more convenient than mathlib's Tape type,
because that requires the type tobe inhabited,
and it is easy to confuse a list representing one thing with a list representing another,
if the representations are the same except for a sequence of default values at the end.

The head of the machine is the current symbol under the tape head.
We do not assume here, but could add, that the ends of the tape are never none.
The move function should guarantee this, so that two tapes are equal
even if one has written none to the side
-/
structure BiTape (α : Type) where
  (head : Option α)
  (left : StackTape α)
  (right : StackTape α)
deriving Inhabited

def BiTape.mk₁ {α} (l : List α) : BiTape α :=
  match l with
  | [] => { head := none, left := StackTape.empty, right := StackTape.empty }
  | h :: t => { head := some h, left := StackTape.empty, right := StackTape.map_some t }

def BiTape.move {α} : Turing.BiTape α → Dir → Turing.BiTape α
  | t, .left =>
    match t.left, t.head, t.right with
    | l, h, r => { head := l.head, left := l.tail, right := StackTape.cons h r }
  | t, .right =>
    match t.left, t.head, t.right with
    | l, h, r => { head := r.head, left := StackTape.cons h l, right := r.tail }


def BiTape.move? {α} : Turing.BiTape α → Option Dir → Turing.BiTape α
  | t, none => t
  | t, some d => t.move d

def BiTape.write {α} : Turing.BiTape α → Option α → Turing.BiTape α
  | t, a => { t with head := a }

/--
The space used by a BiTape is the number of symbols
between and including the head, and leftmost and rightmost non-blank symbols on the BiTape
-/
def BiTape.space_used {α} (t : Turing.BiTape α) : ℕ :=
  1 + t.left.length + t.right.length

lemma BiTape.space_used_write {α} (t : Turing.BiTape α) (a : Option α) :
    (t.write a).space_used = t.space_used := by
  rfl

lemma BiTape.space_used_mk₁ (l : List α) :
    (BiTape.mk₁ l).space_used = max 1 l.length := by
  cases l with
  | nil =>
    simp [mk₁, space_used, StackTape.length_empty]
  | cons h t =>
    simp [mk₁, space_used, StackTape.length_empty, StackTape.length_map_some]
    omega

lemma BiTape.space_used_move {α} (t : Turing.BiTape α) (d : Dir) :
    (t.move d).space_used ≤ t.space_used + 1 := by
  cases d with
  | left =>
    simp only [move, space_used]
    have h1 := StackTape.length_tail_le t.left
    have h2 := StackTape.length_cons_le t.head t.right
    omega
  | right =>
    simp only [move, space_used]
    have h1 := StackTape.length_cons_le t.head t.left
    have h2 := StackTape.length_tail_le t.right
    omega

end Turing
