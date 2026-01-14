/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Cslib.Foundations.Data.OList
public import Mathlib.Computability.TuringMachine

@[expose] public section

/-!
# OTape: Tape representation using OList

This file defines `OTape`, a tape representation for Turing machines
in the form of an `List` of `Option` values,
with the additional property that the list cannot end with `none`.

## Design

Note that Mathlib has a `Tape` type, but it requires the alphabet type to be inhabited,
and considers the ends of the tape to be filled with default values.

The design that requires the tape elements to be `Option` values ensures that
Lists of the base alphabet, rendered directly onto the tape by mapping over `some`,
will not collide.

## Main definitions

* `OTape`: A tape with a head symbol and left/right contents stored as `OList`
* `OTape.move`: Move the tape head left or right
* `OTape.write`: Write a symbol at the current head position
* `OTape.space_used`: The space used by the tape
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
structure OTape (α : Type) where
  (head : Option α)
  (left : OList α)
  (right : OList α)
deriving Inhabited

def OTape.mk₁ (l : List Bool) : OTape Bool :=
  match l with
  | [] => { head := none, left := OList.empty, right := OList.empty }
  | h :: t => { head := some h, left := OList.empty, right := OList.map_some t }

def OTape.move {α} : Turing.OTape α → Dir → Turing.OTape α
  | t, .left =>
    match t.left, t.head, t.right with
    | l, h, r => { head := l.head, left := l.tail, right := OList.cons h r }
  | t, .right =>
    match t.left, t.head, t.right with
    | l, h, r => { head := r.head, left := OList.cons h l, right := r.tail }


def OTape.move? {α} : Turing.OTape α → Option Dir → Turing.OTape α
  | t, none => t
  | t, some d => t.move d

def OTape.write {α} : Turing.OTape α → Option α → Turing.OTape α
  | t, a => { t with head := a }

open Classical in
noncomputable def ListBlank.space_used {α} [Inhabited α] (l : ListBlank α) : ℕ :=
  Nat.find (p := fun n => ∀ i > n, l.nth i = default)
    (l.inductionOn (fun xs => ⟨xs.length, fun i hi => by
      change (ListBlank.mk xs).nth i = default
      rw [ListBlank.nth_mk]
      exact List.getI_eq_default xs (Nat.le_of_lt hi)⟩))

/--
The space used by a OTape is the number of symbols
between and including the head, and leftmost and rightmost non-blank symbols on the OTape
-/
noncomputable def OTape.space_used {α} [Inhabited α] (t : Turing.OTape α) : ℕ :=
  1 + t.left.length + t.right.length

lemma OTape.space_used_write {α} [Inhabited α] (t : Turing.OTape α) (a : Option α) :
    (t.write a).space_used = t.space_used := by
  rfl

lemma OTape.space_used_mk₁ (l : List Bool) :
    (OTape.mk₁ l).space_used = max 1 l.length := by
  cases l with
  | nil =>
    simp [mk₁, space_used, OList.length_empty]
  | cons h t =>
    simp [mk₁, space_used, OList.length_empty, OList.length_map_some]
    omega

lemma OTape.space_used_move {α} [Inhabited α] (t : Turing.OTape α) (d : Dir) :
    (t.move d).space_used ≤ t.space_used + 1 := by
  cases d with
  | left =>
    simp only [move, space_used]
    have h1 := OList.length_tail_le t.left
    have h2 := OList.length_cons_le t.head t.right
    omega
  | right =>
    simp only [move, space_used]
    have h1 := OList.length_cons_le t.head t.left
    have h2 := OList.length_tail_le t.right
    omega

end Turing
