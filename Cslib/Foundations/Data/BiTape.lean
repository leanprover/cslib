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
  | h :: t => { head := some h, left := ∅, right := StackTape.map_some t }

open scoped Int in
/-- Returns the tape symbol at positon `p` relative to the head, where
positive numbers are right of the head and negative are left of the head. -/
@[scoped grind]
def get (t : BiTape Symbol) : ℤ → Option Symbol
  | 0 => t.head
  | (p' + 1 : Nat) => t.right.toList[p']?.getD none
  | -[p'+1] => t.left.toList[p']?.getD none

/-- Two tapes are equal if and only if their `get` functions are equal. This allows to view
tapes as functions `ℤ → Option Symbol`. -/
@[ext]
lemma ext_get (t₁ t₂ : BiTape Symbol) (h_get_eq : ∀ p, t₁.get p = t₂.get p) : t₁ = t₂ := by
  obtain ⟨head₁, left₁, right₁⟩ := t₁
  obtain ⟨head₂, left₂, right₂⟩ := t₂
  have h_head : head₁ = head₂ := by simpa [get] using h_get_eq 0
  have h_right : right₁ = right₂ := by
    apply StackTape.ext_get
    intro p
    simpa [get] using h_get_eq (p + 1)
  have h_left : left₁ = left₂ := by
    apply StackTape.ext_get
    intro p
    simpa [get] using h_get_eq (Int.negSucc p)
  grind


section Move

/--
Move the head left by shifting the left StackTape under the head.
-/
def move_left (t : BiTape Symbol) : BiTape Symbol :=
  ⟨t.left.head, t.left.tail, StackTape.cons t.head t.right⟩

/--
Move the head right by shifting the right StackTape under the head.
-/
def move_right (t : BiTape Symbol) : BiTape Symbol :=
  ⟨t.right.head, StackTape.cons t.head t.left, t.right.tail⟩

/--
Move the head to the left or right, shifting the tape underneath it.
-/
def move (t : BiTape Symbol) : Dir → BiTape Symbol
  | .left => t.move_left
  | .right => t.move_right

/--
Optionally perform a `move`, or do nothing if `none`.
-/
def optionMove : BiTape Symbol → Option Dir → BiTape Symbol
  | t, none => t
  | t, some d => t.move d

@[simp]
lemma move_left_move_right (t : BiTape Symbol) : t.move_left.move_right = t := by
  simp [move_right, move_left]

@[simp]
lemma move_right_move_left (t : BiTape Symbol) : t.move_right.move_left = t := by
  simp [move_left, move_right]

/-- Translate an optional direction into a head movement offset, where the positive
direction is to the right. -/
@[scoped grind]
def optionDirToInt (d : Option Dir) : ℤ :=
  match d with
  | none => 0
  | some .left => -1
  | some .right => 1

@[simp, scoped grind =]
lemma get_move_left (t : BiTape Symbol) (p : ℤ) :
    (t.move_left).get p = t.get (p - 1) := by
  unfold move_left get
  match p with
  | Int.ofNat 0 =>
    rw [show Int.ofNat 0 - 1 = Int.negSucc 0 from rfl]
    simp [StackTape.head_eq_getD]
  | Int.ofNat 1 => simp
  | Int.ofNat (n + 2) =>
    rw [show Int.ofNat (n + 2) - 1 = Int.ofNat (n + 1) by lia]
    simp
  | Int.negSucc n => simp

@[simp, scoped grind =]
lemma get_move_right (t : BiTape Symbol) (p : ℤ) :
    (t.move_right).get p = t.get (p + 1) := by
  unfold move_right get
  match p with
  | Int.ofNat n =>
    rw [show Int.ofNat n + 1 = Int.ofNat (n + 1) by lia]
    cases n <;> simp [StackTape.head_eq_getD]
  | Int.negSucc 0 => simp
  | Int.negSucc (n + 1) =>
    rw [show Int.negSucc (n + 1) + 1 = Int.negSucc n from rfl]
    simp

@[simp, scoped grind =]
lemma get_optionMove (t : BiTape Symbol) (d : Option Dir) (p : ℤ) :
    (t.optionMove d).get p = t.get (p + optionDirToInt d) := by
  unfold optionMove optionDirToInt
  grind [move]

@[simp, scoped grind =]
lemma get_move_right_iterate (t : BiTape Symbol) (n : ℕ) (p : ℤ) :
    (move_right^[n] t).get p = t.get (p + n):= by
  induction n generalizing t p with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply, ih, Int.add_assoc]

@[simp, scoped grind =]
lemma get_move_left_iterate (t : BiTape Symbol) (n : ℕ) (p : ℤ) :
    (move_left^[n] t).get p = t.get (p - n):= by
  induction n generalizing t p with
  | zero => simp
  | succ n ih =>
    have : p - n - 1 = p - (n + 1) := by lia
    simp [Function.iterate_succ_apply, ih, this]

end Move

/--
Write a value under the head of the `BiTape`.
-/
def write (t : BiTape Symbol) (a : Option Symbol) : BiTape Symbol := { t with head := a }

@[simp, scoped grind =]
lemma get_write (t : BiTape Symbol) (a : Option Symbol) :
    (t.write a).get = Function.update t.get 0 a := by
  unfold write get Function.update
  funext p
  match p with
  | Int.ofNat 0 => simp
  | Int.ofNat (n + 1) => grind
  | Int.negSucc n => simp

/--
The space used by a `BiTape` is the number of symbols
between and including the head, and leftmost and rightmost non-blank symbols on the `BiTape`.
-/
@[scoped grind]
def space_used (t : BiTape Symbol) : ℕ := 1 + t.left.length + t.right.length

@[simp, grind =]
lemma space_used_write (t : BiTape Symbol) (a : Option Symbol) :
    (t.write a).space_used = t.space_used := by rfl

lemma space_used_mk₁ (l : List Symbol) :
    (mk₁ l).space_used = max 1 l.length := by
  cases l with
  | nil => simp [mk₁, space_used, nil, StackTape.length_nil]
  | cons h t => simp [mk₁, space_used, StackTape.length_nil, StackTape.length_map_some]; omega

lemma space_used_move (t : BiTape Symbol) (d : Dir) :
    (t.move d).space_used ≤ t.space_used + 1 := by
  cases d <;> grind [move_left, move_right, move,
    space_used, StackTape.length_tail_le, StackTape.length_cons_le]

end BiTape

end Turing
