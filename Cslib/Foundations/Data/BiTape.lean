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

open StackTape

variable {Symbol : Type}

instance : Inhabited (BiTape Symbol) where
  default := ⟨none, ∅, ∅⟩

instance : EmptyCollection (BiTape Symbol) := ⟨default⟩

@[simp]
lemma empty_eq_default : (∅ : BiTape Symbol) = default := rfl

/--
Given a `List` of `Symbol`s, construct a `BiTape` by mapping the list to `some` elements
and laying them out to the right side,
with the head under the first element of the list if it exists.
-/
def mk₁ (l : List Symbol) : BiTape Symbol :=
  { head := l.head?, left := ∅, right := StackTape.mapSome l.tail }

@[simp, scoped grind =]
lemma mk₁_nil : mk₁ ([] : List Symbol) = ∅ := rfl

open scoped Int in
/-- Returns the tape symbol at positon `p` relative to the head, where
positive numbers are right of the head and negative are left of the head. -/
@[scoped grind]
def get (t : BiTape Symbol) : ℤ → Option Symbol
  | 0 => t.head
  | (p' + 1 : Nat) => t.right.toList[p']?.getD none
  | -[p'+1] => t.left.toList[p']?.getD none

lemma get_succ (t : BiTape Symbol) (p : ℕ) : t.get (p + 1) = t.right.toList[p]?.getD none := by
  grind [get]

/-- Two tapes are equal if and only if their `get` functions are equal. This allows to view
tapes as functions `ℤ → Option Symbol` and composes better across moves. -/
@[ext]
lemma ext_get (t₁ t₂ : BiTape Symbol) (h_get_eq : ∀ p, t₁.get p = t₂.get p) : t₁ = t₂ := by
  cases t₁
  congr
  · simpa [get] using h_get_eq 0
  · apply StackTape.ext_get
    intro p
    simpa [get] using h_get_eq (Int.negSucc p)
  · apply StackTape.ext_get
    intro p
    simpa [get_succ] using h_get_eq (p + 1)

/-- Simplification lemma that explains the contents of each of the cells after tape
construction using mk₁. -/
@[simp, scoped grind =]
lemma get_mk₁ (l : List Symbol) (p : ℤ) :
  (mk₁ l).get p = if p < 0 then none else l[p.toNat]? := by
  match p with
  | Int.ofNat 0 => simp [mk₁, get, List.head?_eq_getElem?]
  | Int.ofNat (n + 1) => grind [mk₁, get]
  | Int.negSucc n => cases l <;> simp [mk₁, get]

section Move

/--
Move the head left by shifting the left StackTape under the head.
-/
@[scoped grind =]
def moveLeft (t : BiTape Symbol) : BiTape Symbol :=
  ⟨t.left.head, t.left.tail, StackTape.cons t.head t.right⟩

/--
Move the head right by shifting the right StackTape under the head.
-/
@[scoped grind =]
def moveRight (t : BiTape Symbol) : BiTape Symbol :=
  ⟨t.right.head, StackTape.cons t.head t.left, t.right.tail⟩

/--
Move the head to the left or right, shifting the tape underneath it.
-/
@[scoped grind =]
def move (t : BiTape Symbol) : Dir → BiTape Symbol
  | .left => t.moveLeft
  | .right => t.moveRight

/--
Optionally perform a `move`, or do nothing if `none`.
-/
@[simp, scoped grind =]
def optionMove : BiTape Symbol → Option Dir → BiTape Symbol
  | t, none => t
  | t, some d => t.move d

@[simp]
lemma moveLeft_moveRight (t : BiTape Symbol) : t.moveLeft.moveRight = t := by
  simp [moveRight, moveLeft]

@[simp]
lemma moveRight_moveLeft (t : BiTape Symbol) : t.moveRight.moveLeft = t := by
  simp [moveLeft, moveRight]

/-- Translate an optional direction into a head movement offset, where the positive
direction is to the right. -/
@[scoped grind =]
def optionDirToInt (d : Option Dir) : ℤ :=
  match d with
  | none => 0
  | some .left => -1
  | some .right => 1

@[simp, scoped grind =]
lemma get_moveLeft (t : BiTape Symbol) (p : ℤ) : t.moveLeft.get p = t.get (p - 1) := by
  unfold moveLeft get
  match p with
  | Int.ofNat 0 =>
    simp [StackTape.head_eq_getD]
    rfl
  | Int.ofNat 1 => simp
  | Int.ofNat (n + 2) =>
    rw [show Int.ofNat (n + 2) - 1 = Int.ofNat (n + 1) by lia]
    simp
  | Int.negSucc n => simp

@[simp, scoped grind =]
lemma get_moveRight (t : BiTape Symbol) (p : ℤ) : t.moveRight.get p = t.get (p + 1) := by
  unfold moveRight get
  match p with
  | Int.ofNat n =>
    rw [show Int.ofNat n + 1 = Int.ofNat (n + 1) by lia]
    cases n <;> simp [StackTape.head_eq_getD]
  | Int.negSucc 0 => simp
  | Int.negSucc (n + 1) =>
    rw [show Int.negSucc (n + 1) + 1 = Int.negSucc n from rfl]
    simp

@[simp, scoped grind =]
lemma get_move (t : BiTape Symbol) (d : Dir) (p : ℤ) :
    (t.move d).get p = t.get (p + optionDirToInt (some d)) := by
  cases d <;> grind

@[simp, scoped grind =]
lemma get_moveRight_iterate (t : BiTape Symbol) (n : ℕ) (p : ℤ) :
    (moveRight^[n] t).get p = t.get (p + n):= by
  induction n generalizing t p with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply, ih, Int.add_assoc]

@[simp, scoped grind =]
lemma get_moveLeft_iterate (t : BiTape Symbol) (n : ℕ) (p : ℤ) :
    (moveLeft^[n] t).get p = t.get (p - n):= by
  induction n generalizing t p with
  | zero => simp
  | succ n ih =>
    have : p - n - 1 = p - (n + 1) := by lia
    simp [Function.iterate_succ_apply, ih, this]

/-- Move the tape head by an integer amount where positive numbers move the head to the right and
negative to the left. -/
def moveInt (t : BiTape Symbol) (Δ : ℤ) : BiTape Symbol :=
  if Δ ≥ 0 then
    .moveRight^[Δ.toNat] t
  else
    .moveLeft^[(-Δ).toNat] t

@[simp, scoped grind =]
lemma get_moveInt (t : BiTape Symbol) (Δ p : ℤ) :
  (moveInt t Δ).get p = t.get (p + Δ) := by
  grind [moveInt]

@[simp, scoped grind =]
lemma head_moveInt (t : BiTape Symbol) (Δ : ℤ) :
  (moveInt t Δ).head = t.get Δ := by
  rw [show (moveInt t Δ).head = (moveInt t Δ).get 0 from rfl]
  grind [moveInt]

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
def spaceUsed (t : BiTape Symbol) : ℕ := 1 + t.left.length + t.right.length

@[simp, grind =]
lemma spaceUsed_write (t : BiTape Symbol) (a : Option Symbol) :
    (t.write a).spaceUsed = t.spaceUsed := by rfl

lemma spaceUsed_mk₁ (l : List Symbol) :
    (mk₁ l).spaceUsed = max 1 l.length := by
  cases l with
  | nil => simp [mk₁, spaceUsed, StackTape.length_nil]
  | cons h t => simp [mk₁, spaceUsed, StackTape.length_nil, StackTape.length_mapSome]; omega

lemma spaceUsed_move (t : BiTape Symbol) (d : Dir) :
    (t.move d).spaceUsed ≤ t.spaceUsed + 1 := by
  cases d <;> grind [moveLeft, moveRight, move,
    spaceUsed, StackTape.length_tail_le, StackTape.length_cons_le]

end BiTape

end Turing
