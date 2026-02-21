/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Christian Reitwiessner
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
  head : Option α
  /-- The contents to the left of the head -/
  left : StackTape α
  /-- The contents to the right of the head -/
  right : StackTape α

namespace BiTape

/-- The empty `BiTape` -/
def nil {α} : BiTape α := ⟨none, ∅, ∅⟩

instance {α : Type} : Inhabited (BiTape α) where
  default := nil

instance {α : Type} : EmptyCollection (BiTape α) :=
  ⟨nil⟩

@[simp]
lemma empty_eq_nil {α} : (∅ : BiTape α) = nil := rfl

/--
Given a `List` of `α`, construct a `BiTape` by mapping the list to `some` elements
and laying them out to the right side,
with the head under the first element of the list if it exists.
-/
def mk₁ {α} (l : List α) : BiTape α :=
  match l with
  | [] => ∅
  | h :: t => { head := some h, left := ∅, right := StackTape.map_some t }

/-- Indexes the tape using integers, where `0` is the symbol at the tape head,
positive integers index to the right, and negative integers index to the left. -/
def nth {α} (t : BiTape α) (n : ℤ) : Option α :=
  match n with
  | Int.ofNat 0 => t.head
  | Int.ofNat (n + 1) => t.right.toList.getD n none
  | Int.negSucc n => t.left.toList.getD n none

@[simp, grind =]
lemma nth_zero {α} (t : BiTape α) :
    t.nth 0 = t.head := by rfl

lemma ext_nth {α} {t₁ t₂ : BiTape α} (h_nth_eq : ∀ n, t₁.nth n = t₂.nth n) :
  t₁ = t₂ := by
  cases t₁ with | mk head₁ left₁ right₁
  cases t₂ with | mk head₂ left₂ right₂
  simp only [mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · -- head₁ = head₂
    have := h_nth_eq 0
    simpa [nth] using this
  · -- left₁ = left₂
    apply StackTape.ext_toList
    intro n
    have := h_nth_eq (Int.negSucc n)
    sorry -- simpa [nth] using this

  · -- right₁ = right₂
    apply StackTape.ext_toList
    intro n
    have := h_nth_eq (Int.ofNat (n + 1))
    sorry -- simpa [nth] using this

section Move

/--
Move the head left by shifting the left StackTape under the head.
-/
def move_left {α} (t : BiTape α) : BiTape α :=
  ⟨t.left.head, t.left.tail, StackTape.cons t.head t.right⟩

/--
Move the head right by shifting the right StackTape under the head.
-/
def move_right {α} (t : BiTape α) : BiTape α :=
  ⟨t.right.head, StackTape.cons t.head t.left, t.right.tail⟩

/--
Move the head to the left or right, shifting the tape underneath it.
-/
def move {α} (t : BiTape α) : Dir → BiTape α
  | .left => t.move_left
  | .right => t.move_right

/--
Optionally perform a `move`, or do nothing if `none`.
-/
def optionMove {α} : BiTape α → Option Dir → BiTape α
  | t, none => t
  | t, some d => t.move d

@[simp]
lemma move_left_move_right {α} (t : BiTape α) : t.move_left.move_right = t := by
  simp [move_right, move_left]

@[simp]
lemma move_right_move_left {α} (t : BiTape α) : t.move_right.move_left = t := by
  simp [move_left, move_right]


@[simp, grind =]
lemma move_right_nth {α} (t : BiTape α) (p : ℤ) :
    (t.move_right).nth p = t.nth (p + 1) := by
  unfold nth
  split
  · grind [move_right]
  · rename_i n
    simp only [move_right, List.getD_eq_getElem?_getD, Nat.succ_eq_add_one, Int.ofNat_eq_natCast,
      Int.natCast_add, Int.cast_ofNat_Int]
    have h: (n : ℤ) + 1 + 1 ≥ 2 := by omega
    split
    · grind
    · rename_i n'' h_eq
      simp at h_eq
      rw [show n'' = n + 1 by omega]
      simp
    · grind
  · rename_i n
    simp only [move_right, List.getD_eq_getElem?_getD]
    split
    · rename_i h_eq
      simp only [StackTape.cons]
      grind
    · grind
    · rename_i n' h_eq
      rw [show n = n' + 1 by omega]
      simp only [StackTape.cons]
      grind

@[simp, grind =]
lemma move_left_nth {α} (t : BiTape α) (p : ℤ) :
    (t.move_left).nth p = t.nth (p - 1) := by
  rw [← move_left_move_right t]
  simp only [move_right_nth]
  simp

@[simp, grind =]
lemma move_right_iter_nth {α} (t : BiTape α) (n : ℕ) (p : ℤ) :
    (move_right^[n] t).nth p = t.nth (p + n) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    grind

@[simp, grind =]
lemma move_left_iter_nth {α} (t : BiTape α) (n : ℕ) (p : ℤ) :
    (move_left^[n] t).nth p = t.nth (p - n) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    grind

/-- Move the head by an integer amount of cells where positive amounts cause the tape head to move
to the right while a negative amounts move the tape head to the left. -/
def move_int {α} (t : BiTape α) (delta : ℤ) : BiTape α :=
  match delta with
  | Int.ofNat n => move_right^[n] t
  | Int.negSucc n => move_left^[n + 1] t

@[simp, grind =]
lemma move_int_zero_eq_id {α} (t : BiTape α) :
    t.move_int 0 = t := by rfl

@[simp, grind =]
lemma move_int_one_eq_move_right {α} (t : BiTape α) :
    t.move_int 1 = move_right t := by rfl

@[simp, grind =]
lemma move_int_neg_one_eq_move_left {α} (t : BiTape α) :
    t.move_int (-1) = move_left t := by rfl

@[simp, grind =]
lemma move_int_nth {α} (t : BiTape α) (n p : ℤ) :
    (move_int t n).nth p = t.nth (p + n) := by
  unfold move_int
  split <;> grind

@[simp, grind =]
lemma move_int_head {α} (t : BiTape α) (n : ℤ) :
    (move_int t n).head = t.nth n := by
  simp [← nth_zero, move_int_nth]

@[simp, grind =]
lemma move_int_move_int {α} (t : BiTape α) (n₁ n₂ : ℤ) :
  (t.move_int n₁).move_int n₂ = t.move_int (n₁ + n₂) := by
  apply BiTape.ext_nth
  grind

end Move

/--
Write a value under the head of the `BiTape`.
-/
def write {α} (t : BiTape α) (a : Option α) : BiTape α := { t with head := a }

@[simp, grind =]
lemma write_head {α} (t : BiTape α) : t.write t.head = t := by rfl

/--
The space used by a `BiTape` is the number of symbols
between and including the head, and leftmost and rightmost non-blank symbols on the `BiTape`.
-/
@[scoped grind]
def space_used {α} (t : BiTape α) : ℕ := 1 + t.left.length + t.right.length

@[simp, grind =]
lemma space_used_write {α} (t : BiTape α) (a : Option α) :
    (t.write a).space_used = t.space_used := by rfl

lemma space_used_mk₁ {α} (l : List α) :
    (mk₁ l).space_used = max 1 l.length := by
  cases l with
  | nil => simp [mk₁, space_used, nil, StackTape.length_nil]
  | cons h t => simp [mk₁, space_used, StackTape.length_nil, StackTape.length_map_some]; omega

@[simp, grind =]
lemma space_used_defaul {α} : (default : BiTape α).space_used = 1 := by
  simp [space_used, nil, default]

lemma space_used_move {α} (t : BiTape α) (d : Dir) :
    (t.move d).space_used ≤ t.space_used + 1 := by
  cases d <;> grind [move_left, move_right, move,
    space_used, StackTape.length_tail_le, StackTape.length_cons_le]

end BiTape

end Turing
