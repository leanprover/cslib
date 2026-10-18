/-
Copyright (c) 2026 Vignesh Karri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vignesh Karri
-/

module

public import Cslib.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.Card

/-!
# Boolean functions on the hypercube

A Boolean function is a map `{0,1}ⁿ → {0,1}`, shared across the library as
`Cslib.BooleanFunction` on `Cslib.BitString n`. This file sets up block flips, which are the moves
of sensitivity and block sensitivity, and partial assignments. The complexity measures are built in
`Measures.lean`.

## Main definitions

- `BitString.flipBlock B x`: `x` with every coordinate of `B` flipped.
- `Block n`: a set of coordinates.
- `PartialAssignment n`: a partial assignment, fixing some coordinates and leaving others free.
- `restrict x S`: the partial assignment reading off `x` on the coordinates in `S`.
- `Agrees`: An input is consistent with a partial assignment.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09],
  Chapter 12 (Decision Trees); the notions defined here underpin Sections 12.2 and 12.5.1.
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Cslib

variable {n : ℕ}

namespace BitString

/-! ## Flipping blocks of bits -/

/-- `x` with every coordinate of `B` flipped. -/
def flipBlock (B : Finset (Fin n)) (x : BitString n) : BitString n :=
  fun j => if j ∈ B then !(x j) else x j

/-- Flipping `B` splices the negation of `x` into `x` on `B`. -/
theorem flipBlock_eq_piecewise (B : Finset (Fin n)) (x : BitString n) :
    flipBlock B x = B.piecewise (fun j => !(x j)) x :=
  rfl

@[simp]
theorem flipBlock_apply_of_mem {B : Finset (Fin n)} {x : BitString n} {j : Fin n} (h : j ∈ B) :
    flipBlock B x j = !(x j) := by
  simp [flipBlock, h]

@[simp]
theorem flipBlock_apply_of_notMem {B : Finset (Fin n)} {x : BitString n} {j : Fin n} (h : j ∉ B) :
    flipBlock B x j = x j := by
  simp [flipBlock, h]

/-- Flipping no coordinates does nothing. -/
@[simp]
theorem flipBlock_empty (x : BitString n) : flipBlock ∅ x = x := by
  funext j; simp [flipBlock]

/-- Flipping the same block twice does nothing. -/
@[simp]
theorem flipBlock_flipBlock (B : Finset (Fin n)) (x : BitString n) :
    flipBlock B (flipBlock B x) = x := by
  funext j; by_cases h : j ∈ B <;> simp [flipBlock, h]

/-- Flipping a block is an involution. -/
theorem flipBlock_involutive (B : Finset (Fin n)) : Function.Involutive (flipBlock B) :=
  flipBlock_flipBlock B

/-- Flipping the block `{i}` is flipping the single bit `i`. -/
@[simp]
theorem flipBlock_singleton (i : Fin n) (x : BitString n) :
    flipBlock {i} x = Function.update x i (!x i) := by
  funext j; by_cases h : j = i <;> simp [flipBlock, h]

/-- Flipping `B \ {i}` is flipping `B` and then restoring bit `i ∈ B`. -/
theorem flipBlock_erase {B : Finset (Fin n)} {i : Fin n} (hi : i ∈ B) (x : BitString n) :
    flipBlock (B.erase i) x = Function.update (flipBlock B x) i (x i) := by
  funext j
  by_cases hij : j = i
  · subst hij; simp [flipBlock, hi]
  · simp [flipBlock, hij]

end BitString

namespace QueryComplexity

/-- A block: a set of coordinates. -/
abbrev Block (n : ℕ) : Type := Finset (Fin n)

/-! ## Partial assignments -/

/-- `C i = some b` fixes coordinate `i` to `b`; `C i = none` leaves it free. -/
abbrev PartialAssignment (n : ℕ) : Type := Fin n → Option Bool

/-- The coordinates the partial assignment fixes. -/
def support (C : PartialAssignment n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (C i).isSome)

/-- A coordinate lies in the support if and only if the partial assignment fixes it. -/
@[simp]
lemma mem_support {C : PartialAssignment n} {i : Fin n} :
    i ∈ support C ↔ (C i).isSome := by simp [support]

/-- How many coordinates the partial assignment fixes. -/
def size (C : PartialAssignment n) : ℕ := (support C).card

/-- `x` agrees with `C` when it matches `C` on every fixed coordinate. -/
def Agrees (C : PartialAssignment n) (x : BitString n) : Prop := ∀ i b, C i = some b → x i = b

instance (C : PartialAssignment n) (x : BitString n) : Decidable (Agrees C x) :=
  inferInstanceAs (Decidable (∀ i b, C i = some b → x i = b))

/-- The total assignment reading off every coordinate of `x`. -/
def ofBitString (x : BitString n) : PartialAssignment n := fun i => some (x i)

/-- A total assignment read off `x` is agreed with by `x` alone. -/
@[simp]
theorem agrees_ofBitString_iff {x y : BitString n} : Agrees (ofBitString x) y ↔ y = x := by
  constructor
  · intro h; funext i; exact h i (x i) rfl
  · rintro rfl i b hb; simpa [ofBitString] using hb

/-- Reading off the whole input fixes all `n` coordinates. -/
@[simp]
theorem size_ofBitString (x : BitString n) : size (ofBitString x) = n := by
  simp [size, support, ofBitString]

/-- The partial assignment reading off `x` on the coordinates only in `S`. -/
def restrict (x : BitString n) (S : Finset (Fin n)) : PartialAssignment n :=
  fun i => if i ∈ S then some (x i) else none

/-- An input agrees with `restrict x S` if and only if it matches `x` on `S`. -/
@[simp]
theorem agrees_restrict_iff {x y : BitString n} {S : Finset (Fin n)} :
    Agrees (restrict x S) y ↔ ∀ i ∈ S, y i = x i := by
  constructor
  · intro h i hi
    exact h i (x i) (by simp [restrict, hi])
  · intro h i b hb
    by_cases hi : i ∈ S <;> simp_all [restrict]

/-- `restrict x S` fixes exactly the coordinates in `S`. -/
@[simp]
theorem support_restrict (x : BitString n) (S : Finset (Fin n)) : support (restrict x S) = S := by
  ext i
  by_cases hi : i ∈ S <;> simp [restrict, hi]

/-- A partial assignment consistent with `x` is `x` restricted to its support. -/
theorem eq_restrict_support {C : PartialAssignment n} {x : BitString n} (h : Agrees C x) :
    C = restrict x (support C) := by
  funext i
  cases hC : C i with
  | none => simp [restrict, hC]
  | some b => simp [restrict, hC, h i b hC]

end QueryComplexity

end Cslib
