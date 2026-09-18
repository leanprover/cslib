/-
Copyright (c) 2026 Vignesh Karri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vignesh Karri
-/

module

public import Cslib.Init
public import Mathlib.Data.Fintype.Card

/-!
# Boolean functions on the hypercube

A Boolean function is a map `{0,1}ⁿ → {0,1}`. This file sets up the boolean hypercube, bit and block
flips, and partial assignments. The complexity measures are built in
`Measures.lean` and `DecisionTree.lean`.

## Main definitions

- `Cube n`: bit strings of length `n`, i.e. `Fin n → Bool`.
- `BoolFunc n`: Boolean functions `Cube n → Bool`.
- `Block n`: a set of coordinates.
- `flipBit`, `flipBlock`: flipping one coordinate, or every coordinate of a block.
- `Assignment n`: a partial assignment, fixing some coordinates and leaving others free.
- `Agrees`: An input is consistent with a partial assignment.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09],
  Chapter 12 (Decision Trees); the notions defined here underpin Sections 12.2 and 12.5.1.
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Cslib.QueryComplexity

variable {n : ℕ}

/-- Bit string of length `n`. -/
abbrev Cube (n : ℕ) : Type := Fin n → Bool

/-- `f : {0,1}ⁿ → {0,1}`. -/
abbrev BoolFunc (n : ℕ) : Type := Cube n → Bool

/-- A block: a set of coordinates. -/
abbrev Block (n : ℕ) : Type := Finset (Fin n)

/-- `x` with coordinate `i` flipped. Phrased with `Function.update` so that the
whole `Function.update` simp set (`update_self`, `update_of_ne`, `update_idem`,
`update_eq_self`, …) applies to it. -/
def flipBit (x : Cube n) (i : Fin n) : Cube n := Function.update x i (!x i)

/-- The flipped coordinate reads back negated. -/
@[simp]
lemma flipBit_self (x : Cube n) (i : Fin n) : flipBit x i i = !x i :=
  Function.update_self ..

/-- Every other coordinate is left alone. -/
@[simp]
lemma flipBit_of_ne {x : Cube n} {i j : Fin n} (h : j ≠ i) : flipBit x i j = x j :=
  Function.update_of_ne h ..

/-- `x` with every coordinate of `B` flipped. -/
def flipBlock (x : Cube n) (B : Block n) : Cube n :=
  fun j => if j ∈ B then !(x j) else x j

/-! ## Flipping lemmas -/

/-- Flipping the same bit twice does nothing. -/
@[simp]
lemma flipBit_flipBit (x : Cube n) (i : Fin n) : flipBit (flipBit x i) i = x := by
  simp [flipBit]

/-- Flipping no coordinates does nothing. -/
@[simp]
lemma flipBlock_empty (x : Cube n) : flipBlock x ∅ = x := by
  funext j; simp [flipBlock]

/-- Flipping a block is an involution. -/
@[simp]
lemma flipBlock_flipBlock (x : Cube n) (B : Block n) :
    flipBlock (flipBlock x B) B = x := by
  funext j; by_cases h : j ∈ B <;> simp [flipBlock, h]

/-- Flipping the block `{i}` is flipping the single bit `i`. -/
@[simp]
lemma flipBlock_singleton (x : Cube n) (i : Fin n) :
    flipBlock x {i} = flipBit x i := by
  funext j; by_cases h : j = i <;> simp [flipBlock, flipBit, h]

/-- Flipping `B` then flipping `i ∈ B` back is flipping `B \ {i}`. -/
lemma flipBlock_erase (x : Cube n) (B : Block n) {i : Fin n} (hi : i ∈ B) :
    flipBlock x (B.erase i) = flipBit (flipBlock x B) i := by
  funext j
  by_cases hij : j = i
  · subst hij; simp [flipBlock, flipBit, hi]
  · simp [flipBit, flipBlock, hij]

/-! ## Partial assignments -/

/-- `C i = some b` fixes coordinate `i` to `b`; `C i = none` leaves it free. -/
abbrev Assignment (n : ℕ) : Type := Fin n → Option Bool

/-- The coordinates the assignment fixes. -/
def support (C : Assignment n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (C i).isSome)

/-- A coordinate lies in the support exactly when the assignment fixes it. -/
@[simp]
lemma mem_support {C : Assignment n} {i : Fin n} :
    i ∈ support C ↔ (C i).isSome := by simp [support]

/-- How many coordinates the assignment fixes. -/
def size (C : Assignment n) : ℕ := (support C).card

/-- `x` agrees with `C` when it matches `C` on every fixed coordinate. -/
def Agrees (C : Assignment n) (x : Cube n) : Prop := ∀ i b, C i = some b → x i = b

instance (C : Assignment n) (x : Cube n) : Decidable (Agrees C x) :=
  inferInstanceAs (Decidable (∀ i b, C i = some b → x i = b))

/-- The total assignment reading off every coordinate of `x`. -/
def ofCube (x : Cube n) : Assignment n := fun i => some (x i)

/-- A total assignment read off `x` is agreed with by `x` alone. -/
@[simp]
theorem agrees_ofCube_iff {x y : Cube n} : Agrees (ofCube x) y ↔ y = x := by
  constructor
  · intro h; funext i; exact h i (x i) rfl
  · rintro rfl i b hb; simpa [ofCube] using hb

/-- Reading off the whole input fixes all `n` coordinates. -/
@[simp]
theorem size_ofCube (x : Cube n) : size (ofCube x) = n := by
  simp [size, support, ofCube]

end Cslib.QueryComplexity
