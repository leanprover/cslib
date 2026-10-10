/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Program
public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite circuit syntax

A finite signature gives computable enumerations of lines and programs of each fixed size.
Their cardinalities count syntax and are independent of any interpretation or carrier.
`Line.card_le` bounds the number of lines when all operation arities are bounded.
For the full basis on a carrier of size `q`, there are `q ^ (q ^ k)` operation tables
and `q` constants. `Line.card_full` counts their possible arguments separately.
-/

@[expose] public section

namespace Cslib.Circuits

universe v
variable {σ : Signature.{v}} [Fintype σ.Op]

instance Line.instFintype (n g : ℕ) : Fintype (Line σ n g) :=
  Fintype.ofEquiv _ (Line.equiv σ n g).symm

instance Program.instFintype (n : ℕ) : (g : ℕ) → Fintype (Program σ n g)
  | 0 => Fintype.ofEquiv PUnit (Program.emptyEquiv σ n).symm
  | g + 1 =>
      letI := Program.instFintype n g
      Fintype.ofEquiv _ (Program.gateEquiv σ n g).symm

/-- For each operation, choose one wire for each of its arguments. -/
theorem Line.card (n g : ℕ) :
    Fintype.card (Line σ n g) = ∑ op : σ.Op, (n + g) ^ σ.Arity op := by
  rw [Fintype.card_congr (Line.equiv σ n g), Fintype.card_sigma]
  simp

/-- A uniform arity bound gives a uniform bound on the number of lines, including when
there are no available wires. -/
theorem Line.card_le (n g r : ℕ) (arity_le : ∀ op, σ.Arity op ≤ r) :
    Fintype.card (Line σ n g) ≤ Fintype.card σ.Op * (n + g + 1) ^ r := by
  rw [Line.card]
  calc
    ∑ op : σ.Op, (n + g) ^ σ.Arity op ≤ ∑ _op : σ.Op, (n + g + 1) ^ r := by
      apply Finset.sum_le_sum
      intro op _
      exact (Nat.pow_le_pow_left (by omega : n + g ≤ n + g + 1) _).trans
        (Nat.pow_le_pow_right (by omega) (arity_le op))
    _ = _ := by simp

/-- There is one empty program, regardless of the signature or number of inputs. -/
@[simp] theorem Program.card_zero (n : ℕ) : Fintype.card (Program σ n 0) = 1 := by
  rw [Fintype.card_congr (Program.emptyEquiv σ n)]
  simp

/-- Choose a prefix program and then its last line. -/
theorem Program.card_succ (n g : ℕ) :
    Fintype.card (Program σ n (g + 1)) =
      Fintype.card (Program σ n g) * Fintype.card (Line σ n g) := by
  rw [Fintype.card_congr (Program.gateEquiv σ n g), Fintype.card_prod]

/-- The line at each position may refer to the inputs and all preceding gates. -/
theorem Program.card (n g : ℕ) :
    Fintype.card (Program σ n g) =
      ∏ j ∈ Finset.range g, ∑ op : σ.Op, (n + j) ^ σ.Arity op := by
  induction g with
  | zero => simp
  | succ g ih => simp [Program.card_succ, ih, Line.card, Finset.prod_range_succ]

namespace FullOp

/-- A full-basis operation is either a `k`-ary function or a constant. -/
def equiv (k : ℕ) (U : Type*) : FullOp k U ≃ (((Fin k → U) → U) ⊕ U) where
  toFun
    | .fn f => .inl f
    | .con c => .inr c
  invFun
    | .inl f => .fn f
    | .inr c => .con c
  left_inv op := by cases op <;> rfl
  right_inv op := by cases op <;> rfl

instance {U : Type*} [Fintype U] [DecidableEq U] {k : ℕ} : Fintype (FullOp k U) :=
  Fintype.ofEquiv _ (equiv k U).symm

instance {U : Type*} [Finite U] {k : ℕ} : Finite (FullOp k U) :=
  Finite.of_equiv _ (equiv k U).symm

/-- Full-basis operations consist of all function tables and all constants. -/
@[simp] theorem card (k : ℕ) (U : Type*) [Fintype U] [DecidableEq U] :
    Fintype.card (FullOp k U) = Fintype.card U ^ (Fintype.card U ^ k) + Fintype.card U := by
  simpa using Fintype.card_congr (equiv k U)

end FullOp

instance {U : Type*} [Fintype U] [DecidableEq U] {k : ℕ} : Fintype (fullSignature k U).Op :=
  inferInstanceAs (Fintype (FullOp k U))

instance {U : Type*} [Finite U] {k : ℕ} : Finite (fullSignature k U).Op :=
  inferInstanceAs (Finite (FullOp k U))

/-- A function table takes `k` wire arguments; a constant takes none. -/
theorem Line.card_full (k n g : ℕ) (U : Type*) [Fintype U] [DecidableEq U] :
    Fintype.card (Line (fullSignature k U) n g) =
      Fintype.card U ^ (Fintype.card U ^ k) * (n + g) ^ k + Fintype.card U := by
  rw [Line.card]
  change (∑ op : FullOp k U, (n + g) ^ (fullSignature k U).Arity op) = _
  rw [← (FullOp.equiv k U).symm.sum_comp]
  simp [FullOp.equiv, fullSignature]

end Cslib.Circuits
