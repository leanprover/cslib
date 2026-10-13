/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Program
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum

/-!
# Finite circuit syntax

A finite signature gives finitely many lines and programs of each fixed size.
Their cardinalities count syntax and are independent of any interpretation or carrier.
`Line.card_le` bounds the number of lines when all operation arities are bounded.
For the full basis on a carrier of size `q`, there are `q ^ (q ^ k)` operation tables
and `q` constants. `Line.card_full` counts their possible arguments separately.
-/

@[expose] public section

namespace Cslib.Circuits

universe v
variable {σ : Signature.{v}} [Finite σ.Op]

instance Line.instFinite (n g : ℕ) : Finite (Line σ n g) :=
  Finite.of_equiv _ (Line.equiv σ n g).symm

instance Program.instFinite (n : ℕ) : (g : ℕ) → Finite (Program σ n g)
  | 0 => Finite.of_equiv PUnit (Program.emptyEquiv σ n).symm
  | g + 1 =>
      letI := Program.instFinite n g
      Finite.of_equiv _ (Program.gateEquiv σ n g).symm

/-- For each operation, choose one wire for each of its arguments. -/
theorem Line.card (n g : ℕ) :
    Nat.card (Line σ n g) = ∑ᶠ op : σ.Op, (n + g) ^ σ.Arity op := by
  let := Fintype.ofFinite σ.Op
  rw [Nat.card_congr (Line.equiv σ n g), Nat.card_sigma, finsum_eq_sum_of_fintype]
  simp [Nat.card_eq_fintype_card]

/-- A uniform arity bound gives a uniform bound on the number of lines, including when
there are no available wires. -/
theorem Line.card_le (n g r : ℕ) (arity_le : ∀ op, σ.Arity op ≤ r) :
    Nat.card (Line σ n g) ≤ Nat.card σ.Op * (n + g + 1) ^ r := by
  let := Fintype.ofFinite σ.Op
  rw [Line.card, finsum_eq_sum_of_fintype]
  calc
    ∑ op : σ.Op, (n + g) ^ σ.Arity op ≤ ∑ _op : σ.Op, (n + g + 1) ^ r := by
      apply Finset.sum_le_sum
      intro op _
      exact (Nat.pow_le_pow_left (by lia : n + g ≤ n + g + 1) _).trans
        (Nat.pow_le_pow_right (by lia) (arity_le op))
    _ = _ := by simp [Nat.card_eq_fintype_card]

omit [Finite σ.Op] in
/-- There is one empty program, regardless of the signature or number of inputs. -/
@[simp] theorem Program.card_zero (n : ℕ) : Nat.card (Program σ n 0) = 1 := by
  rw [Nat.card_congr (Program.emptyEquiv σ n)]
  simp

omit [Finite σ.Op] in
/-- Choose a prefix program and then its last line. -/
theorem Program.card_succ (n g : ℕ) :
    Nat.card (Program σ n (g + 1)) =
      Nat.card (Program σ n g) * Nat.card (Line σ n g) := by
  rw [Nat.card_congr (Program.gateEquiv σ n g), Nat.card_prod]

/-- The line at each position may refer to the inputs and all preceding gates. -/
theorem Program.card (n g : ℕ) :
    Nat.card (Program σ n g) =
      ∏ j ∈ Finset.range g, ∑ᶠ op : σ.Op, (n + j) ^ σ.Arity op := by
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

instance {U : Type*} [Finite U] {k : ℕ} : Finite (FullOp k U) :=
  Finite.of_equiv _ (equiv k U).symm

/-- Full-basis operations consist of all function tables and all constants. -/
@[simp] theorem card (k : ℕ) (U : Type*) [Finite U] :
    Nat.card (FullOp k U) = Nat.card U ^ (Nat.card U ^ k) + Nat.card U := by
  simpa [Nat.card_fun] using Nat.card_congr (equiv k U)

end FullOp

instance {U : Type*} [Finite U] {k : ℕ} : Finite (fullSignature k U).Op :=
  inferInstanceAs (Finite (FullOp k U))

/-- A function table takes `k` wire arguments; a constant takes none. -/
theorem Line.card_full (k n g : ℕ) (U : Type*) [Finite U] :
    Nat.card (Line (fullSignature k U) n g) =
      Nat.card U ^ (Nat.card U ^ k) * (n + g) ^ k + Nat.card U := by
  classical
  let := Fintype.ofFinite U
  rw [Line.card]
  change (∑ᶠ op : FullOp k U, (n + g) ^ (fullSignature k U).Arity op) = _
  rw [← finsum_comp_equiv (FullOp.equiv k U).symm, finsum_eq_sum_of_fintype]
  simp [FullOp.equiv, fullSignature, Nat.card_eq_fintype_card]

end Cslib.Circuits
