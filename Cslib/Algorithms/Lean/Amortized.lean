/-
Copyright (c) 2026 Simon Cruanes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Cruanes
-/

module

import Cslib.Init
import Mathlib
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Order.Ring.Int

/-!
# Amortized cost analysis

This complements `TimeM` in the cases where amortized costs are necessary.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Amortized

/-- Physicist method: a potential (lower bound on savings) defined on a
    data structure.
    [Okasaki, *Purely Functional Data Structures*, 1996][okasaki1996] -/
class Potential (φ α : Type*) [CommRing φ] [LinearOrder φ] [IsStrictOrderedRing φ] where
  /-- The potential, a representation of savings accumulated (just like
      potential energy), to be released later. In some functional data
      structures, amortized costs allow some operations to be more expensive
      by "using" potential previously accumulated in cheaper operations. -/
  potential : α → φ

class Op α o where
  applyOp : α → o → TimeM ℕ α

@[simp] def applyOps {α o : Type*} [Op α o] (x : α) (ops : List o)
    : TimeM ℕ α :=
  List.foldlM (fun x op => Op.applyOp x op) x ops

/-- Amortized cost with the physicist's method,
    following Okasaki, chapter 5 -/
def amortizedCost {α o φ : Type*}
    [Op α o] [CommRing φ] [LinearOrder φ] [IsStrictOrderedRing φ] [Potential φ α]
    (x : α) (op : o) : φ :=
  Nat.cast (Op.applyOp x op).time
    + Potential.potential (Op.applyOp x op).ret
    - Potential.potential x

/-- If each operation's cost is bounded by `k`, then the amortized
  cost over a series of operations is bounded by `k * ops.length`. -/
theorem constantAmortizedCostL {α o φ : Type*}
    [CommRing φ] [LinearOrder φ] [IsStrictOrderedRing φ]
    [h_op : Op α o] [h_pot : Potential φ α]
    (k : φ) (h_bounded : ∀ (x : α) (op : o), amortizedCost x op ≤ k)
    (x : α) (ops : List o)
    : (applyOps x ops).time
        + Potential.potential (applyOps x ops).ret - Potential.potential x
      ≤ k * Nat.cast ops.length
    := by
  simp only [applyOps]
  revert x
  induction ops with
  | nil =>
    intro x
    simp only [List.foldlM, TimeM.time_pure, CharP.cast_eq_zero,
      TimeM.ret_pure, zero_add, sub_self,
      List.length_nil, mul_zero, Std.le_refl]
  | cons op ops2 h_ind =>
    intro x
    simp only [amortizedCost] at h_bounded
    simp only [List.foldlM, TimeM.time_bind, Nat.cast_add, TimeM.ret_bind, List.length_cons,
      Nat.cast_one]
    have bound1 := h_bounded x op
    have bound2 := h_ind (Op.applyOp x op).ret
    set applyOpX := (Op.applyOp x op : TimeM ℕ α)
    set applyOps2 := (List.foldlM (fun x op => Op.applyOp x op) (Op.applyOp x op).ret ops2)
    set potX := (Potential.potential x : φ)
    set potOpX := (Potential.potential applyOpX.ret : φ)
    set potOps2 := (Potential.potential applyOps2.ret : φ)
    /- have potOpXPos := (Potential.potentialNonNegative (φ := φ) applyOpX.ret) -/
    ring_nf
    have jfdoit := add_le_add bound1 bound2
    ring_nf at jfdoit
    linarith

end Cslib.Algorithms.Lean.Amortized

end
