/-
Copyright (c) 2026 Simon Cruanes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Cruanes
-/

module

import Cslib.Init
import Mathlib
public import Cslib.Algorithms.Lean.TimeM

/-!
# Amortized cost analysis

This complements `TimeM` in the cases where amortized costs are necessary.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Amortized

/-- Physicist method: a potential (lower bound on savings) defined on a
    data structure -/
class Potential α where
  /-- Initial potential should be 0.
      [Okasaki, *Purely Functional Data Structures*, 1996][okasaki1996] -/
  potential : α → Nat

class Op α o where
  applyOp : α → o → TimeM ℕ α

@[simp] def applyOps {α o : Type*} [Op α o] (x : α) (ops : List o)
    : TimeM ℕ α :=
  List.foldlM (fun x op => Op.applyOp x op) x ops

def triples {α o : Type*} [Op α o] (x : α) (ops : List o) : List (α × o) × α :=
  match ops with
  | [] => ([], x)
  | o :: ops2 =>
    let ⟨ x2, _cost ⟩ := Op.applyOp x o
    let ⟨ pairs, final ⟩ := triples x2 ops2
    ((x2, o) :: pairs, final)

/-- Amortized cost with the physicist's method,
    following Okasaki, chapter 5 -/
def amortizedCost {α o : Type*} [Op α o] [Potential α]
    (x : α) (op : o) : ℕ :=
  (Op.applyOp x op).time
    + Potential.potential (Op.applyOp x op).ret
    - Potential.potential x

def amortizedCostL {α o : Type*} [Op α o] [Potential α]
    (x : α) (ops : List o) : ℕ :=
  (applyOps x ops).time
    + Potential.potential (applyOps x ops).ret
    - Potential.potential x

/-- If each operation's cost is bounded by `k`, then the amortized
  cost over a series of operations is bounded by `k * ops.length`. -/
theorem constantAmortizedCostL {α o : Type*}
    [h_op : Op α o] [h_pot : Potential α]
    (k : ℕ) (h_bounded : ∀ (x : α) (op : o), amortizedCost x op ≤ k)
    (x : α) (ops : List o)
    : amortizedCostL x ops ≤ k * ops.length
    := by
  simp only [amortizedCostL, applyOps, tsub_le_iff_right]
  revert x
  induction ops with
  | nil => simp [List.foldlM]
  | cons op ops2 h_ind =>
    intro x
    simp only [amortizedCost, tsub_le_iff_right] at h_bounded
    simp [List.foldlM, List.length_cons]
    have bound1 := h_bounded x op
    have bound2 := h_ind (Op.applyOp x op).ret
    linarith

end Cslib.Algorithms.Lean.Amortized

end
