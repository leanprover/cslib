/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.Arith.Defs
import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Ring.Defs

/-! # Complex Multiplication: Correctness and Cost Analysis

A simple example showing how to use `Prog.cost` with variable/parametrized query costs.

We prove that both `complexMulNaive` and `complexMulGauss` correctly compute
complex multiplication when given an honest oracle, and compute their exact
costs under a parametric weight function. The cost theorems hold for *any* oracle
(not just honest ones), because both algorithms are straight-line (no branching
on query results).
-/

open Cslib.Query

public section

namespace Cslib.Query

variable {α : Type}

-- ## Correctness

theorem complexMulNaive_eval_honest [Ring α] (a b c d : α) :
    (complexMulNaive a b c d).eval ArithQuery.honest = (a * c - b * d, a * d + b * c) := by
  simp [complexMulNaive, ArithQuery.doMul, ArithQuery.doSub, ArithQuery.doAdd, ArithQuery.honest]

theorem complexMulGauss_eval_honest [CommRing α] (a b c d : α) :
    (complexMulGauss a b c d).eval ArithQuery.honest = (a * c - b * d, a * d + b * c) := by
  simp [complexMulGauss, ArithQuery.doMul, ArithQuery.doSub, ArithQuery.doAdd, ArithQuery.honest]
  ring

-- ## Exact cost counts

theorem complexMulNaive_cost (oracle : {ι : Type} → ArithQuery α ι → ι)
    (c_add c_mul : Nat) (a b c d : α) :
    (complexMulNaive a b c d).cost oracle (ArithQuery.weight c_add c_mul) =
      4 * c_mul + 2 * c_add := by
  simp [complexMulNaive, ArithQuery.doMul, ArithQuery.doSub, ArithQuery.doAdd, ArithQuery.weight]
  omega

theorem complexMulGauss_cost (oracle : {ι : Type} → ArithQuery α ι → ι)
    (c_add c_mul : Nat) (a b c d : α) :
    (complexMulGauss a b c d).cost oracle (ArithQuery.weight c_add c_mul) =
      3 * c_mul + 5 * c_add := by
  simp [complexMulGauss, ArithQuery.doMul, ArithQuery.doSub, ArithQuery.doAdd, ArithQuery.weight]
  omega

-- ## Crossover: Gauss beats naive when multiplication costs more than 3× addition

theorem gauss_le_naive (c_add c_mul : Nat) (h : 3 * c_add ≤ c_mul) :
    3 * c_mul + 5 * c_add ≤ 4 * c_mul + 2 * c_add := by omega

theorem gauss_le_naive_iff (c_add c_mul : Nat) :
    3 * c_mul + 5 * c_add ≤ 4 * c_mul + 2 * c_add ↔ 3 * c_add ≤ c_mul := by omega

end Cslib.Query

end -- public section
