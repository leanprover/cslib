/-
Copyright (c) 2026 Simon Cruanes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Cruanes
-/

module

import Cslib.Init
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
  /-- non-negative potential. Initial potential should be 0.
      [Okasaki, *Purely Functional Data Structures*, 1996][okasaki1996] -/
  potential : α → Nat

class Op α o where
  applyOp : α → o → TimeM ℕ α

@[simp] def applyOps {α o : Type u} [Op α o] (ops : List o) (x : α)
    : TimeM ℕ α :=
  List.foldlM (fun x op => Op.applyOp x op) x ops

/-- Amortized cost with the physicist's method,
    following Okasaki, chapter 5 -/
def amortizedCost {α o : Type*} [Op α o] [Potential α] (x : α) (op : o) : ℕ :=
  (Op.applyOp x op).time + Potential.potential (Op.applyOp x op).ret - Potential.potential x

end Cslib.Algorithms.Lean.Amortized

end
