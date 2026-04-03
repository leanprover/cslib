/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Cslib.Algorithms.Lean.Query.Prog

/-! # Arithmetic Queries and Complex Multiplication

A simple example showing how to use `Prog.cost` with variable/parametrized query costs.

`ArithQuery α` supports addition, subtraction, and multiplication, each with
independently parametrized costs. Complex number multiplication provides a toy example
where two algorithms (naive and Gauss's trick) trade multiplications for additions,
and the optimal choice depends on the cost ratio.
-/

open Cslib.Query

public section

namespace Cslib.Query

/-- Arithmetic queries: addition, subtraction, and multiplication. -/
inductive ArithQuery (α : Type) : Type → Type where
  | add (a b : α) : ArithQuery α α
  | sub (a b : α) : ArithQuery α α
  | mul (a b : α) : ArithQuery α α

namespace ArithQuery

@[expose] def doAdd (a b : α) : Prog (ArithQuery α) α := .liftBind (.add a b) .pure
@[expose] def doSub (a b : α) : Prog (ArithQuery α) α := .liftBind (.sub a b) .pure
@[expose] def doMul (a b : α) : Prog (ArithQuery α) α := .liftBind (.mul a b) .pure

/-- An honest oracle interprets arithmetic queries using the actual ring operations. -/
@[expose] def honest [Add α] [Sub α] [Mul α] {ι : Type} : ArithQuery α ι → ι
  | .add a b => a + b
  | .sub a b => a - b
  | .mul a b => a * b

/-- Weighted cost model for arithmetic queries. Subtraction costs the same as addition
    (both are linear-time on bignums). -/
@[expose] def weight (c_add c_mul : Nat) {ι : Type} : ArithQuery α ι → Nat
  | .add _ _ => c_add
  | .sub _ _ => c_add
  | .mul _ _ => c_mul

end ArithQuery

/-- Naive complex multiplication: `(a + bi)(c + di) = (ac - bd) + (ad + bc)i`.
    Uses 4 multiplications, 1 subtraction, 1 addition. -/
@[expose] def complexMulNaive (a b c d : α) : Prog (ArithQuery α) (α × α) := do
  let ac ← ArithQuery.doMul a c
  let bd ← ArithQuery.doMul b d
  let ad ← ArithQuery.doMul a d
  let bc ← ArithQuery.doMul b c
  let real ← ArithQuery.doSub ac bd
  let imag ← ArithQuery.doAdd ad bc
  pure (real, imag)

/-- Gauss's trick for complex multiplication: computes `(a+b)(c+d)` to save one
    multiplication, at the cost of extra additions and subtractions.
    Uses 3 multiplications, 2 subtractions, 2 additions. -/
@[expose] def complexMulGauss (a b c d : α) : Prog (ArithQuery α) (α × α) := do
  let ac ← ArithQuery.doMul a c
  let bd ← ArithQuery.doMul b d
  let apb ← ArithQuery.doAdd a b
  let cpd ← ArithQuery.doAdd c d
  let abcd ← ArithQuery.doMul apb cpd
  let real ← ArithQuery.doSub ac bd
  let imag ← ArithQuery.doSub abcd (← ArithQuery.doAdd ac bd)
  pure (real, imag)

end Cslib.Query

end -- public section
