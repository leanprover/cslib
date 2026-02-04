/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.URM.Execution

/-! # URM-Computable Functions

This file defines the notion of URM-computability for partial functions on natural numbers.

## Main definitions

- `URM.Computes`: A program computes a given partial function.
- `URM.Computable`: A partial function is URM-computable if there exists a URM program that
  computes it.

## Implementation notes

Inputs are provided in registers 0, 1, ..., n-1 and output is read from register 0.
-/

@[expose] public section

namespace Cslib.URM

/-- A program `p` computes a partial function `f : (Fin n → ℕ) → Part ℕ` if for any input,
`eval p inputs = f inputs` as partial values. This captures both:
- The program halts iff the function is defined on that input
- When both are defined, the program's output equals the function's value

Note: Inputs are provided in registers 0, 1, ..., n-1 and output is read from register 0. -/
def Computes (n : ℕ) (p : Program) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∀ inputs : Fin n → ℕ, eval p (List.ofFn inputs) = f inputs

/-- A partial function `f : (Fin n → ℕ) → Part ℕ` is URM-computable if there exists a URM program
that computes it. -/
def Computable (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∃ p : Program, Computes n p f

end Cslib.URM

end
