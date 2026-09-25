/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Shannon
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# Generic circuit counting tests

These tests exercise computable syntax enumeration, semantic counting on an infinite carrier,
normalization of distinct symbols with the same interpretation, and empty or nullary signatures.
The Shannon theorem is also instantiated on the NAND basis and a three-valued carrier.
-/

namespace CslibTests.CircuitCounting

open Cslib.Circuits

inductive ArithmeticOp where
  | zero (tag : Bool)
  | add
  deriving DecidableEq, Fintype

abbrev arithmeticSignature : Signature where
  Op := ArithmeticOp
  Arity
    | .zero _ => 0
    | .add => 2

def arithmeticInterpretation : Interpretation arithmeticSignature ℕ
  | .zero _, _ => 0
  | .add, input => input 0 + input 1

-- Syntax enumeration computes even with no input wires and operations of mixed arities.
example : Fintype.card (Line arithmeticSignature 0 0) = 2 := by decide
example : Fintype.card (Line arithmeticSignature 2 1) = 11 := by decide
example : Fintype.card (Program arithmeticSignature 0 2) = 6 := by decide
example : Fintype.card (Circuit arithmeticSignature 0 0 0) = 1 := by decide
example : Fintype.card (Circuit arithmeticSignature 0 0 1) = 0 := by decide

def addition : Circuit arithmeticSignature 2 1 1 where
  program := .gate .empty ⟨.add, fun i => Wire.input i⟩
  outputs := fun _ => Wire.gate 0

example : (fun x => x 0 + x 1) ∈ computableFunctions arithmeticInterpretation 2 1 :=
  (mem_computableFunctions (I := arithmeticInterpretation)).mpr
    ⟨1, le_rfl, addition, fun _ => rfl⟩

def redundant : Circuit arithmeticSignature 0 2 2 where
  program := .gate (.gate .empty ⟨.zero false, Fin.elim0⟩) ⟨.zero true, Fin.elim0⟩
  outputs := Wire.gate

example : ¬ redundant.Irredundant arithmeticInterpretation := by
  intro h
  have : (0 : Fin 2) = 1 := h (by rfl)
  contradiction

-- Normalization preserves all outputs together over the infinite carrier.
example : ∃ k ≤ 2, ∃ c : Circuit arithmeticSignature 0 k 2,
    (∀ x j, c.eval arithmeticInterpretation x j = 0) ∧
      c.Irredundant arithmeticInterpretation := by
  obtain ⟨k, hk, c, hc, hi⟩ := redundant.exists_irredundant arithmeticInterpretation
  refine ⟨k, hk, c, ?_, hi⟩
  intro x j
  rw [hc]
  fin_cases j <;> rfl

abbrev emptySignature : Signature where
  Op := Empty
  Arity := Empty.elim

def emptyInterpretation : Interpretation emptySignature ℕ := fun op => nomatch op

example : Fintype.card (Program emptySignature 1 1) = 0 := by decide

example : (fun x : Fin 1 → ℕ => x 0) ∈ computableFunctions emptyInterpretation 1 0 :=
  (mem_computableFunctions (I := emptyInterpretation)).mpr
    ⟨0, le_rfl, Circuit.id emptySignature 1,
      by simp [Circuit.Computes, funext_iff, Fin.forall_fin_one]⟩

example (s : ℕ) : (computableFunctions emptyInterpretation 0 s).card * s.factorial ≤
    (s + 1) * s ^ s * s := by
  simpa using card_computableFunctions_mul_factorial_le_of_arity_le emptyInterpretation
    0 s 0 (fun op => nomatch op)

abbrev nullarySignature : Signature where
  Op := Unit
  Arity := fun _ => 0

def nullaryInterpretation : Interpretation nullarySignature ℕ := fun _ _ => 0

example (s : ℕ) : (computableFunctions nullaryInterpretation 0 s).card * s.factorial ≤
    (s + 1) * (max s 1) ^ s * s := by
  simpa using card_computableFunctions_mul_factorial_le_of_arity_le nullaryInterpretation
    0 s 0 (fun _ => le_rfl)

abbrev binarySignature : Signature where
  Op := Unit
  Arity := fun _ => 2

def nandInterpretation : Interpretation binarySignature Bool := fun _ x => !(x 0 && x 1)

example : ∃ N : ℕ, ∀ n ≥ N, ∃ f : (Fin n → Bool) → Bool,
    ∀ {g} (c : Circuit binarySignature n g 1),
      c.Computes nandInterpretation (fun x _ => f x) →
        2 ^ n / (n : ℝ) < (c.size : ℝ) := by
  simpa [Nat.card_eq_fintype_card] using
    Shannon.exists_hard_function nandInterpretation (fun _ => le_rfl)

def ternaryInterpretation : Interpretation binarySignature (Fin 3) := fun _ x => x 0 + x 1

example : ∃ N : ℕ, ∀ n ≥ N, ∃ f : (Fin n → Fin 3) → Fin 3,
    ∀ {g} (c : Circuit binarySignature n g 1),
      c.Computes ternaryInterpretation (fun x _ => f x) →
        3 ^ n / (n : ℝ) < (c.size : ℝ) := by
  simpa [Nat.card_eq_fintype_card] using
    Shannon.exists_hard_function ternaryInterpretation (fun _ => le_rfl)

end CslibTests.CircuitCounting
