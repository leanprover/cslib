/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Synthesis
import Mathlib.Data.Fintype.Card

/-!
# Generic synthesis tests

These examples use arbitrary carriers and an infinite arithmetic signature with unbounded
arities. They exercise shared outputs, ordered and unordered folds, and empty constructions.
-/

namespace CslibTests.Synthesis

open Cslib.Circuits

universe v u

example {σ : Signature.{v}} {U : Type u} (I : Interpretation σ U) {n : ℕ} (i : Fin n) :
    ∃ c : Circuit σ n 1, c.Computes I (fun x => x i) ∧ c.size ≤ 0 := by
  have h : Synthesis I (inputs n) {fun x => x i} 0 :=
    Synthesis.of_mem ⟨i, rfl⟩
  exact h.exists_circuit

example {σ : Signature.{v}} {U : Type u} (I : Interpretation σ U) :
    ∃ c : Circuit σ 0 0, c.ComputesFamily I (fun j _ => Fin.elim0 j) ∧ c.size ≤ 0 := by
  have h : Synthesis I (inputs 0) (Set.range fun (j : Fin 0) (_ : Fin 0 → U) => Fin.elim0 j)
      0 := Synthesis.of_subset (by rintro _ ⟨j, rfl⟩; exact Fin.elim0 j)
  exact h.exists_circuit_family

inductive Op where
  | const (value : ℕ)
  | add
  | mul
  | sub
  | total (arity : ℕ)

abbrev signature : Signature where
  Op := Op
  Arity
    | .const _ => 0
    | .add | .mul | .sub => 2
    | .total k => k

def interpretation : Interpretation signature ℕ
  | .const value, _ => value
  | .add, x => x 0 + x 1
  | .mul, x => x 0 * x 1
  | .sub, x => x 0 - x 1
  | .total _, x => ∑ i, x i

private theorem projection {n : ℕ} (i : Fin n) :
    Synthesis interpretation (inputs n) {fun x => x i} 0 :=
  Synthesis.of_mem ⟨i, rfl⟩

private theorem add_available {n : ℕ} (f g : (Fin n → ℕ) → ℕ) :
    Synthesis interpretation {f, g} {fun x => f x + g x} 1 := by
  exact Synthesis.binary (I := interpretation)
    (Synthesis.of_mem (by simp)) (Synthesis.of_mem (by simp)) .add

private theorem sub_available {n : ℕ} (f g : (Fin n → ℕ) → ℕ) :
    Synthesis interpretation {f, g} {fun x => f x - g x} 1 := by
  exact Synthesis.binary (I := interpretation)
    (Synthesis.of_mem (by simp)) (Synthesis.of_mem (by simp)) .sub

example (value : ℕ) :
    ∃ c : Circuit signature 0 1, c.Computes interpretation (fun _ => value) ∧ c.size ≤ 1 :=
  (Synthesis.nullary (I := interpretation) (s := inputs 0) (.const value) rfl).exists_circuit

example (n : ℕ) :
    ∃ c : Circuit signature n 1,
      c.Computes interpretation (fun x => ∑ i, x i) ∧ c.size ≤ 1 := by
  have h := Synthesis.gate_of_syntheses (I := interpretation) (.total n)
    (fun i x => x i) (fun _ => 0) projection
  simpa [interpretation] using h.exists_circuit

private def product (x : Fin 2 → ℕ) : ℕ := x 0 * x 1

private def sharedOutputs (i : Fin 3) (x : Fin 2 → ℕ) : ℕ :=
  if i = 1 then product x + x 0 else product x

-- The product is computed once, used by the sum, and selected twice as an output.
example : ∃ c : Circuit signature 2 3,
    c.ComputesFamily interpretation sharedOutputs ∧ c.size ≤ 2 := by
  have hproduct : Synthesis interpretation (inputs 2) {product} 1 :=
    Synthesis.gate (I := interpretation) .mul (fun i x => x i) (fun i => ⟨i, rfl⟩)
  have hsum : Synthesis interpretation (inputs 2 ∪ {product}) {fun x => product x + x 0} 1 := by
    exact Synthesis.binary (I := interpretation) (s := inputs 2 ∪ {product})
      (Synthesis.of_mem (Set.mem_union_right _ (Set.mem_singleton product)))
      (Synthesis.of_mem (Set.mem_union_left _ ⟨0, rfl⟩)) .add
  have h := hproduct.comp hsum
  have hout : Synthesis interpretation (inputs 2) (Set.range sharedOutputs) 2 :=
    h.mono Set.Subset.rfl (by rintro _ ⟨i, rfl⟩; unfold sharedOutputs; split <;> simp) le_rfl
  exact hout.exists_circuit_family

-- Subtraction is neither commutative nor associative; the list determines the order.
example : ∃ c : Circuit signature 2 1,
    c.Computes interpretation (fun x => x 0 - (x 1 - x 0)) ∧ c.size ≤ 2 := by
  have h := Synthesis.foldr (I := interpretation) (· - ·) 1 sub_available
    ([0, 1] : List (Fin 2)) (projection 0) (fun i _ => projection i)
  simpa using h.exists_circuit

-- A finite-set fold may start from an available, nonconstant seed.
example : ∃ c : Circuit signature 2 1,
    c.Computes interpretation
      (fun x => Finset.univ.fold (· + ·) (x 0) (fun i : Fin 2 => x i)) ∧ c.size ≤ 2 := by
  have h := Synthesis.finset_fold (I := interpretation) (· + ·) 1 add_available
    (Finset.univ : Finset (Fin 2)) (projection 0) (fun i _ => projection i)
  simpa using h.exists_circuit

example : ∃ c : Circuit signature 1 1,
    c.Computes interpretation (fun x => x 0) ∧ c.size ≤ 0 := by
  have h := Synthesis.finset_fold (I := interpretation) (· + ·) 1 add_available
    (∅ : Finset (Fin 1)) (projection 0) (fun i _ => projection i)
  simpa using h.exists_circuit

end CslibTests.Synthesis
