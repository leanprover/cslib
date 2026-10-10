/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Simulation

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# Synthesis and simulation over the full basis

The full basis of arity `k` contains every constant and every operation with `k` arguments.
Each takes one gate, and so does every operation with at most `k` arguments: a nullary
operation is a constant, and other operations repeat their arguments to fill all `k`
positions. Applying such an operation to `r` functions synthesized with budgets `cost i`
therefore takes at most `∑ i, cost i + 1` gates. `Synthesis.full_binary` states the binary
case with two separate budgets. All constructions preserve previously available functions.

Consequently, the full basis of arity `k` simulates any interpretation whose operations have
arity at most `k`, replacing each operation by one gate. This includes nullary operations and
the case `k = 0`, and needs no assumption on the carrier.
-/

@[expose] public section

namespace Cslib.Circuits

universe v u

variable {U : Type u} {k n a b : ℕ} {s : Set ((Fin n → U) → U)}

namespace Synthesis

/-- A constant can be synthesized with one gate of the full basis. -/
theorem full_const (value : U) :
    Synthesis (fullInterpretation (k := k)) s {fun _ => value} 1 :=
  nullary (I := fullInterpretation (k := k)) (.con value) rfl

/-- Apply any operation with at most `k` arguments to available functions using one gate.
Nullary operations use a constant gate; other operations pad their arguments by repetition. -/
theorem full_gate {r : ℕ} (hr : r ≤ k) (op : (Fin r → U) → U)
    (args : Fin r → (Fin n → U) → U) (hargs : ∀ i, args i ∈ s) :
    Synthesis (fullInterpretation (k := k)) s {fun x => op (fun i => args i x)} 1 := by
  by_cases hzero : r = 0
  · subst r
    convert! full_const (k := k) (s := s) (op Fin.elim0)
  · let : NeZero r := ⟨hzero⟩
    simpa [fullInterpretation] using
      (gate (I := fullInterpretation (k := k)) (s := s)
        (.fn fun x => op (fun i => x (Fin.castLE hr i)))
        (fun i => args (Fin.ofNat r i.val)) (fun i => hargs _))

/-- Construct the arguments of an operation of arity at most `k`, then apply it with one
further gate. All functions computed while constructing the arguments remain available. -/
theorem full_gate_of_syntheses {r : ℕ} (hr : r ≤ k) (op : (Fin r → U) → U)
    (args : Fin r → (Fin n → U) → U) (cost : Fin r → ℕ)
    (h : ∀ i, Synthesis (fullInterpretation (k := k)) s {args i} (cost i)) :
    Synthesis (fullInterpretation (k := k)) s {fun x => op (fun i => args i x)}
      ((∑ i, cost i) + 1) :=
  (family args cost h).trans (full_gate hr op args (fun i => Set.mem_union_right _ ⟨i, rfl⟩))

/-- Apply any binary operation to synthesized functions in the binary full basis. -/
theorem full_binary {f g : (Fin n → U) → U}
    (hf : Synthesis (fullInterpretation (k := 2)) s {f} a)
    (hg : Synthesis (fullInterpretation (k := 2)) s {g} b) (op : U → U → U) :
    Synthesis (fullInterpretation (k := 2)) s {fun x => op (f x) (g x)} (a + b + 1) := by
  simpa [Fin.sum_univ_two] using full_gate_of_syntheses le_rfl (fun v => op (v 0) (v 1))
    ![f, g] ![a, b] (Fin.forall_fin_two.mpr ⟨hf, hg⟩)

end Synthesis

/-- The full basis simulates operations of arity at most `k` with a budget of one gate each. -/
theorem fullInterpretation_simulatesWithCost {σ : Signature.{v}} (I : Interpretation σ U)
    (h : ∀ op, σ.Arity op ≤ k) :
    (fullInterpretation (k := k)).SimulatesWithCost I (fun _ => 1) := by
  intro op
  exact (Synthesis.full_gate (s := inputs _) (h op) (I op)
    (fun i x => x i) (fun i => ⟨i, rfl⟩)).exists_circuit

/-- The full basis simulates any interpretation whose operations have arity at most `k`. -/
theorem fullInterpretation_simulates {σ : Signature.{v}} (I : Interpretation σ U)
    (h : ∀ op, σ.Arity op ≤ k) : (fullInterpretation (k := k)).Simulates I :=
  (fullInterpretation_simulatesWithCost I h).simulates

end Cslib.Circuits
