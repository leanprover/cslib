/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Simulation

import Mathlib.Data.Fintype.Pi

/-!
# Circuits over the full basis

The full basis contains constants and all operations of a fixed arity. A constant can be
synthesized with one gate. In the binary full basis, applying any binary operation to
functions synthesized with budgets `a` and `b` takes at most `a + b + 1` gates.
Both constructions preserve all previously available functions.

More generally, `Synthesis.full_gate` applies an operation of arity at most `k` to
available functions with one gate. `Synthesis.full_gate_of_syntheses` first constructs
the arguments, retaining their intermediate values, and then applies the operation.

The full basis of arity `k` simulates any interpretation whose operations have arity at most
`k`, using at most one gate per operation. Constants are handled separately so this also
applies when `k = 0`, without assuming the carrier is inhabited.

On a finite carrier, every full basis of arity at least two is functionally complete.
The binary construction tests each input tuple and combines the prescribed values;
simulation transfers completeness to larger arities.
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
    Synthesis (fullInterpretation (k := 2)) s {fun x => op (f x) (g x)} (a + b + 1) :=
  hf.binary hg (.fn fun x => op (x 0) (x 1))

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

private theorem exists_full_synthesis_point [DecidableEq U]
    (value default : U) (point : Fin n → U) :
    ∃ cost, Synthesis (fullInterpretation (k := 2)) (inputs n)
      {fun x => if x = point then value else default} cost := by
  classical
  have step (indices : Finset (Fin n)) :
      ∃ cost, Synthesis (fullInterpretation (k := 2)) (inputs n)
        {fun x => if ∀ i ∈ indices, x i = point i then value else default} cost := by
    induction indices using Finset.induction_on with
    | empty => exact ⟨1, by simpa using Synthesis.full_const value⟩
    | @insert i indices hi ih =>
      obtain ⟨cost, hcost⟩ := ih
      have hinput : Synthesis (fullInterpretation (k := 2)) (inputs n)
          {fun x : Fin n → U => x i} 0 :=
        Synthesis.of_mem ⟨i, rfl⟩
      exact ⟨_, by simpa [ite_and] using
        hinput.full_binary hcost (fun v acc => if v = point i then acc else default)⟩
  simpa [funext_iff] using step Finset.univ

private theorem exists_full_synthesis_finset [DecidableEq U]
    (f : (Fin n → U) → U) (default : U)
    (tuples : Finset (Fin n → U)) :
    ∃ cost, Synthesis (fullInterpretation (k := 2)) (inputs n)
      {fun x => if x ∈ tuples then f x else default} cost := by
  classical
  induction tuples using Finset.induction_on with
  | empty => exact ⟨1, by simpa using Synthesis.full_const default⟩
  | @insert point tuples hp ih =>
    obtain ⟨a, ha⟩ := exists_full_synthesis_point (f point) default point
    obtain ⟨b, hb⟩ := ih
    refine ⟨a + b + 1, ?_⟩
    convert ha.full_binary hb (fun v acc => if v = default then acc else v) using 1
    congr 1
    funext x
    by_cases hx : x = point <;> simp [hx, hp]

private theorem fullInterpretation_isComplete_two [Finite U] :
    (fullInterpretation (k := 2) (Carrier := U)).IsComplete where
  exists_computes_single {n} f := by
    classical
    cases isEmpty_or_nonempty U with
    | inl h =>
      let := h
      cases n with
      | zero => exact isEmptyElim (f Fin.elim0)
      | succ n => exact ⟨Circuit.wiring _ (fun _ => 0), fun x => isEmptyElim (x 0)⟩
    | inr h =>
      let := Fintype.ofFinite U
      obtain ⟨cost, hcost⟩ := exists_full_synthesis_finset f (Classical.choice h) Finset.univ
      simpa using hcost.exists_circuit.imp fun _ hc => hc.1

/-- Every full basis of arity at least two is complete on a finite carrier. -/
theorem fullInterpretation_isComplete [Finite U] (hk : 2 ≤ k) :
    (fullInterpretation (k := k) (Carrier := U)).IsComplete := by
  let := fullInterpretation_isComplete_two (U := U)
  apply (fullInterpretation_simulates (fullInterpretation (k := 2) (Carrier := U)) ?_).isComplete
  intro op
  cases op with
  | fn _ => exact hk
  | con _ => exact Nat.zero_le _

/-- Full bases with at least two arguments are complete on finite carriers. -/
instance [Finite U] : (fullInterpretation (k := k + 2) (Carrier := U)).IsComplete :=
  fullInterpretation_isComplete (by lia)

end Cslib.Circuits
