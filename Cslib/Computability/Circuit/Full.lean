/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Simulation

/-!
# Synthesis and simulation over the full basis

The full basis contains constants and all operations of a fixed arity. A constant can be
synthesized with one gate. In the binary full basis, applying any binary operation to
functions synthesized with budgets `a` and `b` takes at most `a + b + 1` gates.
Both constructions preserve all previously available functions.

The full basis of arity `k` simulates any interpretation whose operations have arity at most
`k`, using at most one gate per operation. Constants are handled separately so this also
applies when `k = 0`, without assuming the carrier is inhabited.
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
  by_cases hzero : σ.Arity op = 0
  · let : IsEmpty (Fin (σ.Arity op)) := ⟨fun i => (Fin.cast hzero i).elim0⟩
    convert! (Synthesis.full_const (k := k) (n := σ.Arity op)
      (s := inputs _) (I op isEmptyElim)).exists_circuit
  · let : NeZero (σ.Arity op) := ⟨hzero⟩
    simpa [fullInterpretation] using
      (Synthesis.gate (I := fullInterpretation (k := k)) (s := inputs (σ.Arity op))
        (.fn fun x => I op (fun i => x (Fin.castLE (h op) i)))
        (fun i x => x (Fin.ofNat _ i.val)) (fun i => ⟨_, rfl⟩)).exists_circuit

/-- The full basis simulates any interpretation whose operations have arity at most `k`. -/
theorem fullInterpretation_simulates {σ : Signature.{v}} (I : Interpretation σ U)
    (h : ∀ op, σ.Arity op ≤ k) : (fullInterpretation (k := k)).Simulates I :=
  (fullInterpretation_simulatesWithCost I h).simulates

end Cslib.Circuits
