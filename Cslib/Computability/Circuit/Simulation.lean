/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Composition

/-!
# Simulation between circuit bases with gate budgets

`J.Simulates I` means that every operation of `I` can be computed by a circuit over `J`.
`J.SimulatesWithCost I cost` also bounds the number of gates used for each operation.
Replacing each gate of a program preserves all input and intermediate wire values, with
total gate count at most `Program.cost`. The interpretations share a carrier, but their
signatures and gate arities may differ. A budget may be zero when wiring suffices.
-/

@[expose] public section

namespace Cslib.Circuits

universe v w u

variable {σ : Signature.{v}} {τ : Signature.{w}} {U : Type u}
variable {I : Interpretation σ U} {J : Interpretation τ U} {n g : ℕ}

/-- `J` simulates `I` if it can compute every primitive operation of `I`. -/
def Interpretation.Simulates (J : Interpretation τ U) (I : Interpretation σ U) : Prop :=
  ∀ op : σ.Op, ∃ c : Circuit τ (σ.Arity op) 1, c.Computes J (single (I op))

/-- A simulation with a gate budget for each primitive operation. -/
def Interpretation.SimulatesWithCost (J : Interpretation τ U) (I : Interpretation σ U)
    (cost : σ.Op → ℕ) : Prop :=
  ∀ op : σ.Op, ∃ c : Circuit τ (σ.Arity op) 1,
    c.Computes J (single (I op)) ∧ c.size ≤ cost op

theorem Interpretation.SimulatesWithCost.simulates {cost : σ.Op → ℕ}
    (h : J.SimulatesWithCost I cost) : J.Simulates I :=
  fun op => (h op).imp fun _ hc => hc.1

/-- The sum of per-operation budgets along a straight-line program. -/
def Program.cost {g : ℕ} (p : Program σ n g) (cost : σ.Op → ℕ) : ℕ :=
  match p with
  | .empty => 0
  | .gate p line => p.cost cost + cost line.op

@[simp] theorem Program.cost_empty (cost : σ.Op → ℕ) :
    (Program.empty : Program σ n 0).cost cost = 0 := rfl

@[simp] theorem Program.cost_gate (p : Program σ n g) (line : Line σ n g)
    (cost : σ.Op → ℕ) : (p.gate line).cost cost = p.cost cost + cost line.op := rfl

@[simp] theorem Program.cost_const (p : Program σ n g) (b : ℕ) :
    p.cost (fun _ => b) = b * g := by
  induction p <;> simp_all [Nat.mul_add]

/-- Replace each gate of `p` within its budget. The renaming `ρ` fixes the input wires and
identifies every intermediate value with a wire of the resulting program `q`. -/
theorem Program.exists_simulationWithCost (p : Program σ n g) (cost : σ.Op → ℕ)
    (h : J.SimulatesWithCost I cost) :
    ∃ k : ℕ, ∃ q : Program τ n k, ∃ ρ : Wire.Renaming n g k,
      k ≤ p.cost cost ∧ ∀ x : Fin n → U, q.trace J x ∘ ρ = p.trace I x := by
  induction p with
  | empty =>
    exact ⟨0, .empty, .id, le_rfl, fun _ => funext fun w => by
      rw [Function.comp_apply, Wire.Renaming.id_apply]; rfl⟩
  | @gate g p line ih =>
    obtain ⟨k, q, ρ, hcost, hρ⟩ := ih
    obtain ⟨c, hc, hsize⟩ := h line.op
    let feed := ρ ∘ line.wires
    let prior : Wire.Renaming n g (k + c.size) := ⟨fun j => (ρ.gates j).castAdd c.size⟩
    refine ⟨k + c.size, q.append feed c.program,
      prior.skipLast (Program.appendedWire feed (c.outputs 0)), Nat.add_le_add hcost hsize, ?_⟩
    intro x
    funext w
    dsimp only [Function.comp_apply]
    refine Wire.lastCases ?_ (fun w => ?_) w
    · simp only [Wire.Renaming.apply_gate, Wire.Renaming.skipLast_gates_last]
      rw [Program.trace_append_appendedWire]
      change c.eval J _ 0 = _
      rw [hc]
      change I line.op ((q.trace J x ∘ ρ) ∘ line.wires) = _
      rw [hρ x]
      exact (Program.eval_gate_last p line I x).symm
    · rw [Wire.Renaming.skipLast_castSucc, Program.trace_gate_castSucc]
      have hold := (Program.trace_append_castAdd q feed J x c.program (ρ w)).trans
        (congrFun (hρ x) w)
      cases w <;> exact hold

end Cslib.Circuits
