/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Complexity

/-!
# Simulation between circuit bases with gate budgets

`J.Simulates I` means that every operation of `I` can be computed by a circuit over `J`.
`J.SimulatesWithCost I cost` also bounds the number of gates used for each operation.
Replacing each gate of a program preserves all input and intermediate wire values, with
total gate count at most `Program.cost`. The interpretations share a carrier, but their
signatures and gate arities may differ. A budget may be zero when wiring suffices.

Gate replacement yields equivalent circuits and preserves computation on any support.
Simulations compose, multiplying uniform gate budgets, and transfer functional completeness
from the simulated basis to the simulating basis.
-/

@[expose] public section

namespace Cslib.Circuits

universe v w z u

variable {σ : Signature.{v}} {τ : Signature.{w}} {U : Type u}
variable {I : Interpretation σ U} {J : Interpretation τ U} {n g : ℕ}
variable {υ : Signature.{z}} {K : Interpretation υ U} {m : ℕ}

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

/-- Replace the gates of a program, preserving every input and intermediate value. -/
theorem Program.exists_simulation (p : Program σ n g) (h : J.Simulates I) :
    ∃ k : ℕ, ∃ q : Program τ n k, ∃ ρ : Wire.Renaming n g k,
      ∀ x : Fin n → U, q.trace J x ∘ ρ = p.trace I x := by
  choose gate hgate using h
  obtain ⟨k, q, ρ, _, hρ⟩ := p.exists_simulationWithCost (fun op => (gate op).size)
    (fun op => ⟨gate op, hgate op, le_rfl⟩)
  exact ⟨k, q, ρ, hρ⟩

/-- The total replacement cost bounds the size of an equivalent circuit. -/
theorem Circuit.exists_simulationWithCost (c : Circuit σ n m) (cost : σ.Op → ℕ)
    (h : J.SimulatesWithCost I cost) :
    ∃ d : Circuit τ n m, d.eval J = c.eval I ∧ d.size ≤ c.program.cost cost := by
  obtain ⟨k, q, ρ, hcost, hρ⟩ := c.program.exists_simulationWithCost cost h
  exact ⟨⟨q, ρ ∘ c.outputs⟩, funext fun x => congrArg (· ∘ c.outputs) (hρ x), hcost⟩

/-- A uniform per-gate simulation budget gives a multiplicative circuit-size bound. -/
theorem Circuit.exists_simulation_le (c : Circuit σ n m) {b : ℕ}
    (h : J.SimulatesWithCost I (fun _ => b)) :
    ∃ d : Circuit τ n m, d.eval J = c.eval I ∧ d.size ≤ b * c.size := by
  simpa only [Program.cost_const] using c.exists_simulationWithCost (fun _ => b) h

/-- Every basis simulates itself with a one-gate budget for each operation. -/
theorem Interpretation.SimulatesWithCost.refl (I : Interpretation σ U) :
    I.SimulatesWithCost I (fun _ => 1) :=
  fun op => ⟨⟨.gate .empty ⟨op, .input⟩, fun _ => .gate 0⟩, fun _ => rfl, le_rfl⟩

/-- Uniform simulation budgets multiply under composition. -/
theorem Interpretation.SimulatesWithCost.trans {b c : ℕ}
    (hK : K.SimulatesWithCost J (fun _ => b)) (hJ : J.SimulatesWithCost I (fun _ => c)) :
    K.SimulatesWithCost I (fun _ => b * c) := by
  intro op
  obtain ⟨d, hd, hsize⟩ := hJ op
  obtain ⟨e, he, hcost⟩ := d.exists_simulation_le hK
  exact ⟨e, fun x => (congrFun he x).trans (hd x),
    hcost.trans (Nat.mul_le_mul_left b hsize)⟩

/-- Gate replacement gives an equivalent circuit over the simulating basis. -/
theorem Circuit.exists_simulation (c : Circuit σ n m) (h : J.Simulates I) :
    ∃ d : Circuit τ n m, d.eval J = c.eval I := by
  obtain ⟨k, q, ρ, hρ⟩ := c.program.exists_simulation h
  exact ⟨⟨q, ρ ∘ c.outputs⟩, funext fun x => congrArg (· ∘ c.outputs) (hρ x)⟩

/-- Simulation preserves computation on any support. -/
theorem Circuit.ComputesOn.simulation {c : Circuit σ n m} {S : Set (Fin n → U)}
    {f : (Fin n → U) → Fin m → U} (hc : c.ComputesOn I S f) (h : J.Simulates I) :
    ∃ d : Circuit τ n m, d.ComputesOn J S f := by
  obtain ⟨d, hd⟩ := c.exists_simulation h
  exact ⟨d, by simpa only [Circuit.ComputesOn, hd] using hc⟩

/-- Simulation preserves computation on all inputs. -/
theorem Circuit.Computes.simulation {c : Circuit σ n m} {f : (Fin n → U) → Fin m → U}
    (hc : c.Computes I f) (h : J.Simulates I) :
    ∃ d : Circuit τ n m, d.Computes J f := by
  obtain ⟨d, hd⟩ := c.exists_simulation h
  exact ⟨d, by simpa only [Circuit.Computes, hd] using hc⟩

/-- Every basis simulates itself. -/
@[refl] theorem Interpretation.Simulates.refl (I : Interpretation σ U) : I.Simulates I :=
  (Interpretation.SimulatesWithCost.refl I).simulates

/-- Compose simulations by replacing the gates of each implementing circuit. -/
theorem Interpretation.Simulates.trans (hK : K.Simulates J) (hJ : J.Simulates I) :
    K.Simulates I := by
  intro op
  obtain ⟨c, hc⟩ := hJ op
  exact hc.simulation hK

/-- A basis that simulates a complete basis is itself complete. -/
theorem Interpretation.Simulates.isComplete (h : J.Simulates I) [I.IsComplete] :
    J.IsComplete where
  exists_computes_single f := by
    obtain ⟨c, hc⟩ := Interpretation.IsComplete.exists_computes_single (I := I) f
    exact hc.simulation h

/-- A complete basis simulates every interpretation on the same carrier. -/
theorem Interpretation.IsComplete.simulates [J.IsComplete] (I : Interpretation σ U) :
    J.Simulates I := fun op => Interpretation.IsComplete.exists_computes_single (I op)

end Cslib.Circuits
