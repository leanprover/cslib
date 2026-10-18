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

`Program.simulate` constructs the replacement program and wire map from supplied circuits.
`Program.simulateProgram` and `Program.simulateRenaming` name these two components.
`Program.trace_simulate` proves that this construction preserves every wire value.

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

/-- A simulation with a gate budget for each primitive operation. -/
def Interpretation.SimulatesWithCost (J : Interpretation τ U) (I : Interpretation σ U)
    (cost : σ.Op → ℕ) : Prop :=
  ∀ op : σ.Op, ∃ c : Circuit τ (σ.Arity op) 1,
    c.Computes J (single (I op)) ∧ c.size ≤ cost op

/-- `J` simulates `I` if it can compute every primitive operation of `I`, with some gate budget. -/
def Interpretation.Simulates (J : Interpretation τ U) (I : Interpretation σ U) : Prop :=
  ∃ cost, J.SimulatesWithCost I cost

theorem Interpretation.SimulatesWithCost.simulates {cost : σ.Op → ℕ}
    (h : J.SimulatesWithCost I cost) : J.Simulates I :=
  ⟨cost, h⟩

theorem Interpretation.simulates_iff :
    J.Simulates I ↔ ∀ op : σ.Op, ∃ c : Circuit τ (σ.Arity op) 1,
      c.Computes J (single (I op)) := by
  constructor
  · rintro ⟨cost, h⟩ op
    exact (h op).imp fun _ hc => hc.1
  · intro h
    choose impl himpl using h
    exact ⟨fun op => (impl op).size, fun op => ⟨impl op, himpl op, le_rfl⟩⟩

/-- Given a cost per operation, this is the sum of the costs along a straight-line program. -/
def Program.cost {g : ℕ} (p : Program σ n g) (cost : σ.Op → ℕ) : ℕ :=
  p.foldl (fun total line => total + cost line.op) 0

@[simp] theorem Program.cost_empty (cost : σ.Op → ℕ) :
    (Program.empty : Program σ n 0).cost cost = 0 := rfl

@[simp] theorem Program.cost_gate (p : Program σ n g) (line : Line σ n g)
    (cost : σ.Op → ℕ) : (p.gate line).cost cost = p.cost cost + cost line.op := rfl

@[simp] theorem Program.cost_const (p : Program σ n g) (b : ℕ) :
    p.cost (fun _ => b) = b * g := by
  induction p <;> simp_all [Nat.mul_add]

theorem Program.cost_mono (p : Program σ n g) {cost cost' : σ.Op → ℕ}
    (h : ∀ op, cost op ≤ cost' op) : p.cost cost ≤ p.cost cost' :=
  p.foldl_rel (· ≤ ·) le_rfl fun line htotal => Nat.add_le_add htotal (h line.op)

/-- Replace each operation by its supplied circuit, returning the resulting program and
a map from the original wires to their replacements. The gate count is the sum of the
sizes of the replacement circuits. -/
def Program.simulate {g : ℕ} (p : Program σ n g)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) :
    Program τ n (p.cost fun op => (impl op).size) ×
      Wire.Renaming n g (p.cost fun op => (impl op).size) :=
  match p with
  | .empty => ⟨.empty, .id⟩
  | .gate q line =>
    let (r, ρ) := q.simulate impl
    let c := impl line.op
    let feed := ρ ∘ line.wires
    let prior : Wire.Renaming n _ _ := ⟨fun j => (ρ.gates j).castAdd c.size⟩
    ⟨r.append feed c.program, prior.skipLast (Program.appendedWire feed (c.outputs 0))⟩

/-- The program obtained by replacing each operation by its supplied circuit. -/
abbrev Program.simulateProgram (p : Program σ n g)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) :
    Program τ n (p.cost fun op => (impl op).size) :=
  (p.simulate impl).1

/-- The map from original wires to their replacements in `Program.simulateProgram`. -/
abbrev Program.simulateRenaming (p : Program σ n g)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) :
    Wire.Renaming n g (p.cost fun op => (impl op).size) :=
  (p.simulate impl).2

/-- Replacing each operation by a circuit computing it preserves every wire value. -/
theorem Program.trace_simulate (p : Program σ n g)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1)
    (h : ∀ op, (impl op).Computes J (single (I op))) (x : Fin n → U) :
    (p.simulateProgram impl).trace J x ∘ p.simulateRenaming impl = p.trace I x := by
  induction p with
  | empty =>
    funext w
    cases w <;> rfl
  | gate q line ih =>
    let r := q.simulateProgram impl
    let ρ := q.simulateRenaming impl
    let c := impl line.op
    let feed := ρ ∘ line.wires
    funext w
    dsimp only [simulateProgram, simulateRenaming, simulate, cost_gate, Function.comp_apply]
    refine Wire.lastCases ?_ (fun w => ?_) w
    · simp only [Wire.Renaming.apply_gate, Wire.Renaming.skipLast_gates_last]
      rw [Program.trace_append_appendedWire]
      change c.eval J _ 0 = _
      rw [h line.op]
      change I line.op ((r.trace J x ∘ ρ) ∘ line.wires) = _
      rw [ih]
      exact (Program.eval_gate_last q line I x).symm
    · rw [Wire.Renaming.skipLast_castSucc, Program.trace_gate_castSucc]
      have hold := (Program.trace_append_castAdd r feed J x c.program (ρ w)).trans
        (congrFun ih w)
      cases w <;> exact hold

/-- Simulate a program over `σ` by a program over `τ`, with a bound on the number of gates.

Assume that each operation `op` under `I` is computed by a circuit under `J` using at most
`cost op` gates. Replacing the gates of `p : Program σ n g` by these circuits produces a
program `q : Program τ n k` with `k ≤ p.cost cost`.

The returned map `ρ : Wire.Renaming n g k` fixes the input wires and maps every gate wire of
`p` to a wire of `q` carrying the same value. For every input `x`, the equality
`q.trace J x ∘ ρ = p.trace I x` says that all input and intermediate values are preserved. -/
theorem Program.exists_simulationWithCost (p : Program σ n g) (cost : σ.Op → ℕ)
    (h : J.SimulatesWithCost I cost) :
    ∃ k : ℕ, ∃ q : Program τ n k, ∃ ρ : Wire.Renaming n g k,
      k ≤ p.cost cost ∧ ∀ x : Fin n → U, q.trace J x ∘ ρ = p.trace I x := by
  choose impl himpl hsize using h
  use p.cost fun op => (impl op).size, p.simulateProgram impl, p.simulateRenaming impl,
    p.cost_mono hsize, p.trace_simulate impl himpl

/-- Replace the gates of a program, preserving every input and intermediate value. -/
theorem Program.exists_simulation (p : Program σ n g) (h : J.Simulates I) :
    ∃ k : ℕ, ∃ q : Program τ n k, ∃ ρ : Wire.Renaming n g k,
      ∀ x : Fin n → U, q.trace J x ∘ ρ = p.trace I x := by
  obtain ⟨cost, hcost⟩ := h
  obtain ⟨k, q, ρ, _, hρ⟩ := p.exists_simulationWithCost cost hcost
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
  rw [Interpretation.simulates_iff] at hJ ⊢
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
    J.Simulates I :=
  Interpretation.simulates_iff.mpr fun op => Interpretation.IsComplete.exists_computes_single (I op)

end Cslib.Circuits
