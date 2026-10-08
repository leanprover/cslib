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

`Program.simulate` constructs the replacement program and wire map from supplied circuits.
`Program.simulateProgram` and `Program.simulateRenaming` name these two components.
`Program.trace_simulate` proves that this construction preserves every wire value.
-/

@[expose] public section

namespace Cslib.Circuits

universe v w u

variable {σ : Signature.{v}} {τ : Signature.{w}} {U : Type u}
variable {I : Interpretation σ U} {J : Interpretation τ U} {n g : ℕ}

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

end Cslib.Circuits
