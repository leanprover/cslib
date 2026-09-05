/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuits.Homomorphism
public import Cslib.Computability.Circuits.Wire

/-!
# Straight-line programs

A program is a topologically ordered sequence of gates. Each `Line` records an
operation and its argument wires. The gate-count index ensures that wires refer
only to original inputs or earlier gates.

This file defines

* lines, their evaluation and depth, and `Line.mapWires` together with the
  transport lemmas `Line.eval_mapWires` and `Line.eval_mapRenaming`;
* programs, their evaluation `Program.eval`, the input-and-gate valuation
  `Program.trace`, gate depths, and the bounded-fan-in predicate
  `Program.FanInAtMost`;
* the scalar views `Program.gateFunction` and `Program.wireFunction`, and the
  widened line collection `Program.lines` with `Program.lines_eval`.

Evaluation of lines and programs commutes with homomorphisms
(`Line.map_eval`, `Program.map_eval`, `Program.map_trace`).
-/

@[expose] public section

namespace Cslib.Circuits

universe v u u₁ u₂

variable {σ : Signature.{v}} {inputCount gateCount : Nat}
variable {sourceInputCount targetInputCount sourceGateCount targetGateCount : Nat}
variable {U : Type u} {U₁ : Type u₁} {U₂ : Type u₂}

/-- One gate together with the wires supplying its arguments. -/
structure Line (σ : Signature) (inputCount gateCount : Nat) where
  /-- The operation performed by the gate. -/
  op : σ.Op
  /-- The wire supplying each argument of the operation. -/
  wires : Fin (σ.Arity op) → Wire inputCount gateCount

/-- Apply a function to every wire read by a line. -/
def Line.mapWires
    (line : Line σ sourceInputCount sourceGateCount)
    (wireMap : Wire sourceInputCount sourceGateCount → Wire targetInputCount targetGateCount) :
    Line σ targetInputCount targetGateCount where
  op := line.op
  wires := wireMap ∘ line.wires

@[simp] theorem Line.mapWires_op
    (line : Line σ sourceInputCount sourceGateCount)
    (wireMap : Wire sourceInputCount sourceGateCount → Wire targetInputCount targetGateCount) :
    (line.mapWires wireMap).op = line.op := rfl

@[simp] theorem Line.mapWires_wires
    (line : Line σ sourceInputCount sourceGateCount)
    (wireMap : Wire sourceInputCount sourceGateCount → Wire targetInputCount targetGateCount)
    (argument : Fin (σ.Arity line.op)) :
    (line.mapWires wireMap).wires argument = wireMap (line.wires argument) := rfl

/-- A topologically ordered straight-line program, indexed by its gate count. -/
inductive Program (σ : Signature.{v}) (inputCount : Nat) : Nat → Type v where
  | empty : Program σ inputCount 0
  | gate {gateCount : Nat} :
      Program σ inputCount gateCount → Line σ inputCount gateCount →
        Program σ inputCount (gateCount + 1)

/-- Every gate in a program has at most `r` arguments. -/
def Program.FanInAtMost {gateCount : Nat} : (program : Program σ inputCount gateCount) → Nat → Prop
  | .empty, _ => True
  | .gate program line, r =>
      program.FanInAtMost r ∧ σ.Arity line.op ≤ r

/-- Bounded fan-in is decidable for every concrete program. -/
instance Program.instDecidableFanInAtMost {gateCount : Nat}
    (program : Program σ inputCount gateCount)
    (r : Nat) : Decidable (program.FanInAtMost r) :=
  match program with
  | .empty => isTrue trivial
  | .gate prior line =>
      @instDecidableAnd (prior.FanInAtMost r)
        (σ.Arity line.op ≤ r)
        (Program.instDecidableFanInAtMost prior r) inferInstance

/-- Evaluate a line from the values of the inputs and preceding gates. -/
def Line.eval
    (line : Line σ inputCount gateCount)
    (i : Interpretation σ U)
    (inputs : Fin inputCount → U)
    (gates : Fin gateCount → U) : U :=
  i line.op (Fin.addCases inputs gates ∘ line.wires)

/-- Mapping a line's wires preserves evaluation when the new valuation agrees
with the old valuation along the map. The source and target input namespaces
may differ. -/
theorem Line.eval_mapWires
    (line : Line σ sourceInputCount sourceGateCount)
    (wireMap : Wire sourceInputCount sourceGateCount → Wire targetInputCount targetGateCount)
    (interpretation : Interpretation σ U)
    (oldInputs : Fin sourceInputCount → U)
    (newInputs : Fin targetInputCount → U)
    (oldGates : Fin sourceGateCount → U)
    (newGates : Fin targetGateCount → U)
    (preserves : ∀ wire : Wire sourceInputCount sourceGateCount,
      (Fin.addCases newInputs newGates : Wire targetInputCount targetGateCount → U) (wireMap wire) =
        (Fin.addCases oldInputs oldGates : Wire sourceInputCount sourceGateCount → U) wire) :
    (line.mapWires wireMap).eval interpretation newInputs newGates =
      line.eval interpretation oldInputs oldGates := by
  unfold Line.mapWires Line.eval
  congr 1
  funext argument
  simp only [Function.comp_apply]
  exact preserves (line.wires argument)

/-- Specialization of `Line.eval_mapWires` to an input-fixing wire renaming. -/
theorem Line.eval_mapRenaming
    (line : Line σ inputCount sourceGateCount)
    (ρ : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (interpretation : Interpretation σ U)
    (inputs : Fin inputCount → U)
    (oldGates : Fin sourceGateCount → U)
    (newGates : Fin targetGateCount → U)
    (preservesGates : ∀ gate,
      (Fin.addCases inputs newGates : Wire inputCount targetGateCount → U) (ρ.gates gate) =
        oldGates gate) :
    (line.mapWires ρ).eval interpretation inputs newGates =
      line.eval interpretation inputs oldGates := by
  apply Line.eval_mapWires
  exact ρ.value_apply inputs oldGates newGates preservesGates

/-- The depth of a line, given the depth of every wire it may read. -/
def Line.depth
    (line : Line σ inputCount gateCount)
    (wireDepths : Wire inputCount gateCount → Nat) : Nat :=
  Nat.succ <| Fin.foldl (σ.Arity line.op)
    (fun depth k => max depth (wireDepths (line.wires k))) 0

/-- Evaluating a line commutes with a homomorphism. -/
theorem Line.map_eval
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    (line : Line σ inputCount gateCount)
    (h : Homomorphism i₁ i₂)
    (inputs : Fin inputCount → U₁)
    (gates : Fin gateCount → U₁) :
    h.map (line.eval i₁ inputs gates) =
      line.eval i₂ (h.map ∘ inputs) (h.map ∘ gates) := by
  rw [Line.eval, Line.eval, h.homomorphic]
  congr 1
  funext k
  simp only [Function.comp_apply]
  exact Fin.addCases (fun _ => by simp) (fun _ => by simp) (line.wires k)

/-- Evaluate every gate in a program, in program order. -/
def Program.eval {gateCount : Nat}
    (p : Program σ inputCount gateCount)
    (i : Interpretation σ U)
    (x : Fin inputCount → U) : Fin gateCount → U :=
  match p with
  | .empty => Fin.elim0
  | .gate p line =>
      let prior := p.eval i x
      Fin.lastCases (line.eval i x prior) prior

@[simp] theorem Program.eval_gate_last
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U) :
    (program.gate line).eval interpretation input (Fin.last gateCount) =
      line.eval interpretation input (program.eval interpretation input) := by
  simp [Program.eval]

@[simp] theorem Program.eval_gate_castSucc
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U)
    (gate : Fin gateCount) :
    (program.gate line).eval interpretation input gate.castSucc =
      program.eval interpretation input gate := by
  simp [Program.eval]

/-- The depth of every gate in a program. Inputs have implicit depth zero. -/
def Program.depths {gateCount : Nat} (p : Program σ inputCount gateCount) : Fin gateCount → Nat :=
  match p with
  | .empty => Fin.elim0
  | .gate p line =>
      let prior := p.depths
      let wireDepths := Fin.addCases (fun _ => 0) prior
      Fin.lastCases (line.depth wireDepths) prior

/-- The depth of every input or gate wire in a program. -/
def Program.wireDepths (p : Program σ inputCount gateCount) : Wire inputCount gateCount → Nat :=
  Fin.addCases (fun _ => 0) p.depths

/-- The maximum depth of any gate in a program. -/
def Program.depth (p : Program σ inputCount gateCount) : Nat :=
  Fin.foldl gateCount (fun depth k => max depth (p.depths k)) 0

/-- Evaluating a program commutes with a homomorphism. -/
theorem Program.map_eval
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    (p : Program σ inputCount gateCount)
    (h : Homomorphism i₁ i₂)
    (x : Fin inputCount → U₁) :
    h.map ∘ p.eval i₁ x = p.eval i₂ (h.map ∘ x) := by
  induction p with
  | empty =>
      funext k
      exact Fin.elim0 k
  | gate p line ih =>
      funext k
      refine Fin.lastCases ?_ ?_ k
      · simpa only [Program.eval, Function.comp_apply, Fin.lastCases_last, ih] using
          line.map_eval h x (p.eval i₁ x)
      · intro j
        simpa only [Program.eval, Function.comp_apply, Fin.lastCases_castSucc] using
          congrFun ih j

/-- The input values followed by all gate values, in program order. -/
def Program.trace
    (p : Program σ inputCount gateCount)
    (i : Interpretation σ U)
    (x : Fin inputCount → U) : Fin (inputCount + gateCount) → U :=
  Fin.addCases x (p.eval i x)

@[simp] theorem Program.trace_input
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U)
    (sourceInput : Fin inputCount) :
    program.trace interpretation input (Wire.input sourceInput) =
      input sourceInput := by
  simp [Program.trace]

@[simp] theorem Program.trace_gate_castSucc
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U)
    (wire : Wire inputCount gateCount) :
    (program.gate line).trace interpretation input wire.castSucc =
      program.trace interpretation input wire := by
  unfold Program.trace
  refine Fin.addCases (fun original => ?_) (fun gate => ?_) wire
  · simp [Fin.castSucc_castAdd]
  · simp

@[simp] theorem Program.trace_gate_last
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U) :
    (program.gate line).trace interpretation input (Fin.last (inputCount + gateCount)) =
      line.eval interpretation input (program.eval interpretation input) := by
  rw [← Fin.natAdd_last (n := inputCount) (m := gateCount)]
  unfold Program.trace
  rw [Fin.addCases_right]
  simp

/-- Evaluating every input and gate wire commutes with a homomorphism. -/
theorem Program.map_trace
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    (p : Program σ inputCount gateCount)
    (h : Homomorphism i₁ i₂)
    (x : Fin inputCount → U₁) :
    h.map ∘ p.trace i₁ x = p.trace i₂ (h.map ∘ x) := by
  funext wire
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · simp [Program.trace, Function.comp_apply]
  · simpa [Program.trace, Function.comp_apply] using congrFun (p.map_eval h x) gate

/-- The scalar function computed by an internal gate. -/
def Program.gateFunction
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (gate : Fin gateCount)
    (input : Fin inputCount → U) : U :=
  program.eval interpretation input gate

/-- The scalar function carried by an input or internal-gate wire. -/
def Program.wireFunction
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (wire : Wire inputCount gateCount)
    (input : Fin inputCount → U) : U :=
  program.trace interpretation input wire

@[simp] theorem Program.gateFunction_apply
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (gate : Fin gateCount)
    (input : Fin inputCount → U) :
    program.gateFunction interpretation gate input =
      program.eval interpretation input gate := rfl

@[simp] theorem Program.wireFunction_input
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (inputWire : Fin inputCount) :
    program.wireFunction interpretation (Wire.input inputWire) =
      fun input => input inputWire := by
  funext input
  simp [Program.wireFunction, Program.trace]

@[simp] theorem Program.wireFunction_gate
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (gate : Fin gateCount) :
    program.wireFunction interpretation (Wire.gate gate) =
      program.gateFunction interpretation gate := by
  funext input
  simp [Program.wireFunction, Program.trace]

@[simp] theorem Program.gateFunction_gate_last
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount)
    (interpretation : Interpretation σ U) :
    (program.gate line).gateFunction interpretation (Fin.last gateCount) =
      fun input => line.eval interpretation input
        (program.eval interpretation input) := by
  funext input
  exact Program.eval_gate_last program line interpretation input

@[simp] theorem Program.gateFunction_gate_castSucc
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (gate : Fin gateCount) :
    (program.gate line).gateFunction interpretation gate.castSucc =
      program.gateFunction interpretation gate := by
  funext input
  exact Program.eval_gate_castSucc program line interpretation input gate

@[simp] theorem Program.trace_gateWire
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U)
    (gate : Fin gateCount) :
    program.trace interpretation input (Wire.gate gate) =
      program.gateFunction interpretation gate input := by
  unfold Program.trace Program.gateFunction Wire.gate
  simp

/-- The program's lines, each widened to the final wire namespace. -/
def Program.lines {gateCount : Nat} :
    (program : Program σ inputCount gateCount) → Fin gateCount → Line σ inputCount gateCount
  | .empty => Fin.elim0
  | @Program.gate _ _ gateCount program line =>
      Fin.lastCases
        (line.mapWires Wire.Renaming.castSucc)
        (fun gate => (program.lines gate).mapWires Wire.Renaming.castSucc)

@[simp] theorem Program.lines_gate_last
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount) :
    (program.gate line).lines (Fin.last gateCount) =
      line.mapWires Wire.Renaming.castSucc := by
  simp [Program.lines]

@[simp] theorem Program.lines_gate_castSucc
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount)
    (gate : Fin gateCount) :
    (program.gate line).lines gate.castSucc =
      (program.lines gate).mapWires Wire.Renaming.castSucc := by
  simp [Program.lines]

/-- A widened line evaluates to the value of its corresponding program gate. -/
theorem Program.lines_eval
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U)
    (gate : Fin gateCount) :
    (program.lines gate).eval interpretation input
        (program.eval interpretation input) =
      program.eval interpretation input gate := by
  induction program with
  | empty => exact Fin.elim0 gate
  | @gate gateCount program line ih =>
      have evalWidened (oldLine : Line σ inputCount gateCount) :
          (oldLine.mapWires Wire.Renaming.castSucc).eval interpretation input
              ((program.gate line).eval interpretation input) =
            oldLine.eval interpretation input
              (program.eval interpretation input) := by
        apply Line.eval_mapWires
        intro wire
        simpa only [Wire.Renaming.castSucc_apply, Program.trace] using
          Program.trace_gate_castSucc program line interpretation input wire
      refine Fin.lastCases ?_ (fun priorGate => ?_) gate
      · simpa only [Program.lines_gate_last, Program.eval_gate_last] using
          evalWidened line
      · simp only [Program.lines_gate_castSucc, Program.eval_gate_castSucc]
        exact (evalWidened (program.lines priorGate)).trans (ih priorGate)

end Cslib.Circuits
