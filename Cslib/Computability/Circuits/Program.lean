/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuits.Homomorphism
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Logic.Equiv.Defs

/-!
# Straight-line programs

A program is a topologically ordered sequence of gates. Each gate is a `Line`:
an operation symbol together with the wires supplying its arguments, where a
`Wire` is either one of the `n` original inputs or the output of an earlier
gate. Programs are indexed by their gate count, so `Program σ n g` has exactly
`g` gates and every gate reads only from wires that precede it.

This file defines

* wires, the input-fixing wire renamings `Wire.Renaming`, and the standard
  ways to build them (identity, composition, `castSucc`, `skipLast`,
  `appendLast`, and permutations);
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

/-- A wire is either an original input or the output of an earlier gate. -/
abbrev Wire n g := Fin (n + g)

/-- Regard an original input as a wire. -/
abbrev Wire.input {n g : Nat} (input : Fin n) : Wire n g :=
  Fin.castAdd g input

/-- Regard a gate output as a wire. -/
abbrev Wire.gate {n g : Nat} (gate : Fin g) : Wire n g :=
  Fin.natAdd n gate

/-- A renaming of gate wires that fixes every original input. Gate wires may be
sent to either inputs or gates in the target namespace. -/
structure Wire.Renaming (n g h : Nat) where
  /-- The target wire representing each source gate. -/
  gates : Fin g → Wire n h

namespace Wire.Renaming

/-- Apply an input-fixing wire renaming. -/
def apply (ρ : Wire.Renaming n g h) : Wire n g → Wire n h :=
  Fin.addCases Wire.input ρ.gates

instance : CoeFun (Wire.Renaming n g h) fun _ => Wire n g → Wire n h :=
  ⟨apply⟩

@[simp] theorem apply_input
    (ρ : Wire.Renaming n g h) (input : Fin n) :
    ρ (Wire.input input) = Wire.input input := by
  simp [apply]

@[simp] theorem apply_gate
    (ρ : Wire.Renaming n g h) (gate : Fin g) :
    ρ (Wire.gate gate) = ρ.gates gate := by
  simp [apply]

/-- The identity wire renaming. -/
def id : Wire.Renaming n g g where
  gates := Wire.gate

@[simp] theorem id_apply (wire : Wire n g) :
    (id : Wire.Renaming n g g) wire = wire := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire <;> simp [id]

/-- Compose input-fixing wire renamings. -/
def comp
    (outer : Wire.Renaming n h k)
    (inner : Wire.Renaming n g h) : Wire.Renaming n g k where
  gates := outer ∘ inner.gates

@[simp] theorem comp_apply
    (outer : Wire.Renaming n h k)
    (inner : Wire.Renaming n g h)
    (wire : Wire n g) :
    (outer.comp inner) wire = outer (inner wire) := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire <;>
    simp [comp, Function.comp_apply]

/-- Include all wires into a namespace with one additional gate. -/
def castSucc : Wire.Renaming n g (g + 1) where
  gates := fun gate => Wire.gate gate.castSucc

@[simp] theorem castSucc_apply (wire : Wire n g) :
    (castSucc : Wire.Renaming n g (g + 1)) wire = wire.castSucc := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · simp [castSucc, Fin.castSucc_castAdd]
  · simp [castSucc]

/-- Extend a renaming while replacing the new last gate by an existing wire. -/
def skipLast
    (prior : Wire.Renaming n g k)
    (replacement : Wire n k) : Wire.Renaming n (g + 1) k where
  gates := Fin.lastCases replacement prior.gates

theorem skipLast_gate_last
    (prior : Wire.Renaming n g k)
    (replacement : Wire n k) :
    prior.skipLast replacement (Wire.gate (Fin.last g)) = replacement := by
  rw [apply_gate]
  simp [skipLast]

@[simp] theorem skipLast_lastWire
    (prior : Wire.Renaming n g k)
    (replacement : Wire n k) :
    prior.skipLast replacement (Fin.last (n + g)) = replacement := by
  rw [← Fin.natAdd_last (n := n) (m := g)]
  exact skipLast_gate_last prior replacement

@[simp] theorem skipLast_castSucc
    (prior : Wire.Renaming n g k)
    (replacement : Wire n k)
    (wire : Wire n g) :
    prior.skipLast replacement wire.castSucc = prior wire := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · simp [Fin.castSucc_castAdd]
  · simp [skipLast]

/-- Extend a renaming and retain the new last gate as a fresh target gate. -/
def appendLast
    (prior : Wire.Renaming n g k) : Wire.Renaming n (g + 1) (k + 1) where
  gates := Fin.lastCases (Wire.gate (n := n) (Fin.last k)) fun gate =>
    (prior.gates gate).castSucc

theorem appendLast_gate_last
    (prior : Wire.Renaming n g k) :
    prior.appendLast (Wire.gate (Fin.last g)) =
      Wire.gate (n := n) (Fin.last k) := by
  rw [apply_gate]
  simp [appendLast]

@[simp] theorem appendLast_lastWire
    (prior : Wire.Renaming n g k) :
    prior.appendLast (Fin.last (n + g)) = Wire.gate (n := n) (Fin.last k) := by
  rw [← Fin.natAdd_last (n := n) (m := g)]
  exact appendLast_gate_last prior

@[simp] theorem appendLast_castSucc
    (prior : Wire.Renaming n g k)
    (wire : Wire n g) :
    prior.appendLast wire.castSucc = (prior wire).castSucc := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · simp [Fin.castSucc_castAdd]
  · simp [appendLast]

/-- Rename gate wires by a permutation. -/
def ofPermutation (permutation : Equiv.Perm (Fin g)) : Wire.Renaming n g g where
  gates := fun gate => Wire.gate (permutation gate)

theorem ofPermutation_gate
    (permutation : Equiv.Perm (Fin g)) (gate : Fin g) :
    (ofPermutation permutation : Wire.Renaming n g g) (Wire.gate gate) =
      Wire.gate (permutation gate) := by
  simp [ofPermutation]

/-- A source and target gate valuation agree along a renaming when they agree
on the image of every source gate. Original inputs agree automatically. -/
theorem value_apply
    (ρ : Wire.Renaming n g h)
    (inputs : Fin n → U)
    (oldGates : Fin g → U)
    (newGates : Fin h → U)
    (preservesGates : ∀ gate,
      (Fin.addCases inputs newGates : Wire n h → U) (ρ.gates gate) =
        oldGates gate)
    (wire : Wire n g) :
    (Fin.addCases inputs newGates : Wire n h → U) (ρ wire) =
      (Fin.addCases inputs oldGates : Wire n g → U) wire := by
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · simp
  · simpa using preservesGates gate

end Wire.Renaming

/-- One gate together with the wires supplying its arguments. -/
structure Line (σ : Signature) (n g : Nat) where
  /-- The operation performed by the gate. -/
  op : σ.Op
  /-- The wire supplying each argument of the operation. -/
  wires : Fin (σ.Arity op) → Wire n g

/-- Apply a function to every wire read by a line. -/
def Line.mapWires
    (line : Line σ n g)
    (wireMap : Wire n g → Wire n' h) : Line σ n' h where
  op := line.op
  wires := wireMap ∘ line.wires

@[simp] theorem Line.mapWires_op
    (line : Line σ n g)
    (wireMap : Wire n g → Wire n' h) :
    (line.mapWires wireMap).op = line.op := rfl

@[simp] theorem Line.mapWires_wires
    (line : Line σ n g)
    (wireMap : Wire n g → Wire n' h)
    (argument : Fin (σ.Arity line.op)) :
    (line.mapWires wireMap).wires argument = wireMap (line.wires argument) := rfl

/-- A topologically ordered straight-line program of `g` gates. -/
inductive Program (σ : Signature) (n : Nat) : Nat → Type v where
  | empty : Program σ n 0
  | gate : Program σ n g → Line σ n g → Program σ n (g + 1)

/-- Every gate in a program has at most `r` arguments. -/
def Program.FanInAtMost : (program : Program σ n g) → Nat → Prop
  | .empty, _ => True
  | .gate program line, r =>
      program.FanInAtMost r ∧ σ.Arity line.op ≤ r

/-- Bounded fan-in is decidable for every concrete program. -/
instance Program.instDecidableFanInAtMost
    (program : Program σ n g)
    (r : Nat) : Decidable (program.FanInAtMost r) :=
  match program with
  | .empty => isTrue trivial
  | .gate prior line =>
      @instDecidableAnd (prior.FanInAtMost r)
        (σ.Arity line.op ≤ r)
        (Program.instDecidableFanInAtMost prior r) inferInstance

/-- Evaluate a line from the values of the inputs and preceding gates. -/
def Line.eval
  (line : Line σ n g)
  (i : Interpretation σ U)
  (inputs : Fin n → U)
  (gates : Fin g → U) : U :=
  i line.op (Fin.addCases inputs gates ∘ line.wires)

/-- Mapping a line's wires preserves evaluation when the new valuation agrees
with the old valuation along the map. The source and target input namespaces
may differ. -/
theorem Line.eval_mapWires
    (line : Line σ n g)
    (wireMap : Wire n g → Wire n' h)
    (interpretation : Interpretation σ U)
    (oldInputs : Fin n → U)
    (newInputs : Fin n' → U)
    (oldGates : Fin g → U)
    (newGates : Fin h → U)
    (preserves : ∀ wire : Wire n g,
      (Fin.addCases newInputs newGates : Wire n' h → U) (wireMap wire) =
        (Fin.addCases oldInputs oldGates : Wire n g → U) wire) :
    (line.mapWires wireMap).eval interpretation newInputs newGates =
      line.eval interpretation oldInputs oldGates := by
  unfold Line.mapWires Line.eval
  congr 1
  funext argument
  simp only [Function.comp_apply]
  exact preserves (line.wires argument)

/-- Specialization of `Line.eval_mapWires` to an input-fixing wire renaming. -/
theorem Line.eval_mapRenaming
    (line : Line σ n g)
    (ρ : Wire.Renaming n g h)
    (interpretation : Interpretation σ U)
    (inputs : Fin n → U)
    (oldGates : Fin g → U)
    (newGates : Fin h → U)
    (preservesGates : ∀ gate,
      (Fin.addCases inputs newGates : Wire n h → U) (ρ.gates gate) =
        oldGates gate) :
    (line.mapWires ρ).eval interpretation inputs newGates =
      line.eval interpretation inputs oldGates := by
  apply Line.eval_mapWires
  exact ρ.value_apply inputs oldGates newGates preservesGates

/-- The depth of a line, given the depth of every wire it may read. -/
def Line.depth
  (line : Line σ n g)
  (wireDepths : Wire n g → Nat) : Nat :=
  Nat.succ <| Fin.foldl (σ.Arity line.op)
    (fun depth k => max depth (wireDepths (line.wires k))) 0

/-- Evaluating a line commutes with a homomorphism. -/
theorem Line.map_eval
  {i₁ : Interpretation σ U₁}
  {i₂ : Interpretation σ U₂}
  (line : Line σ n g)
  (h : Homomorphism i₁ i₂)
  (inputs : Fin n → U₁)
  (gates : Fin g → U₁) :
  h.map (line.eval i₁ inputs gates) =
    line.eval i₂ (h.map ∘ inputs) (h.map ∘ gates) := by
  rw [Line.eval, Line.eval, h.homomorphic]
  congr 1
  funext k
  simp only [Function.comp_apply]
  exact Fin.addCases (fun _ => by simp) (fun _ => by simp) (line.wires k)

/-- Evaluate every gate in a program, in program order. -/
def Program.eval
  (p : Program σ n g)
  (i : Interpretation σ U)
  (x : Fin n → U) : Fin g → U :=
  match p with
  | .empty => Fin.elim0
  | .gate p line =>
      let prior := p.eval i x
      Fin.lastCases (line.eval i x prior) prior

@[simp] theorem Program.eval_gate_last
    (program : Program σ n g)
    (line : Line σ n g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (program.gate line).eval interpretation input (Fin.last g) =
      line.eval interpretation input (program.eval interpretation input) := by
  simp [Program.eval]

@[simp] theorem Program.eval_gate_castSucc
    (program : Program σ n g)
    (line : Line σ n g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U)
    (gate : Fin g) :
    (program.gate line).eval interpretation input gate.castSucc =
      program.eval interpretation input gate := by
  simp [Program.eval]

/-- The depth of every gate in a program. Inputs have implicit depth zero. -/
def Program.depths (p : Program σ n g) : Fin g → Nat :=
  match p with
  | .empty => Fin.elim0
  | .gate p line =>
      let prior := p.depths
      let wireDepths := Fin.addCases (fun _ => 0) prior
      Fin.lastCases (line.depth wireDepths) prior

/-- The depth of every input or gate wire in a program. -/
def Program.wireDepths (p : Program σ n g) : Wire n g → Nat :=
  Fin.addCases (fun _ => 0) p.depths

/-- The maximum depth of any gate in a program. -/
def Program.depth (p : Program σ n g) : Nat :=
  Fin.foldl g (fun depth k => max depth (p.depths k)) 0

/-- Evaluating a program commutes with a homomorphism. -/
theorem Program.map_eval
  {i₁ : Interpretation σ U₁}
  {i₂ : Interpretation σ U₂}
  (p : Program σ n g)
  (h : Homomorphism i₁ i₂)
  (x : Fin n → U₁) :
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
  (p : Program σ n g)
  (i : Interpretation σ U)
  (x : Fin n → U) : Fin (n + g) → U :=
  Fin.addCases x (p.eval i x)

@[simp] theorem Program.trace_input
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U)
    (sourceInput : Fin n) :
    program.trace interpretation input (Wire.input sourceInput) =
      input sourceInput := by
  simp [Program.trace]

@[simp] theorem Program.trace_gate_castSucc
    (program : Program σ n g)
    (line : Line σ n g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U)
    (wire : Wire n g) :
    (program.gate line).trace interpretation input wire.castSucc =
      program.trace interpretation input wire := by
  unfold Program.trace
  refine Fin.addCases (fun original => ?_) (fun gate => ?_) wire
  · simp [Fin.castSucc_castAdd]
  · simp

@[simp] theorem Program.trace_gate_last
    (program : Program σ n g)
    (line : Line σ n g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U) :
    (program.gate line).trace interpretation input (Fin.last (n + g)) =
      line.eval interpretation input (program.eval interpretation input) := by
  rw [← Fin.natAdd_last (n := n) (m := g)]
  unfold Program.trace
  rw [Fin.addCases_right]
  simp

/-- Evaluating every input and gate wire commutes with a homomorphism. -/
theorem Program.map_trace
  {i₁ : Interpretation σ U₁}
  {i₂ : Interpretation σ U₂}
  (p : Program σ n g)
  (h : Homomorphism i₁ i₂)
  (x : Fin n → U₁) :
  h.map ∘ p.trace i₁ x = p.trace i₂ (h.map ∘ x) := by
  funext wire
  refine Fin.addCases (fun input => ?_) (fun gate => ?_) wire
  · simp [Program.trace, Function.comp_apply]
  · simpa [Program.trace, Function.comp_apply] using congrFun (p.map_eval h x) gate

/-- The scalar function computed by an internal gate. -/
def Program.gateFunction
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (gate : Fin g) : (Fin n → U) → U :=
  fun input => program.eval interpretation input gate

/-- The scalar function carried by an input or internal-gate wire. -/
def Program.wireFunction
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (wire : Wire n g) : (Fin n → U) → U :=
  fun input => program.trace interpretation input wire

@[simp] theorem Program.gateFunction_apply
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (gate : Fin g)
    (input : Fin n → U) :
    program.gateFunction interpretation gate input =
      program.eval interpretation input gate := rfl

@[simp] theorem Program.wireFunction_input
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (inputWire : Fin n) :
    program.wireFunction interpretation (Wire.input inputWire) =
      fun input => input inputWire := by
  funext input
  simp [Program.wireFunction, Program.trace]

@[simp] theorem Program.wireFunction_gate
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (gate : Fin g) :
    program.wireFunction interpretation (Wire.gate gate) =
      program.gateFunction interpretation gate := by
  funext input
  simp [Program.wireFunction, Program.trace]

@[simp] theorem Program.gateFunction_gate_last
    (program : Program σ n g)
    (line : Line σ n g)
    (interpretation : Interpretation σ U) :
    (program.gate line).gateFunction interpretation (Fin.last g) =
      fun input => line.eval interpretation input
        (program.eval interpretation input) := by
  funext input
  exact Program.eval_gate_last program line interpretation input

@[simp] theorem Program.gateFunction_gate_castSucc
    (program : Program σ n g)
    (line : Line σ n g)
    (interpretation : Interpretation σ U)
    (gate : Fin g) :
    (program.gate line).gateFunction interpretation gate.castSucc =
      program.gateFunction interpretation gate := by
  funext input
  exact Program.eval_gate_castSucc program line interpretation input gate

@[simp] theorem Program.trace_gateWire
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U)
    (gate : Fin g) :
    program.trace interpretation input (Wire.gate gate) =
      program.gateFunction interpretation gate input := by
  unfold Program.trace Program.gateFunction Wire.gate
  simp

/-- The program's lines, each widened to the final wire namespace. -/
def Program.lines : (program : Program σ n g) → Fin g → Line σ n g
  | .empty => Fin.elim0
  | @Program.gate _ _ g program line =>
      Fin.lastCases
        (line.mapWires Wire.Renaming.castSucc)
        (fun gate => (program.lines gate).mapWires Wire.Renaming.castSucc)

@[simp] theorem Program.lines_gate_last
    (program : Program σ n g)
    (line : Line σ n g) :
    (program.gate line).lines (Fin.last g) =
      line.mapWires Wire.Renaming.castSucc := by
  simp [Program.lines]

@[simp] theorem Program.lines_gate_castSucc
    (program : Program σ n g)
    (line : Line σ n g)
    (gate : Fin g) :
    (program.gate line).lines gate.castSucc =
      (program.lines gate).mapWires Wire.Renaming.castSucc := by
  simp [Program.lines]

/-- A widened line evaluates to the value of its corresponding program gate. -/
theorem Program.lines_eval
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (input : Fin n → U)
    (gate : Fin g) :
    (program.lines gate).eval interpretation input
        (program.eval interpretation input) =
      program.eval interpretation input gate := by
  induction program with
  | empty => exact Fin.elim0 gate
  | @gate g program line ih =>
      have evalWidened (oldLine : Line σ n g) :
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
