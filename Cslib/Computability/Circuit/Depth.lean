/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Basic

/-!
# Circuit depth bounds

This file proves bounds for `Program.depth`, defined in `Cslib.Computability.Circuit.Program`,
and `Circuit.depth`, defined in `Cslib.Computability.Circuit.Basic`. Program depth is the maximum
depth of its gates; circuit depth is the maximum depth of its designated outputs.
`Program.depth_le_iff` and `Circuit.depth_le_iff` express bounds in terms of the individual
gates and outputs. These characterizations give
`Circuit.depth_le_program_depth` and `Circuit.depth_le_size` without assumptions on the
signature's fan-in or its interpretation.

Constructor simplification lemmas preserve the depth of earlier wires when a gate is added.
Every gate, including a constant gate, contributes one level; selecting outputs contributes
none. A circuit with no outputs has depth zero, even when its program contains gates.
-/

@[expose] public section

namespace Cslib.Circuits

universe v
variable {σ : Signature.{v}} {n g m : Nat}

private theorem foldl_max_le_iff {n : Nat} (f : Fin n → Nat) (initial bound : Nat) :
    Fin.foldl n (fun acc i => max acc (f i)) initial ≤ bound ↔
      initial ≤ bound ∧ ∀ i, f i ≤ bound := by
  induction n generalizing initial with
  | zero => simp
  | succ n ih =>
      rw [Fin.foldl_succ, ih]
      simp [Fin.forall_fin_succ, and_assoc]

/-- Bounding every argument by `d` bounds the gate's depth by `d + 1`. -/
theorem Line.depth_le_add_one_iff (line : Line σ n g) (depths : Wire n g → Nat) {d : Nat} :
    line.depth depths ≤ d + 1 ↔ ∀ j, depths (line.wires j) ≤ d := by
  simp only [Line.depth, Nat.succ_le_succ_iff]
  simpa using foldl_max_le_iff (fun j => depths (line.wires j)) 0 d

/-- Every gate, including a constant gate, has positive depth. -/
theorem Line.depth_pos (line : Line σ n g) (depths : Wire n g → Nat) :
    0 < line.depth depths := Nat.zero_lt_succ _

@[simp] theorem Program.depths_gate_last (p : Program σ n g) (line : Line σ n g) :
    (p.gate line).depths (Fin.last g) = line.depth p.wireDepths := by
  simp [Program.depths, Program.wireDepths]

@[simp] theorem Program.depths_gate_castSucc (p : Program σ n g) (line : Line σ n g)
    (j : Fin g) : (p.gate line).depths j.castSucc = p.depths j := by
  simp [Program.depths]

@[simp] theorem Program.wireDepths_input (p : Program σ n g) (i : Fin n) :
    p.wireDepths (.input i) = 0 := rfl

@[simp] theorem Program.wireDepths_gateWire (p : Program σ n g) (j : Fin g) :
    p.wireDepths (.gate j) = p.depths j := rfl

@[simp] theorem Program.wireDepths_gate_castSucc (p : Program σ n g) (line : Line σ n g)
    (w : Wire n g) : (p.gate line).wireDepths w.castSucc = p.wireDepths w := by
  cases w <;> simp

@[simp] theorem Program.depth_empty : (Program.empty : Program σ n 0).depth = 0 := rfl

@[simp] theorem Program.depth_gate (p : Program σ n g) (line : Line σ n g) :
    (p.gate line).depth = max p.depth (line.depth p.wireDepths) := by
  simp [Program.depth, Fin.foldl_succ_last]

/-- Program depth is bounded by `d` exactly when every gate depth is bounded by `d`. -/
theorem Program.depth_le_iff (p : Program σ n g) {d : Nat} :
    p.depth ≤ d ↔ ∀ j, p.depths j ≤ d := by
  simpa [Program.depth] using foldl_max_le_iff p.depths 0 d

/-- Every gate depth is at most the depth of the program. -/
theorem Program.depths_le_depth (p : Program σ n g) (j : Fin g) : p.depths j ≤ p.depth :=
  p.depth_le_iff.mp le_rfl j

/-- Every input or gate wire has depth at most the depth of the program. -/
theorem Program.wireDepths_le_depth (p : Program σ n g) (w : Wire n g) :
    p.wireDepths w ≤ p.depth := by
  cases w with
  | input i => exact Nat.zero_le _
  | gate j => exact p.depths_le_depth j

/-- A program's depth is at most its number of gates. -/
theorem Program.depth_le_gateCount (p : Program σ n g) : p.depth ≤ g := by
  induction p with
  | empty => exact le_rfl
  | gate p line ih =>
      rw [depth_gate, max_le_iff]
      exact ⟨Nat.le_succ_of_le ih, (line.depth_le_add_one_iff p.wireDepths).mpr
        (fun j => (p.wireDepths_le_depth (line.wires j)).trans ih)⟩

/-- Circuit depth is bounded by `d` exactly when every designated output depth is bounded by `d`. -/
theorem Circuit.depth_le_iff (c : Circuit σ n m) {d : Nat} :
    c.depth ≤ d ↔ ∀ j, c.outputDepths j ≤ d := by
  simpa [Circuit.depth] using foldl_max_le_iff c.outputDepths 0 d

/-- Every designated output has depth at most the circuit depth. -/
theorem Circuit.outputDepths_le_depth (c : Circuit σ n m) (j : Fin m) :
    c.outputDepths j ≤ c.depth := c.depth_le_iff.mp le_rfl j

/-- Selecting outputs cannot increase the maximum depth over all program gates. -/
theorem Circuit.depth_le_program_depth (c : Circuit σ n m) : c.depth ≤ c.program.depth :=
  c.depth_le_iff.mpr fun j => c.program.wireDepths_le_depth (c.outputs j)

/-- Circuit depth is at most the number of gates. -/
theorem Circuit.depth_le_size (c : Circuit σ n m) : c.depth ≤ c.size :=
  c.depth_le_program_depth.trans c.program.depth_le_gateCount

@[simp] theorem Circuit.depth_zero_outputs (c : Circuit σ n 0) : c.depth = 0 := rfl

end Cslib.Circuits
