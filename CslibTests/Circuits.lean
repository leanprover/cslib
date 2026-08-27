/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuits.Circuit

/-! # Circuit tests

These tests exercise zero-gate wiring, shared internal gates, multiple outputs,
and the size and depth conventions of the generic circuit model.
-/

namespace CslibTests.Circuits

open Cslib.Circuits

inductive NandOp where
  | nand

abbrev nandSignature : Signature where
  Op := NandOp
  Arity := fun _ => 2

def nandInterpretation : Interpretation nandSignature Bool
  | .nand, input => !(input 0 && input 1)

def nandInputs : Line nandSignature 2 0 where
  op := .nand
  wires := Fin.cases (Wire.input 0) fun _ => Wire.input 1

def nandResultTwice : Line nandSignature 2 1 where
  op := .nand
  wires := fun _ => Wire.gate 0

def andProgram : Program nandSignature 2 2 :=
  .gate (.gate .empty nandInputs) nandResultTwice

/-- The first output is AND and the second is NAND. Both reuse the first gate. -/
def andNandCircuit : Circuit nandSignature 2 2 2 where
  program := andProgram
  outputs := Fin.cases (Wire.gate 1) fun _ => Wire.gate 0

def allTrue : Fin 2 → Bool := fun _ => true

def trueFalse : Fin 2 → Bool := Fin.cases true fun _ => false

example : andNandCircuit.eval nandInterpretation allTrue 0 = true := rfl

example : andNandCircuit.eval nandInterpretation allTrue 1 = false := rfl

example : andNandCircuit.eval nandInterpretation trueFalse 0 = false := rfl

example : andNandCircuit.eval nandInterpretation trueFalse 1 = true := rfl

example : andNandCircuit.size = 2 := rfl

example : andNandCircuit.depth = 2 := rfl

example : andNandCircuit.FanInAtMost 2 := by decide

example : ¬ andNandCircuit.FanInAtMost 1 := by decide

example : andNandCircuit.computation nandInterpretation allTrue 0 = false := rfl

example : andNandCircuit.computation nandInterpretation allTrue 1 = true := rfl

example : andNandCircuit.computation nandInterpretation allTrue 2 = true := rfl

example : andNandCircuit.computation nandInterpretation allTrue 3 = false := rfl

example : andNandCircuit.trace nandInterpretation allTrue 1 = true := rfl

example : andNandCircuit.trace nandInterpretation allTrue 2 = false := rfl

example : andNandCircuit.trace nandInterpretation allTrue 3 = true := rfl

example : andNandCircuit.trace nandInterpretation allTrue 4 = true := rfl

/-- A zero-gate circuit can permute inputs without introducing artificial gates. -/
def swap : Circuit nandSignature 2 0 2 where
  program := .empty
  outputs := Fin.cases (Wire.input 1) fun _ => Wire.input 0

example : swap.eval nandInterpretation trueFalse 0 = false := rfl

example : swap.eval nandInterpretation trueFalse 1 = true := rfl

example : swap.size = 0 := rfl

example : swap.depth = 0 := rfl

/-- Duplicating an output wire is also free. -/
def duplicateFirst : Circuit nandSignature 2 0 2 where
  program := .empty
  outputs := fun _ => Wire.input 0

example : duplicateFirst.eval nandInterpretation trueFalse 0 = true := rfl

example : duplicateFirst.eval nandInterpretation trueFalse 1 = true := rfl

example : duplicateFirst.size = 0 := rfl

def noOutputs : Circuit nandSignature 2 2 0 where
  program := andProgram
  outputs := Fin.elim0

example : noOutputs.depth = 0 := rfl

inductive ConstantOp where
  | truth

def constantSignature : Signature where
  Op := ConstantOp
  Arity := fun _ => 0

def constantInterpretation : Interpretation constantSignature Bool
  | .truth, _ => true

def truthLine : Line constantSignature 0 0 where
  op := .truth
  wires := Fin.elim0

def truthProgram : Program constantSignature 0 1 :=
  .gate .empty truthLine

def truthCircuit : Circuit constantSignature 0 1 1 where
  program := truthProgram
  outputs := fun _ => Wire.gate 0

example : truthCircuit.eval constantInterpretation Fin.elim0 0 = true := rfl

example : truthCircuit.FanInAtMost 0 := by decide

example : truthCircuit.depth = 1 := rfl

end CslibTests.Circuits
