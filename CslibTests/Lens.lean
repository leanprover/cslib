/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CSLib Contributors
-/

import Cslib.Foundations.Data.Lens.Basic

/-!
# Lawful Lenses Tests and `MachineState` Verification Example

This file tests the `Lens` and `LawfulLens` API from `Cslib.Foundations.Data.Lens.Basic` on an
abstract machine state (`MachineState`) with fields `pc`, `memory`, and `halted`, demonstrating
verified state updates via lens laws and lens independence without manually destructing states.
-/

namespace CslibTests
namespace Lens

open Cslib
open scoped Cslib.Lens Cslib.LawfulLens

/-- State of a simple abstract machine with a program counter, memory words, and halt flag. -/
structure MachineState where
  /-- Current program counter. -/
  pc : Nat
  /-- Linear memory contents. -/
  memory : List Nat
  /-- Whether execution has halted. -/
  halted : Bool
  deriving DecidableEq, Repr

/-- Lawful lens focusing on `MachineState.pc`. -/
def pcLens : LawfulLens MachineState Nat where
  get s := s.pc
  set s pc := { s with pc := pc }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lawful lens focusing on `MachineState.memory`. -/
def memoryLens : LawfulLens MachineState (List Nat) where
  get s := s.memory
  set s memory := { s with memory := memory }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Lawful lens focusing on `MachineState.halted`. -/
def haltedLens : LawfulLens MachineState Bool where
  get s := s.halted
  set s halted := { s with halted := halted }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- `pcLens` and `memoryLens` are independent. -/
theorem pc_memory_independent : LawfulLens.Independent pcLens memoryLens where
  get_set_right _ _ := rfl
  get_set_left _ _ := rfl
  set_comm _ _ _ := rfl

/-- `pcLens` and `haltedLens` are independent. -/
theorem pc_halted_independent : LawfulLens.Independent pcLens haltedLens where
  get_set_right _ _ := rfl
  get_set_left _ _ := rfl
  set_comm _ _ _ := rfl

/-- `memoryLens` and `haltedLens` are independent. -/
theorem memory_halted_independent : LawfulLens.Independent memoryLens haltedLens where
  get_set_right _ _ := rfl
  get_set_left _ _ := rfl
  set_comm _ _ _ := rfl

/-- Execute one machine step: if not halted, increment the program counter via `pcLens.over`. -/
def step (s : MachineState) : MachineState :=
  if haltedLens.get s then s else pcLens.over (· + 1) s

/-- When the machine is halted, `step` is a no-op. -/
theorem step_of_halted (s : MachineState) (h : s.halted) : step s = s := by
  have hget : haltedLens.get s = true := h
  simp [step, hget]

/-- When the machine is not halted, `step` increments `pc` (via `LawfulLens.get_over`). -/
theorem pcLens_get_step_of_not_halted (s : MachineState) (h : ¬ s.halted) :
    pcLens.get (step s) = pcLens.get s + 1 := by
  have hget : haltedLens.get s = false := Bool.eq_false_iff.mpr h
  simp only [step, hget, Bool.false_eq_true, ↓reduceIte]
  exact pcLens.get_over (· + 1) s

/-- Field-level corollary: when `¬ s.halted`, `(step s).pc = s.pc + 1`. -/
theorem step_pc_of_not_halted (s : MachineState) (h : ¬ s.halted) :
    (step s).pc = s.pc + 1 :=
  pcLens_get_step_of_not_halted s h

/-- `step` always preserves `memory`, proved purely from `pc_memory_independent`. -/
theorem memoryLens_get_step (s : MachineState) :
    memoryLens.get (step s) = memoryLens.get s := by
  unfold step
  split
  · rfl
  · exact LawfulLens.get_over_of_independent pc_memory_independent.symm (· + 1) s

/-- Field-level corollary: `(step s).memory = s.memory`. -/
@[simp]
theorem step_memory (s : MachineState) : (step s).memory = s.memory :=
  memoryLens_get_step s

/-- `step` always preserves `halted`, proved purely from `pc_halted_independent`. -/
theorem haltedLens_get_step (s : MachineState) :
    haltedLens.get (step s) = haltedLens.get s := by
  unfold step
  split
  · rfl
  · exact LawfulLens.get_over_of_independent pc_halted_independent.symm (· + 1) s

/-- Field-level corollary: `(step s).halted = s.halted`. -/
@[simp]
theorem step_halted (s : MachineState) : (step s).halted = s.halted :=
  haltedLens_get_step s

/-- Two consecutive steps on a running machine increment `pc` by `2`. -/
theorem step_twice_pc_of_not_halted (s : MachineState) (h : ¬ s.halted) :
    (step (step s)).pc = s.pc + 2 := by
  have h₁ : ¬ (step s).halted := by simpa only [step_halted] using h
  rw [step_pc_of_not_halted (step s) h₁, step_pc_of_not_halted s h]

/-- Modifying `memory` commutes with `pcLens.over` thanks to `over_comm_of_independent`. -/
theorem modify_memory_comm_inc_pc (f : List Nat → List Nat) (s : MachineState) :
    pcLens.over (· + 1) (memoryLens.over f s) =
      memoryLens.over f (pcLens.over (· + 1) s) :=
  LawfulLens.over_comm_of_independent pc_memory_independent (· + 1) f s

/-- Pairing all three pairwise-independent lenses into a combined lawful lens. -/
def fullStateViewLens : LawfulLens MachineState ((Nat × List Nat) × Bool) :=
  (pcLens.prod memoryLens pc_memory_independent).prod haltedLens
    (LawfulLens.prod_independent pc_memory_independent pc_halted_independent
      memory_halted_independent)

/-- Composing `fullStateViewLens` with `fst` then `fst` recovers `pcLens`. -/
example : (fullStateViewLens.comp LawfulLens.fst).comp LawfulLens.fst = pcLens := by
  simp [fullStateViewLens]

/-- Composing `LawfulLens.fst` and `LawfulLens.snd` focuses on the middle of a nested pair. -/
example (p : (Nat × Bool) × String) :
    ((LawfulLens.fst.comp LawfulLens.snd).over Bool.not p) = ((p.1.1, !p.1.2), p.2) := rfl

/-- `grind` automatically discharges equational goals using the scoped lens laws. -/
example (s : MachineState) (n m : Nat) :
    pcLens.get (pcLens.set (pcLens.set s n) m) = m ∧
      pcLens.set (pcLens.set s n) (pcLens.get s) = s := by
  grind

end Lens
end CslibTests
