/-
Copyright (c) 2026 Mateo Petel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mateo Petel
-/

module

public import Cslib.Foundations.Data.Lens.Basic

/-!
# Machine state example

Lawful lens over the program counter and a verified step that preserves memory and the halt flag.
-/

@[expose] public section

namespace Cslib.Foundations.Data.Lens.Examples

open Cslib Lens

/-- A minimal interpreter-style machine state. -/
structure MachineState where
  /-- Program counter. -/
  pc : Nat
  /-- Main memory as a list of natural numbers. -/
  memory : List Nat
  /-- Whether execution has halted. -/
  halted : Bool

namespace MachineState

/-- Lawful lens focusing on the program counter. -/
def pcLens : LawfulLens MachineState Nat :=
  mkLawful
    (get := MachineState.pc)
    (set := fun s pc => { s with pc := pc })
    (get_set := by intro s pc; rfl)
    (set_get := by intro s; rfl)
    (set_set := by intro s pc₁ pc₂; rfl)

/-- Advance the program counter when the machine has not halted. -/
def step (s : MachineState) : MachineState :=
  if s.halted then s else over pcLens (· + 1) s

/-- `step` leaves memory unchanged. -/
theorem step_preserves_memory (s : MachineState) : (step s).memory = s.memory := by
  rcases s with ⟨pc, memory, hal⟩
  cases hal <;> dsimp [step, pcLens, over, mkLawful]

/-- `step` leaves the halt flag unchanged. -/
theorem step_preserves_halted (s : MachineState) : (step s).halted = s.halted := by
  rcases s with ⟨pc, memory, hal⟩
  cases hal <;> dsimp [step, pcLens, over, mkLawful]

/-- When not halted, `step` increments the program counter by one. -/
theorem step_increments_pc (s : MachineState) (h : ¬ s.halted) : (step s).pc = s.pc + 1 := by
  rcases s with ⟨pc, memory, hal⟩
  cases hal with
  | true => simp at h
  | false => dsimp [step, pcLens, over, mkLawful]

end MachineState

end Cslib.Foundations.Data.Lens.Examples
