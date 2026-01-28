/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.Urm.State
public import Cslib.Computability.Urm.Program

/-! # URM Configuration

This file defines the machine configuration for URMs.

## Main definitions

- `Urm.Config`: Machine configuration (program counter + state)
- `Config.init`: Initial configuration for a program with given inputs
- `Config.is_halted`: A configuration is halted if pc ≥ program length
-/

@[expose] public section

namespace Cslib.Urm

/-- Machine configuration: program counter (0-indexed) and register state. -/
structure Config where
  /-- Program counter (0-indexed). -/
  pc : ℕ
  /-- Register state. -/
  state : State

namespace Config

/-- Initial configuration for a program with given inputs.
The program counter starts at 0, and inputs are loaded into registers 0, 1, .... -/
@[scoped grind =]
def init (inputs : List ℕ) : Config := ⟨0, State.of_inputs inputs⟩

/-- A configuration is halted if the program counter is at or beyond the program length. -/
@[scoped grind =]
def is_halted (c : Config) (p : Program) : Prop := p.length ≤ c.pc

instance (c : Config) (p : Program) : Decidable (c.is_halted p) :=
  inferInstanceAs (Decidable (p.length ≤ c.pc))

@[simp]
theorem is_halted_iff (c : Config) (p : Program) : c.is_halted p ↔ p.length ≤ c.pc := Iff.rfl

/-- Extensionality for Config: two configs are equal iff their components are equal. -/
@[ext]
theorem ext {c₁ c₂ : Config} (hpc : c₁.pc = c₂.pc) (hstate : c₁.state = c₂.state) : c₁ = c₂ := by
  cases c₁; cases c₂; simp only at hpc hstate; simp [hpc, hstate]

instance : Inhabited Config := ⟨init []⟩

instance : Repr Config where
  reprPrec c _ := s!"Config(pc={c.pc})"

end Config

end Cslib.Urm

end
