/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Computability.Urm.Instr
public import Mathlib.Data.List.MinMax

/-! # URM Programs

This file defines URM programs and their basic operations.

## Main definitions

- `Urm.Program`: A finite sequence of instructions
- `Program.max_register`: maximum register index referenced by a program
- `Program.shift_jumps`: shift all jump targets by an offset
- `Program.shift_registers`: shift all register references by an offset
-/

@[expose] public section

namespace Cslib.Urm

/-- A URM program is a list of instructions. -/
abbrev Program := List Instr

namespace Program

/-- The maximum register index referenced by any instruction in the program. -/
@[scoped grind =]
def max_register (p : Program) : ℕ :=
  p.foldl (fun acc instr => max acc instr.max_register) 0

/-- Shift all jump targets in a program by `offset`.
Used when concatenating programs: the second program's jumps must be adjusted
by the length of the first program. -/
@[scoped grind =]
def shift_jumps (offset : ℕ) (p : Program) : Program :=
  p.map (Instr.shift_jumps offset)

/-- Shift all register references in a program by `offset`.
Used to isolate register usage when composing programs. -/
@[scoped grind =]
def shift_registers (offset : ℕ) (p : Program) : Program :=
  p.map (Instr.shift_registers offset)

/-- Any instruction in a program has max_register at most the program's max_register. -/
theorem mem_max_register {p : Program} {instr : Instr} (h : instr ∈ p) :
    instr.max_register ≤ p.max_register := by
  unfold max_register
  rw [List.foldl_map.symm, List.foldl_eq_foldr]
  exact List.le_max_of_le' 0 (List.mem_map.mpr ⟨instr, h, rfl⟩) (le_refl _)

end Program

end Cslib.Urm

end
