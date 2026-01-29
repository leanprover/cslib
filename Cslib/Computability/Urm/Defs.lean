/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Init
public import Mathlib.Data.Finset.Insert
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.List.MinMax

/-! # URM Core Definitions

This file contains the core definitions for Unlimited Register Machines (URMs):
instructions, register state, programs, and machine configurations.

## Main definitions

- `Urm.Instr`: The four URM instructions (Z, S, T, J)
- `Urm.State`: Register contents as a function `ℕ → ℕ`
- `Urm.Program`: A finite sequence of instructions
- `Urm.Config`: Machine configuration (program counter + state)

## File Organization

The URM module is organized into the following files:

- `Defs.lean`: Core type definitions (this file)
- `Basic.lean`: Basic lemmas about instructions and programs
- `Execution.lean`: Step/Steps/Halts/eval definitions
- `StraightLine.lean`: Straight-line program execution theorems
- `StandardForm.lean`: Standard form program execution theorems
- `Computable.lean`: URM-computable functions

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
* [J.C. Shepherdson and H.E. Sturgis,
  *Computability of Recursive Functions*][ShepherdsonSturgis1963]
-/

@[expose] public section

namespace Cslib.Urm

/-! ## Instructions -/

/-- URM instructions.
- `Z n`: Set register n to zero
- `S n`: Increment register n by one
- `T m n`: Transfer (copy) the contents of register m to register n
- `J m n q`: If registers m and n have equal contents, jump to instruction q;
             otherwise proceed to the next instruction
-/
@[grind]
inductive Instr : Type where
  | Z : ℕ → Instr
  | S : ℕ → Instr
  | T : ℕ → ℕ → Instr
  | J : ℕ → ℕ → ℕ → Instr
deriving DecidableEq, Repr

namespace Instr

/-- The registers read by an instruction. -/
@[scoped grind =]
def reads_from : Instr → Finset ℕ
  | Z _ => ∅
  | S n => {n}
  | T m _ => {m}
  | J m n _ => {m, n}

/-- The register written to by an instruction, if any. -/
@[scoped grind =]
def writes_to : Instr → Option ℕ
  | Z n => some n
  | S n => some n
  | T _ n => some n
  | J _ _ _ => none

/-- The maximum register index referenced by an instruction. -/
@[scoped grind =]
def max_register : Instr → ℕ
  | Z n => n
  | S n => n
  | T m n => max m n
  | J m n _ => max m n

/-- Shift all jump targets in an instruction by `offset`.
Used when concatenating programs to maintain correct jump destinations. -/
@[scoped grind =]
def shift_jumps (offset : ℕ) : Instr → Instr
  | Z n => Z n
  | S n => S n
  | T m n => T m n
  | J m n q => J m n (q + offset)

/-- Shift all register references in an instruction by `offset`.
Used to isolate register usage when composing programs. -/
@[scoped grind =]
def shift_registers (offset : ℕ) : Instr → Instr
  | Z n => Z (n + offset)
  | S n => S (n + offset)
  | T m n => T (m + offset) (n + offset)
  | J m n q => J (m + offset) (n + offset) q

end Instr

/-! ## Register State -/

/-- Register state: maps register indices to natural number contents.

Uses the functional representation `ℕ → ℕ` for efficiency with rewrites,
following the advice from the `grind` tactic documentation. -/
abbrev State := ℕ → ℕ

namespace State

/-- The zero state where all registers contain 0. -/
@[scoped grind =]
def zero : State := fun _ => 0

/-- Read the contents of register n. -/
@[scoped grind =]
def read (σ : State) (n : ℕ) : ℕ := σ n

/-- Write value v to register n. -/
@[scoped grind =]
def write (σ : State) (n : ℕ) (v : ℕ) : State := Function.update σ n v

/-- Initialize state with input values in registers 0, 1, ..., k-1.
Registers beyond the inputs are initialized to 0. -/
@[scoped grind =]
def of_inputs (inputs : List ℕ) : State := fun n => inputs.getD n 0

/-- Extract output from register 0. -/
@[scoped grind =]
def output (σ : State) : ℕ := σ 0

end State

/-! ## Programs -/

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

end Program

/-! ## Machine Configuration -/

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

instance : Inhabited Config := ⟨init []⟩

instance : Repr Config where
  reprPrec c _ := s!"Config(pc={c.pc})"

end Config

end Cslib.Urm

end
