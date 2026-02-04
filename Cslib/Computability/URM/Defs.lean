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

- `URM.Instr`: The four URM instructions (Z, S, T, J)
- `URM.Regs`: Register contents as a function `ℕ → ℕ`
- `URM.Program`: A finite sequence of instructions
- `URM.State`: Machine state (program counter + registers)

## References

* [N.J. Cutland, *Computability: An Introduction to Recursive Function Theory*][Cutland1980]
* [J.C. Shepherdson and H.E. Sturgis,
  *Computability of Recursive Functions*][ShepherdsonSturgis1963]
-/

@[expose] public section

namespace Cslib.URM

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
def readsFrom : Instr → Finset ℕ
  | Z _ => ∅
  | S n => {n}
  | T m _ => {m}
  | J m n _ => {m, n}

/-- The register written to by an instruction, if any. -/
@[scoped grind =]
def writesTo : Instr → Option ℕ
  | Z n => some n
  | S n => some n
  | T _ n => some n
  | J _ _ _ => none

/-- The maximum register index referenced by an instruction. -/
@[scoped grind =]
def maxRegister : Instr → ℕ
  | Z n => n
  | S n => n
  | T m n => max m n
  | J m n _ => max m n

/-- Shift all jump targets in an instruction by `offset`.
Used when concatenating programs to maintain correct jump destinations. -/
@[scoped grind =]
def shiftJumps (offset : ℕ) : Instr → Instr
  | Z n => Z n
  | S n => S n
  | T m n => T m n
  | J m n q => J m n (q + offset)

/-- Shift all register references in an instruction by `offset`.
Used to isolate register usage when composing programs. -/
@[scoped grind =]
def shiftRegisters (offset : ℕ) : Instr → Instr
  | Z n => Z (n + offset)
  | S n => S (n + offset)
  | T m n => T (m + offset) (n + offset)
  | J m n q => J (m + offset) (n + offset) q

end Instr

/-! ## Register Contents -/

/-- Register contents: maps register indices to natural number contents.

Uses the functional representation `ℕ → ℕ` for efficiency with rewrites,
following the advice from the `grind` tactic documentation. -/
abbrev Regs := ℕ → ℕ

namespace Regs

/-- The zero registers where all registers contain 0. -/
@[scoped grind =]
def zero : Regs := fun _ => 0

/-- Read the contents of register n. -/
@[scoped grind =]
def read (σ : Regs) (n : ℕ) : ℕ := σ n

/-- Write value v to register n. -/
@[scoped grind =]
def write (σ : Regs) (n : ℕ) (v : ℕ) : Regs := Function.update σ n v

/-- Initialize registers with input values in registers 0, 1, ..., k-1.
Registers beyond the inputs are initialized to 0. -/
@[scoped grind =]
def ofInputs (inputs : List ℕ) : Regs := fun n => inputs.getD n 0

/-- Extract output from register 0. -/
@[scoped grind =]
def output (σ : Regs) : ℕ := σ 0

end Regs

/-! ## Programs -/

/-- A URM program is a list of instructions. -/
abbrev Program := List Instr

namespace Program

/-- The maximum register index referenced by any instruction in the program. -/
@[scoped grind =]
def maxRegister (p : Program) : ℕ :=
  p.foldl (fun acc instr => max acc instr.maxRegister) 0

/-- Shift all jump targets in a program by `offset`.
Used when concatenating programs: the second program's jumps must be adjusted
by the length of the first program. -/
@[scoped grind =]
def shiftJumps (p : Program) (offset : ℕ) : Program :=
  p.map (Instr.shiftJumps offset)

/-- Shift all register references in a program by `offset`.
Used to isolate register usage when composing programs. -/
@[scoped grind =]
def shiftRegisters (p : Program) (offset : ℕ) : Program :=
  p.map (Instr.shiftRegisters offset)

end Program

/-! ## Machine State -/

/-- Machine state: program counter (0-indexed) and register contents. -/
structure State where
  /-- Program counter (0-indexed). -/
  pc : ℕ
  /-- Register contents. -/
  regs : Regs

namespace State

/-- Initial state for a program with given inputs.
The program counter starts at 0, and inputs are loaded into registers 0, 1, .... -/
@[scoped grind =]
def init (inputs : List ℕ) : State := ⟨0, Regs.ofInputs inputs⟩

/-- A state is halted if the program counter is at or beyond the program length. -/
@[scoped grind =]
def isHalted (s : State) (p : Program) : Prop := p.length ≤ s.pc

instance (s : State) (p : Program) : Decidable (s.isHalted p) :=
  inferInstanceAs (Decidable (p.length ≤ s.pc))

instance : Inhabited State := ⟨init []⟩

instance : Repr State where
  reprPrec s _ := s!"State(pc={s.pc})"

end State

end Cslib.URM

end
