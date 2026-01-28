/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Cslib.Init
public import Mathlib.Logic.Function.Basic

/-! # URM State

This file defines the register state for URMs.

## Main definitions

- `Urm.State`: Register contents as a function `ℕ → ℕ`
- `State.read`: Read the contents of a register
- `State.write`: Write a value to a register
- `State.of_inputs`: Initialize state with input values
-/

@[expose] public section

namespace Cslib.Urm

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

-- Basic lemmas about state operations

@[simp, scoped grind =]
theorem write_read_self (σ : State) (n v : ℕ) : (σ.write n v).read n = v := by
  simp only [write, read, Function.update_self]

@[simp, scoped grind =]
theorem write_read_of_ne (σ : State) (m n v : ℕ) (h : m ≠ n) :
    (σ.write n v).read m = σ.read m := by
  simp only [write, read, Function.update_of_ne h]

end State

end Cslib.Urm

end
