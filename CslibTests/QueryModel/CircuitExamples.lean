/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.Models.NCCircuits
public import Mathlib

@[expose] public section

/-!
# Examples of Progs for Circuits

This file contains examples and tests of fan-in 2 circuits written in the Prog Model
-/
namespace CslibTests

open Cslib Algorithms Prog

open Circuit in
def exCircuit1 : Prog (Circuit Bool) Bool := do
  let x := const 0 true
  let y := const 1 true
  let z := add 2 x y
  let w := mul 3 x y
  add 4 z w

-- /--
-- info: true
-- -/
-- #guard_msgs in
-- #eval exCircuit1.eval circModel

-- /--
-- info: { depth := 2, size := 5 }
-- -/
-- #guard_msgs in
-- #eval exCircuit1.time circModel

open Circuit in
def exCircuit2 : Prog (Circuit ℚ) ℚ := do
  let x := const 0 (1 : ℚ)
  let y := const 1 (2 : ℚ)
  let z := add 2 x y
  mul 4 z z

-- /--
-- info: 9
-- -/
-- #guard_msgs in
-- #eval exCircuit2.eval circModel

-- /--
-- info: true
-- -/
-- #guard_msgs in
-- #eval exCircuit2.time circModel == ⟨2,4⟩

open Circuit in
def exCircuit3 (x y : Circuit ℚ ℚ) : Prog (Circuit ℚ) ℚ := do
  let z := add 2 x y
  let w := mul 3 x y
  mul 4 z w

-- /--
-- info: true
-- -/
-- #guard_msgs in
-- #eval (exCircuit3 (.const 0 (1 : ℚ)) (.const 1 (21 : ℚ))).eval circModel == 462

-- /--
-- info: true
-- -/
-- #guard_msgs in
-- #eval (exCircuit3 (.const 0 (1 : ℚ)) (.const 1 (21 : ℚ))).time circModel == ⟨2,5⟩


open Circuit in
def CircAnd (n : ℕ) (x : Fin n → Circuit Bool Bool) : Circuit Bool Bool :=
  match n with
  | 0 => const n true
  | m + 1 =>
      let x_head := x 0
      let x_cons := CircAnd m (Fin.tail x)
      mul (n + m + 1) x_head x_cons

def execCircAnd (x : Fin n → Circuit Bool Bool) : Prog (Circuit Bool) Bool := do
  CircAnd n x

-- /--
-- info: true
-- -/
-- #guard_msgs in
-- #eval (execCircAnd ![.const 0 true, .const 1 true, .const 2 true]).eval circModel == true

-- /--
-- info: true
-- -/
-- #guard_msgs in
-- #eval (execCircAnd ![.const 0 true, .const 1 true, .const 2 true]).time circModel == ⟨3,5⟩


end CslibTests
