/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuits.Formula.Std

namespace CslibTests

open Cslib.Circuits

/-! Tests for Boolean formulas over the standard basis. -/

inductive TestVar where
  | x | y | z
  deriving DecidableEq

def assignment : TestVar → Bool
  | .x => true
  | .y => false
  | .z => true

def x : Formula TestVar NCOp := .var .x
def y : Formula TestVar NCOp := .var .y
def z : Formula TestVar NCOp := .var .z

/-! ### Evaluation tests -/

example : (Formula.and x y).eval assignment = some false := by
  simp [x, y, assignment]

example : (Formula.or x y).eval assignment = some true := by
  simp [x, y, assignment]

example : (Formula.not y).eval assignment = some true := by
  simp [y, assignment]

example : (Formula.not (Formula.or x z)).eval assignment = some false := by
  simp [x, z, assignment]

example : (Formula.and x (Formula.or y z)).eval assignment = some true := by
  simp [x, y, z, assignment]

/-! ### Double negation -/

example : (Formula.not (Formula.not x)).eval assignment = some true := by
  simp [x, assignment]

/-! ### Size tests -/

example : (Formula.and x y).size = 3 := by
  simp [x, y, Formula.and]

example : (Formula.not x).size = 2 := by
  simp [x, Formula.not]

example : (Formula.or (Formula.and x y) z).size = 5 := by
  simp [x, y, z, Formula.and, Formula.or]

/-! ### Depth tests -/

example : (Formula.and x y).depth = 1 := by
  simp [x, y, Formula.and]

example : (Formula.not x).depth = 1 := by
  simp [x, Formula.not]

example : (Formula.or (Formula.and x y) z).depth = 2 := by
  simp [x, y, z, Formula.and, Formula.or]

/-! ### De Morgan via theorem -/

example (v : TestVar → Bool) (a b : Formula TestVar NCOp) :
    (Formula.not (Formula.and a b)).eval v =
    (Formula.or (Formula.not a) (Formula.not b)).eval v :=
  Formula.deMorgan_and v a b

end CslibTests
