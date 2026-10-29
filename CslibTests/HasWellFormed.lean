/-
Copyright (c) 2026 Sean D. Stoneburner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean D. Stoneburner
-/
import Cslib.Algorithms.Lean.TimeM
import Cslib.Foundations.Syntax.HasWellFormed

open Cslib.Algorithms.Lean

/-!
# Syntax Collision Test
This file tests that the `✓` prefix macro from `TimeM` does not collide with
the `✓` postfix notation from `HasWellFormed` across line breaks.
-/

def testParserCollision (n : Nat) : TimeM Nat Nat := do
  let m := n
  ✓ return m

-- Ensure the postfix notation still functions correctly when attached without whitespace
variable {α : Type*} [Cslib.HasWellFormed α] (x : α)

/-- info: Cslib.HasWellFormed.wf x : Prop -/
#guard_msgs in
#check x✓
