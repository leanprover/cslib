/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai
-/

import Cslib.Algorithms.Lean.TimeM

namespace CslibTests

open Cslib.Algorithms.Lean

/-- Test for `TimeM.run` and `TimeM.mapTime`. -/
example : (TimeM.run (TimeM.tick 5 10)) = (5, 10) := rfl

example : (TimeM.run (TimeM.mapTime (· * 2) (TimeM.tick 5 10))) = (5, 20) := rfl

example : (TimeM.run (do
  let x ← TimeM.tick 1 1
  let y ← TimeM.tick 2 2
  return x + y)) = (3, 3) := rfl

end CslibTests
