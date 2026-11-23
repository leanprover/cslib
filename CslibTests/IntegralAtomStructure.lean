/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure

namespace CslibTests

open Cslib.RelationAlgebra.IntegralAlgebra.IsoClass

universe u

-- These tests only inspect the goals that `expand_ofAtoms` produces, so they are left unproved.
set_option warn.sorry false

-- With the total written as a sum, the goal is the sum over the classes, in the same order.
example : (ofAtoms.{u} 5).encard = 83 + 1316 + 3013 := by
  expand_ofAtoms
  guard_target =
    (ofType.{u} 0 2).encard + (ofType.{u} 2 1).encard + (ofType.{u} 4 0).encard =
      83 + 1316 + 3013
  sorry

example : (ofAtoms.{u} 6).encard = 47965 + 988464 + 3849920 := by
  expand_ofAtoms
  guard_target =
    (ofType.{u} 1 2).encard + (ofType.{u} 3 1).encard + (ofType.{u} 5 0).encard =
      47965 + 988464 + 3849920
  sorry

example : (ofAtoms.{u} 7).encard = 4492953 + 2186435732 + 50265788140 + 292352449486 := by
  expand_ofAtoms
  guard_target =
    (ofType.{u} 0 3).encard + (ofType.{u} 2 2).encard + (ofType.{u} 4 1).encard +
      (ofType.{u} 6 0).encard = 4492953 + 2186435732 + 50265788140 + 292352449486
  sorry

-- With the total written as a single number, the goal is still split.
example : (ofAtoms.{u} 5).encard = 4412 := by
  expand_ofAtoms
  guard_target =
    (ofType.{u} 0 2).encard + (ofType.{u} 2 1).encard + (ofType.{u} 4 0).encard = 4412
  sorry

example : (ofAtoms.{u} 6).encard = 4886349 := by
  expand_ofAtoms
  guard_target =
    (ofType.{u} 1 2).encard + (ofType.{u} 3 1).encard + (ofType.{u} 5 0).encard = 4886349
  sorry

example : (ofAtoms.{u} 7).encard = 344809166311 := by
  expand_ofAtoms
  guard_target =
    (ofType.{u} 0 3).encard + (ofType.{u} 2 2).encard + (ofType.{u} 4 1).encard +
      (ofType.{u} 6 0).encard = 344809166311
  sorry

-- The argument must be a numeral.
/-- error: `simp` made no progress -/
#guard_msgs in
example (k : ℕ) : (ofAtoms.{u} k).encard = 4412 := by
  expand_ofAtoms

end CslibTests
