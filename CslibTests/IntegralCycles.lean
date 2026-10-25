/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Foundations.RelationAlgebra.IntegralCycles
import Cslib.Foundations.RelationAlgebra.IntegralSmall

/-! Tests for the `integral_cycles%` elaborator and its diagnostics. -/

namespace CslibTests

open Cslib.RelationAlgebra

-- Valid configurations include omitted options, single names, lists, and converses.
example : AtomStructure (IntegralAtom 0 0) := integral_cycles%

example : AtomStructure (IntegralAtom 1 0) := integral_cycles% (symm := a)

example : AtomStructure (IntegralAtom 1 0) :=
  integral_cycles% (symm := [a]) (a~, a, a)

example : AtomStructure (IntegralAtom 2 0) :=
  integral_cycles% (symm := [a, b]) (a, b, b)

example : AtomStructure (IntegralAtom 0 1) :=
  integral_cycles% (nsymm := a) (a, a, a~)

example : AtomStructure (IntegralAtom 1 1) :=
  integral_cycles% (symm := a) (nsymm := b) (a, b, b~)

--- check that a few small relation algebras have the cycles we expected
section OneConv

open IntegralAtom

theorem oneConv_zero_diversity_cycles : ∀ (b c d : Bool),
    (nsymm 0 b, nsymm 0 c, nsymm 0 d) ∈ (oneConv 0).cycles ↔ b = c ∧ d = !b := by
  dsimp [oneConv, ofCycles]
  decide +kernel

theorem oneConv_one_diversity_cycles : ∀ (b c d : Bool),
    (nsymm 0 b, nsymm 0 c, nsymm 0 d) ∈ (oneConv 1).cycles ↔ b ≠ c ∨ d = b := by
  dsimp [oneConv, ofCycles]
  decide +kernel

theorem oneConv_two_diversity_cycles : ∀ (b c d : Bool),
    (nsymm 0 b, nsymm 0 c, nsymm 0 d) ∈ (oneConv 2).cycles := by
  dsimp [oneConv, ofCycles]
  decide +kernel

end OneConv

-- Atom names must be unique, including across the two options.
/-- error: duplicate atom name 'a' -/
#guard_msgs in
example : AtomStructure (IntegralAtom 2 0) := integral_cycles% (symm := [a, a])

/-- error: duplicate atom name 'a' -/
#guard_msgs in
example : AtomStructure (IntegralAtom 0 2) := integral_cycles% (nsymm := [a, a])

/-- error: duplicate atom name 'a' -/
#guard_msgs in
example : AtomStructure (IntegralAtom 1 1) := integral_cycles% (symm := a) (nsymm := a)

-- Invalid atom names are reported before checking the cycles.
/-- error: expected an atom name -/
#guard_msgs in
example : AtomStructure (IntegralAtom 2 0) := integral_cycles% (symm := [a, 1])

/-- error: undeclared atom 'b' -/
#guard_msgs in
example : AtomStructure (IntegralAtom 1 0) := integral_cycles% (symm := a) (b, a, a)

/-- error: undeclared atom 'b' -/
#guard_msgs in
example : AtomStructure (IntegralAtom 0 1) := integral_cycles% (nsymm := a) (a, b~, a)

-- Both empty and nonempty generators can fail the associativity check.
/-- error: `integral_cycles%` could not prove associativity of the generated cycles -/
#guard_msgs in
example : AtomStructure (IntegralAtom 2 0) := integral_cycles% (symm := [a, b])

/-- error: `integral_cycles%` could not prove associativity of the generated cycles -/
#guard_msgs in
example : AtomStructure (IntegralAtom 2 0) := integral_cycles% (symm := [a, b]) (a, a, a)

end CslibTests
