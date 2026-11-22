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

-- The generators are not checked by the elaborator, so candidates need not be associative.
example : AtomStructure (IntegralAtom 2 0) := integral_cycles% (symm := [a, b])

-- `integral_cycles_lawful` checks the atom structure axioms, unfolding definitions as needed.
example : LawfulAtomStructure (integral_cycles% : AtomStructure (IntegralAtom 0 0)) := by
  integral_cycles_lawful

example : LawfulAtomStructure (integral_cycles% (symm := a) (nsymm := b) (a, b, b~)) := by
  integral_cycles_lawful

example (i : Fin 3) : LawfulAtomStructure (IntegralAtom.oneConv i) := by
  fin_cases i <;> integral_cycles_lawful

example : Cslib.RelationAlgebra (ComplexAlgebra (IntegralAtom.twoSymm 3)) := inferInstance

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
/--
error: `integral_cycles_lawful` could not prove associativity of the generated cycles
---
error: Tactic `decide` proved that the proposition
  (checkRows conv fun r u =>
      maskRow
        (Finset.fold (fun x1 x2 => x1 ||| x2) 0 (fun a => maskOfFinset (⇑cycleIndex) (cycleOrbit a))
          (Finset.empty ∪ Finset.image (fun a => (one, a, a)) Finset.univ))
        (1 + 2 + 2 * 0) ↑r.atomIndex ↑u.atomIndex) =
    true
is false
-/
#guard_msgs in
open IntegralAtom in
example : LawfulAtomStructure (integral_cycles% (symm := [a, b])) := by
  integral_cycles_lawful

/--
error: `integral_cycles_lawful` could not prove associativity of the generated cycles
---
error: Tactic `decide` proved that the proposition
  (checkRows conv fun r u =>
      maskRow
        (Finset.fold (fun x1 x2 => x1 ||| x2) 0 (fun a => maskOfFinset (⇑cycleIndex) (cycleOrbit a))
          (insert (IntegralAtom.symm 0, IntegralAtom.symm 0, IntegralAtom.symm 0) Finset.empty ∪
            Finset.image (fun a => (one, a, a)) Finset.univ))
        (1 + 2 + 2 * 0) ↑r.atomIndex ↑u.atomIndex) =
    true
is false
-/
#guard_msgs in
open IntegralAtom in
example : LawfulAtomStructure (integral_cycles% (symm := [a, b]) (a, a, a)) := by
  integral_cycles_lawful

-- Generators containing the identity atom are rejected.
/--
error: `integral_cycles_lawful` could not prove that all generators are diversity cycles
---
error: Tactic `decide` proved that the proposition
  ∀ c ∈ {(IntegralAtom.one, IntegralAtom.symm 0, IntegralAtom.symm 0)},
    match c with
    | (r, u, t) => r ≠ IntegralAtom.one ∧ u ≠ IntegralAtom.one ∧ t ≠ IntegralAtom.one
is false
-/
#guard_msgs in
example : LawfulAtomStructure
    (IntegralAtom.ofCycles (s := 1) (n := 0) {(.one, .symm 0, .symm 0)}) := by
  integral_cycles_lawful

-- The goal must be an `ofCycles` atom structure with closed generators.
/--
error: `integral_cycles_lawful` could not reduce the atom structure to an application of `ofCycles`
  A
-/
#guard_msgs in
example (A : AtomStructure ℕ) : LawfulAtomStructure A := by
  integral_cycles_lawful

/--
error: `integral_cycles_lawful` requires closed generators, but got
  g
-/
#guard_msgs in
example (g : Finset (IntegralAtom.Cycle 1 0)) : LawfulAtomStructure (IntegralAtom.ofCycles g) := by
  integral_cycles_lawful

/--
error: `integral_cycles_lawful` expects a `LawfulAtomStructure` goal, but got
  True
-/
#guard_msgs in
example : True := by
  integral_cycles_lawful

-- Errors other than a failed check are reported as they are.
/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : LawfulAtomStructure (integral_cycles% (symm := a) (nsymm := b) (a, b, b~)) := by
  set_option maxRecDepth 12 in integral_cycles_lawful

end CslibTests
