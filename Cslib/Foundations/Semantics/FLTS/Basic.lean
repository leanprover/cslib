/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

@[expose] public section

/-! # Functional Labelled Transition System (FLTS)

A Functional Labelled Transition System is a special case of an `LTS` where transitions are
determined by a function.

This is a generalisation of deterministic finite-state machines.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

namespace Cslib

/--
A Functional Labelled Transition System (`FLTS`) for a type of states (`State`) and a type of
transition labels (`Label`) consists of a labelled transition function (`tr`).
-/
structure FLTS (State Label : Type*) where
  /-- The transition function. -/
  tr : State → Label → State

namespace FLTS

variable {State Label : Type*}

/-- Extended transition function.

Implementation note: compared to [Hopcroft2006], the definition consumes the input list of symbols
from the left (instead of the right), in order to match the way lists are constructed.
-/
@[scoped grind =]
def mtr (flts : FLTS State Label) (s : State) (μs : List Label) := μs.foldl flts.tr s

@[simp, scoped grind =]
theorem mtr_nil_eq {flts : FLTS State Label} {s : State} : flts.mtr s [] = s := rfl

@[simp, scoped grind =]
theorem mtr_concat_eq {flts : FLTS State Label} {s : State} {μs : List Label} {μ : Label} :
    flts.mtr s (μs ++ [μ]) = flts.tr (flts.mtr s μs) μ := by
  grind

end FLTS

end Cslib
