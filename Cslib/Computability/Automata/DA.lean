/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.NA

/-! # Deterministic Automaton

A Deterministic Automaton (DA) is an automaton defined by a transition function.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

namespace Cslib

open List

structure DA (State : Type*) (Symbol : Type*) where
  /-- The initial state of the automaton. -/
  start : State
  /-- The transition function of the automaton. -/
  tr : State → Symbol → State

namespace DA

variable {State State1 State2 : Type*} {Symbol : Type*}

/-- Extended transition function. -/
@[scoped grind =]
def mtr (DA : DA State Symbol) (s : State) (xs : List Symbol) := xs.foldl DA.tr s

@[simp, scoped grind =]
theorem mtr_nil_eq {DA : DA State Symbol} {s : State} : DA.mtr s [] = s := rfl

@[scoped grind =]
def prod (da1 : DA State1 Symbol) (da2 : DA State2 Symbol) : DA (State1 × State2) Symbol where
  start := (da1.start, da2.start)
  tr := fun (s1, s2) x ↦ (da1.tr s1 x, da2.tr s2 x)

@[simp, scoped grind =]
theorem prod_mtr_eq (da1 : DA State1 Symbol) (da2 : DA State2 Symbol)
    (s : State1 × State2) (xs : List Symbol) :
    (da1.prod da2).mtr s xs = (da1.mtr s.fst xs, da2.mtr s.snd xs) := by
  induction xs generalizing s <;> grind

end DA

end Cslib
