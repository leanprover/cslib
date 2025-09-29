/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.DA
import Cslib.Foundations.Semantics.LTS.Basic

set_option linter.style.longLine false in
/-! # Deterministic Finite-State Automata

A Deterministic Finite Automaton (DFA) is a finite-state machine that accepts or rejects
a finite string.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

/-- A Deterministic Finite-State Automaton (DFA) consists of a labelled transition function
`tr` over finite sets of states and labels (called symbols), a starting state `start` and a finite
set of accepting states `accept`. -/
structure DFA (State : Type _) (Symbol : Type _) extends DA State Symbol where
  /-- Accept states. -/
  accept : Finset State
  /-- The automaton is finite-state. -/
  finite_state : Finite State
  /-- The type of symbols (also called 'alphabet') is finite. -/
  finite_symbol : Finite Symbol

namespace DFA

/-- Extended transition function.

Implementation note: compared to [Hopcroft2006], the definition consumes the input list of symbols
from the left (instead of the right), in order to follow the way lists are constructed.
-/
@[grind]
def mtr (dfa : DFA State Symbol) (s : State) (xs : List Symbol) :=
  match xs with
  | [] => s
  | x :: xs => dfa.mtr (dfa.tr s x) xs

@[grind]
theorem mtr_nil_eq {dfa : DFA State Symbol} : dfa.mtr s [] = s := by rfl

/-- A DFA accepts a trace if there is a multi-step accepting derivative with that trace from
the start state. -/
@[grind]
def Accepts (dfa : DFA State Symbol) (μs : List Symbol) :=
  (dfa.mtr dfa.start μs) ∈ dfa.accept

/-- The language of a DFA is the set of traces that it accepts. -/
@[grind]
def language (dfa : DFA State Symbol) : Set (List Symbol) :=
  { μs | dfa.Accepts μs }

/-- A trace is accepted by a DFA iff it is in the language of the DFA. -/
@[grind]
theorem accepts_mem_language (dfa : DFA State Symbol) (μs : List Symbol) :
  dfa.Accepts μs ↔ μs ∈ dfa.language := by rfl

section LTS

/-- `DFA` is a special case of `LTS`. -/
@[grind]
def toLTS (dfa : DFA State Symbol) : LTS State Symbol :=
  LTS.mk (fun s1 μ s2 => dfa.tr s1 μ = s2)

instance : Coe (DFA State Symbol) (LTS State Symbol) where
  coe := toLTS

/-- `DFA.toLTS` correctly characterises transitions. -/
@[grind]
theorem toLTS_tr {dfa : DFA State Symbol} :
  dfa.toLTS.Tr s1 μ s2 ↔ dfa.tr s1 μ = s2 := by
  rfl

/-- `DFA.toLTS` correctly characterises multistep transitions. -/
@[grind]
theorem toLTS_mtr {dfa : DFA State Symbol} :
  dfa.toLTS.MTr s1 xs s2 ↔ dfa.mtr s1 xs = s2 := by
  constructor <;> intro h
  case mp =>
    induction h <;> grind
  case mpr =>
    induction xs generalizing s1
    case nil => grind
    case cons x xs ih =>
      apply LTS.MTr.stepL (s2 := dfa.tr s1 x) <;> grind

/-- The LTS induced by a DFA is deterministic. -/
@[grind]
theorem toLTS_deterministic (dfa : DFA State Symbol) : dfa.toLTS.Deterministic := by
  grind

/-- The LTS induced by a DFA is finite-state. -/
@[grind]
theorem toLTS_finiteState (dfa : DFA State Symbol) : dfa.toLTS.FiniteState :=
  dfa.finite_state

end LTS

end DFA
