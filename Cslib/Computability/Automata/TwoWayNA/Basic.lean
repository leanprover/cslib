/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Sign.Basic
public import Cslib.Foundations.Data.List.IsChainFromTo

/-! # Nondeterministic Two-Way Automaton

A Nondeterministic Two-Way Automaton (`TwoWayNA`) reads a finite input word on a tape and may move
its input head in either direction. A transition reads the symbol under the head and, besides
changing the state, moves the head one cell to the left, keeps it in place, or moves it one cell to
the right.

The input head cannot leave the input word to the left and once it leaves the word to the right,
it stops. A run is accepting if and only if it ends in an accepting state with the head just past
the end of the input.

## Main definitions

* `TwoWayNA`, the automaton itself
* `TwoWayNACfg`, a configuration of a `TwoWayNA`: Its input plus a state and the head position.
* `TwoWayNA.Step`, The single-step relation between configurations.

## Implementation notes

The definition of `TwoWayNA` is kept close to [Vardi][Vardi1989]'s, because the main point is to
prove equivalence to `NA.FinAcc`. This means we do not allow the head to move off the input to the
left, but also do not provide an end marker. Once the head moves off to the right, it cannot move
back into the word.

## References

* [Moshe Y. Vardi, *A Note on the Reduction of Two-Way Automata to One-Way Automata*][Vardi1989]

-/

@[expose] public section

namespace Cslib.Automata

variable {State Symbol : Type*}

/-- A nondeterministic two-way automaton: a transition relation that reads an input symbol and
moves the input head, together with a set of initial and a set of accepting states. -/
structure TwoWayNA (State Symbol : Type*) where
  /-- The transition relation. `Tr q x m q'` means that, while reading the symbol `x`, the
  automaton attempts to transition from state `q` to state `q'` and move its head according to
  `m`. -/
  Tr (q : State) (x : Symbol) (m : SignType) (q' : State) : Prop
  /-- The set of initial states of the automaton. -/
  start : Set State
  /-- The set of accepting states of the automaton. -/
  accept : Set State

/-- The configuration of a two-way nondeterministic automaton. -/
@[ext]
structure TwoWayNACfg (State Symbol : Type*) where
  /-- The original input to the automaton. -/
  input : List Symbol
  /-- The state of the automaton. -/
  state : State
  /-- The input head position of the automaton: it can be on any symbol of the input or on the
  position one step to the right of the input. -/
  pos : Fin (input.length + 1)

/-- This defines the set of initial configurations on a specific input. -/
def TwoWayNACfg.IsInitialForInput (a : TwoWayNA State Symbol) (c : TwoWayNACfg State Symbol)
    (input : List Symbol) : Prop :=
  c.state ∈ a.start ∧ c.pos = 0 ∧ c.input = input

/-- If a configuration is a accepting. -/
def TwoWayNACfg.IsAccepting (a : TwoWayNA State Symbol) (c : TwoWayNACfg State Symbol) : Prop :=
  c.state ∈ a.accept ∧ c.pos = Fin.last _

/-- Returns a nondeterministic finite acceptor on the configurations as states, accepting exactly
the runs of the two-way automaton on `input` that end in an accepting configuration. -/
def TwoWayNA.toCfgNAFinAcc {State Symbol : Type*} (a : TwoWayNA State Symbol)
    (input : List Symbol) :
    NA.FinAcc (TwoWayNACfg State Symbol) (Symbol × SignType) where
  Tr
    | c, (x, m), c' =>
      c.input = c'.input ∧
      some x = c.input[c.pos]? ∧
      a.Tr c.state x m c'.state ∧
      (c'.pos : ℤ) = (c.pos : ℤ) + (m.cast : ℤ)
  start := { c | c.IsInitialForInput a input }
  accept := { c | c.IsAccepting a }

@[simp, scoped grind =]
instance : Acceptor (TwoWayNA State Symbol) Symbol where
  Accepts (a : TwoWayNA State Symbol) (input : List Symbol) :=
    ∃ μs, Acceptor.Accepts (a.toCfgNAFinAcc input) μs

end Cslib.Automata
