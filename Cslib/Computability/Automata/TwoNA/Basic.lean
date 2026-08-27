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

A Nondeterministic Two-Way Automaton (TwoNA) reads a finite input word on a tape and may move its
input head in either direction. A transition reads the symbol under the head and, besides changing
the state, moves the head one cell to the left, keeps it in place, or moves it one cell to the
right.

Once it leaves the word to the right, the automaton cannot move back to the word. A run is accepting
if it ends in an accepting state with the head just past the end of the input.

## Main definitions

* `TwoNA`, the automaton itself
* `TwoNACfg`, a configuration of a `TwoNA` running on a fixed input: a state together with a head
  position.
* `TwoNA.Step`, The single-step relation between configurations.

## Implementation notes

The definition of `TwoNA` is kept close to [Vardi][Vardi1989]'s, because the main point is to
prove equivalence to `NA.FinAcc`. This means we do not allow the head to move off the input to the
left, but also do not provide an end marker. Once the head moves off to the right, it cannot move
back into the word.

## References

* [Moshe Y. Vardi, *A Note on the Reduction of Two-Way Automata to One-Way Automata*][Vardi1989]

-/

@[expose] public section

namespace Cslib.Automata

variable {State Symbol : Type*}

/-- The type of the transition relation of a two-way automaton. -/
def TwoNATr (State Symbol : Type*) := State → Symbol → SignType → State → Prop

/-- A nondeterministic two-way automaton: a transition relation that reads an input symbol and
moves the input head, together with a set of initial and a set of accepting states. -/
structure TwoNA (State Symbol : Type*) where
  /-- The transition relation. `Tr q x m q'` means that, while reading the symbol `x`, the
  automaton can move from state `q` to state `q'` and move its head according to `m`. -/
  Tr : TwoNATr State Symbol
  /-- The set of initial states of the automaton. -/
  start : Set State
  /-- The set of accepting states of the automaton. -/
  accept : Set State

/-- The configuration of a two-way nondeterministic automaton. -/
@[ext]
structure TwoNACfg (State Symbol : Type*) (input : List Symbol) where
  /-- The state of the automaton. -/
  state : State
  /-- The input head position of the automaton: it can be on any symbol of the input or on the
  position one step to the right of the input. -/
  pos : Fin (input.length + 1)


def TwoNACfg.IsInitial (a : TwoNA State Symbol) {input : List Symbol}
    (c : TwoNACfg State Symbol input) : Prop :=
  c.state ∈ a.start ∧ c.pos = 0

def TwoNACfg.IsAccepting (a : TwoNA State Symbol) {input : List Symbol}
    (c : TwoNACfg State Symbol input) : Prop :=
  c.state ∈ a.accept ∧ c.pos = Fin.last _

------------------- via LTS -------------------------

def TwoNATr.toCfgTr {State Symbol : Type*} (tr : TwoNATr State Symbol) (input : List Symbol) :
    TwoNACfg State Symbol input → Symbol × SignType → TwoNACfg State Symbol input → Prop
  | c, (x, m), c' =>
    some x = input[c.pos]? ∧
    tr c.state x m c'.state ∧
    (c'.pos : ℤ) = (c.pos : ℤ) + (m.cast : ℤ)

def TwoNA.toCfgLTS {State Symbol : Type*} (a : TwoNA State Symbol) (input : List Symbol) :
    NA.FinAcc (TwoNACfg State Symbol input) (Symbol × SignType) where
  Tr := a.Tr.toCfgTr input
  start := { c | c.IsInitial a }
  accept := { c | c.IsAccepting a }

@[simp, scoped grind =]
instance : Acceptor (TwoNA State Symbol) Symbol where
  Accepts (a : TwoNA State Symbol) (input : List Symbol) :=
    ∃ μs, Acceptor.Accepts (a.toCfgLTS input) μs

------------------ alternative ---------------------------

def TwoNA.Step {State Symbol : Type*} (a : TwoNA State Symbol) {input : List Symbol}
    (c c' : TwoNACfg State Symbol input) : Prop :=
  ∃ x m,
    a.Tr c.state x m c'.state ∧
    some x = input[c.pos]? ∧
    (c'.pos : ℤ) = (c.pos : ℤ) + (m.cast : ℤ)

@[simp, scoped grind =]
instance : Acceptor (TwoNA State Symbol) Symbol where
  Accepts (a : TwoNA State Symbol) (input : List Symbol) :=
    ∃ (init final : TwoNACfg State Symbol input),
    ∃ cfgs : List (TwoNACfg State Symbol input),
    init.IsInitial a ∧ final.IsAccepting a ∧
    cfgs.IsChainFromTo a.Step init final

end Cslib.Automata
