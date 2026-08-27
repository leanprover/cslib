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

/-- A nondeterministic two-way automaton is a nondeterministic automaton whose labels
consist of an input symbol and an input head movement. -/
def TwoNA (State Symbol : Type*) := NA State (Symbol × SignType)

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

def TwoNA.Step (a : TwoNA State Symbol) (input : List Symbol)
    (c c' : TwoNACfg State Symbol input) : Prop :=
  ∃ m, ∃ _ : (c.pos : ℕ) < input.length,
    a.Tr c.state (input[c.pos], m) c'.state ∧ (c'.pos : ℤ) = (c.pos : ℤ) + (m.cast : ℤ)

/-- A nondeterministic two-way automaton that accepts finite strings (lists of symbols). -/
structure TwoNAFinAcc (State Symbol : Type*) extends TwoNA State Symbol where
  /-- The set of accepting states. -/
  accept : Set State

def TwoNACfg.IsAccepting (a : TwoNAFinAcc State Symbol) {input : List Symbol}
    (c : TwoNACfg State Symbol input) : Prop :=
  c.state ∈ a.accept ∧ c.pos = Fin.last _

@[simp, scoped grind =]
instance : Acceptor (TwoNAFinAcc State Symbol) Symbol where
  Accepts (a : TwoNAFinAcc State Symbol) (xs : List Symbol) :=
    ∃ (chain : List (TwoNACfg State Symbol xs)) (s s' : TwoNACfg State Symbol xs),
      chain.IsChainFromTo (TwoNA.Step a.toNA xs) s s' ∧
      s.IsInitial a.toNA ∧ s'.IsAccepting a


end Cslib.Automata
