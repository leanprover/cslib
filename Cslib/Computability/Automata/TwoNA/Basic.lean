/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Sign.Basic

/-! # Nondeterministic Two-Way Automaton

A Nondeterministic Two-Way Automaton (TwoNA) reads a finite input word on a tape and may move its
input head in either direction. A transition reads the symbol under the head and, besides changing
the state, moves the head one cell to the left, keeps it in place, or moves it one cell to the
right.

Once it leaves the word to the right, the automaton cannot move back to the word. A run is accepting
if it ends in an accepting state with the head just past the end of the input.

## Main definitions

* `TwoNA`, the automaton itself: The transition relation and the sets of initial and accepting
  states.
* `TwoNACfg`, a configuration of a `TwoNA` running on a fixed input: a state together with a head
  position.
* `TwoNA.Step`, The single-step relation between configurations.
* `TwoNA.Run`, a run of a `TwoNA` on a fixed input: a nonempty chain of configurations linked by
  steps that starts in an initial configuration.

## Implementation notes

The definition of `TwoNA` is kept close to [Vardi][Vardi1989]'s, because the main point is to
prove equivalence to `NA.FinAcc`. This means we do not allow the head to move off the input to the
left, but also do not provide an end marker. Once the head moves off to the right, it cannot move
back into the word.

Runs are `List.IsChain` chains of configurations, anchored at an initial configuration.

## References

* [Moshe Y. Vardi, *A Note on the Reduction of Two-Way Automata to One-Way Automata*][Vardi1989]

-/

@[expose] public section

namespace Cslib.Automata

variable {State Symbol : Type*}

/-- A nondeterministic two-way automaton: a transition relation that reads an input symbol and
moves the input head, together with a set of initial and a set of accepting states. -/
structure TwoNA (State Symbol : Type*) where
  /-- The transition relation. `Tr q x m q'` means that, while reading the symbol `x`, the
  automaton can move from state `q` to state `q'` and move its head according to `m`. -/
  Tr (q : State) (x : Symbol) (m : SignType) (q' : State) : Prop
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

namespace TwoNA

variable {a : TwoNA State Symbol} {input : List Symbol} {c c' : TwoNACfg State Symbol input}

/-- A single step of `a` on `input`. It is possible only while the head is on an actual input
symbol, and it is performed by a transition of `a` that reads the symbol under the head: such a
transition determines the new state and a head movement `m`, by which the head position changes.
A leftward move at position `0` would take the head off the input, so no such step exists. -/
def Step (a : TwoNA State Symbol) (input : List Symbol)
    (c c' : TwoNACfg State Symbol input) : Prop :=
  ∃ m, ∃ _ : (c.pos : ℕ) < input.length,
    a.Tr c.state input[c.pos] m c'.state ∧ (c'.pos : ℤ) = (c.pos : ℤ) + (m.cast : ℤ)

/-- A run of `a` on `input`: a nonempty chain of configurations, each obtained from the previous
one by a step, that starts in an initial state with the head on the first symbol of the input. -/
structure Run (a : TwoNA State Symbol) (input : List Symbol) where
  /-- The chain of configurations. -/
  chain : List (TwoNACfg State Symbol input)
  /-- Consecutive configurations are linked by a step. -/
  isChain : chain.IsChain (a.Step input)
  /-- There is at least one configuration. -/
  ne : chain ≠ []
  /-- The head starts on the first symbol of the input. -/
  head_pos : (chain.head ne).pos = 0
  /-- The run starts in an initial state. -/
  head_mem_start : (chain.head ne).state ∈ a.start

/-- The configuration a run starts in. -/
def Run.head (r : a.Run input) : TwoNACfg State Symbol input := r.chain.head r.ne

/-- The configuration a run ends in. -/
def Run.last (r : a.Run input) : TwoNACfg State Symbol input := (r.chain).getLast r.ne

/-- A run is accepting if it ends in an accepting state with the head just past the end of the
input. -/
def Run.IsAccepting (r : a.Run input) : Prop := r.last.state ∈ a.accept ∧ r.last.pos = Fin.last _

/-- Extend a run by one more step. -/
def Run.snoc (r : a.Run input) (c : TwoNACfg State Symbol input) (h : a.Step input r.last c) :
    a.Run input where
  chain := r.chain ++ [c]
  isChain := r.isChain.append (List.isChain_singleton c)
    (by simp_all [Run.last, List.getLast?_eq_some_getLast r.ne])
  ne := by simp
  head_pos := by simpa [List.head_append_of_ne_nil r.ne] using r.head_pos
  head_mem_start := by simpa [List.head_append_of_ne_nil r.ne] using r.head_mem_start

@[simp]
theorem Run.last_snoc (r : a.Run input) (c : TwoNACfg State Symbol input)
    (h : a.Step input r.last c) : (r.snoc c h).last = c := by
  simp [Run.snoc, Run.last]

end TwoNA

/-- A `TwoNA` accepts an input if it has an accepting run on it. -/
@[simp, scoped grind =]
instance : Acceptor (TwoNA State Symbol) Symbol where
  Accepts (a : TwoNA State Symbol) (xs : List Symbol) := ∃ r : a.Run xs, r.IsAccepting

end Cslib.Automata
