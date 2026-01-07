/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Computability.Automata.Acceptors.Acceptor
import Cslib.Computability.Automata.Acceptors.OmegaAcceptor
import Cslib.Foundations.Data.OmegaSequence.InfOcc
import Cslib.Foundations.Semantics.FLTS.Basic

/-! # Deterministic Automata

A Deterministic Automaton (`DA`) is an automaton defined by a transition function equipped with an
initial state.

Automata with different accepting conditions are then defined as extensions of `DA`.
These include, for example, a generalised version of DFA as found in the literature (without
finiteness assumptions), deterministic Buchi automata, and deterministic Muller automata.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

open List Filter Cslib.ωSequence
open scoped Cslib.FLTS

namespace Cslib.Automata

/-- A deterministic automaton extends a `FLTS` with a unique initial state. -/
structure DA (State Symbol : Type*) extends FLTS State Symbol where
  /-- The initial state of the automaton. -/
  start : State

namespace DA

variable {State Symbol : Type*}

/-- Helper function for defining `run` below. -/
@[scoped grind =]
def run' (da : DA State Symbol) (xs : ωSequence Symbol) : ℕ → State
  | 0 => da.start
  | n + 1 => da.tr (run' da xs n) (xs n)

/-- Infinite run. -/
@[scoped grind =]
def run (da : DA State Symbol) (xs : ωSequence Symbol) : ωSequence State := da.run' xs

@[simp, scoped grind =]
theorem run_zero {da : DA State Symbol} {xs : ωSequence Symbol} :
    da.run xs 0 = da.start :=
  rfl

@[simp, scoped grind =]
theorem run_succ {da : DA State Symbol} {xs : ωSequence Symbol} {n : ℕ} :
    da.run xs (n + 1) = da.tr (da.run xs n) (xs n) := by
  rfl

@[simp, scoped grind =]
theorem mtr_extract_eq_run {da : DA State Symbol} {xs : ωSequence Symbol} {n : ℕ} :
    da.mtr da.start (xs.extract 0 n) = da.run xs n := by
  induction n
  case zero => rfl
  case succ n h_ind => grind

/-- A deterministic automaton that accepts finite strings (lists of symbols). -/
structure FinAcc (State Symbol : Type*) extends DA State Symbol where
  /-- The set of accepting states. -/
  accept : Set State

namespace FinAcc

/-- A `DA.FinAcc` accepts a string if its multistep transition function maps the start state and
the string to an accept state.

This is the standard string recognition performed by DFAs in the literature. -/
@[simp, scoped grind =]
instance : Acceptor (DA.FinAcc State Symbol) Symbol where
  Accepts (a : DA.FinAcc State Symbol) (xs : List Symbol) :=
    a.mtr a.start xs ∈ a.accept

end FinAcc

/-- Deterministic Buchi automaton. -/
structure Buchi (State Symbol : Type*) extends DA State Symbol where
  /-- The set of accepting states. -/
  accept : Set State

namespace Buchi

/-- An infinite run is accepting iff accepting states occur infinitely many times. -/
@[simp, scoped grind =]
instance : ωAcceptor (Buchi State Symbol) Symbol where
  Accepts (a : Buchi State Symbol) (xs : ωSequence Symbol) :=
    ∃ᶠ k in atTop, a.run xs k ∈ a.accept

end Buchi

/-- Deterministic Muller automaton. -/
structure Muller (State Symbol : Type*) extends DA State Symbol where
  /-- The set of sets of accepting states. -/
  accept : Set (Set State)

namespace Muller

/-- An infinite run is accepting iff the set of states that occur infinitely many times
is one of the sets in `accept`. -/
@[simp, scoped grind =]
instance : ωAcceptor (Muller State Symbol) Symbol where
  Accepts (a : Muller State Symbol) (xs : ωSequence Symbol) :=
    (a.run xs).infOcc ∈ a.accept

end Muller

end DA

end Cslib.Automata
