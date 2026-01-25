/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou, Chris Henson.
-/

module

public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Cslib.Computability.Automata.Acceptors.OmegaAcceptor
public import Cslib.Foundations.Data.OmegaSequence.InfOcc
public import Cslib.Foundations.Semantics.LTS.Basic

@[expose] public section

/-! # Nondeterministic Automaton

A Nondeterministic Automaton (NA) is a transition relation equipped with a set of initial states.

Automata with different accepting conditions are then defined as extensions of `NA`.
These include, for example, a generalised version of NFA as found in the literature (without
finiteness assumptions), nondeterministic Buchi automata, and nondeterministic Muller automata.

This definition extends `LTS` and thus stores the transition system as a relation `Tr` of the form
`State → Symbol → State → Prop`. Note that you can also instantiate `Tr` by passing an argument of
type `State → Symbol → Set State`; it gets automatically expanded to the former shape.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

open Filter

namespace Cslib.Automata

/-- A nondeterministic automaton extends a `LTS` with a set of initial states. -/
structure NA (State Symbol : Type*) extends LTS State Symbol where
  /-- The set of initial states of the automaton. -/
  start : Set State

namespace NA

variable {State Symbol : Type*}

/-- Infinite run. -/
structure Run (na : NA State Symbol) (xs : ωSequence Symbol) (ss : ωSequence State) where
  start : ss 0 ∈ na.start
  trans : na.ωTr ss xs

/-- A nondeterministic automaton that accepts finite strings (lists of symbols). -/
structure FinAcc (State Symbol : Type*) extends NA State Symbol where
  /-- The set of accepting states. -/
  accept : Set State

namespace FinAcc

/-- An `NA.FinAcc` accepts a string if there is a multistep transition from a start state to an
accept state.

This is the standard string recognition performed by NFAs in the literature. -/
@[simp, scoped grind =]
instance : Acceptor (FinAcc State Symbol) Symbol where
  Accepts (a : FinAcc State Symbol) (xs : List Symbol) :=
    ∃ s ∈ a.start, ∃ s' ∈ a.accept, a.MTr s xs s'

/-- The language of an NFA is empty iff there are no final states
reachable from the initial state [Hopcroft2006]. -/
theorem is_empty (a : FinAcc State Symbol) :
    -- a.IsEmpty ↔ Acceptor.language.IsEmpty a := by
    Acceptor.language.IsEmpty a ↔
    ¬∃ s1 s2, a.CanReach s1 s2 ∧ s1 ∈ a.start ∧ s2 ∈ a.accept
    := by
  apply Iff.intro <;> intro h1
  -- If language empty, then no reachable accepting states.
  case mp =>
    rw [Acceptor.language.IsEmpty, not_exists] at h1
    -- Assume that there is a reachable accepting state.
    apply by_contradiction
    intro h2
    rw [not_not] at h2
    -- Then concrete start and accepting states s1 and s2, resp.
    cases h2 with
    | intro s1 h2
    cases h2 with
    | intro s2 h2
    rw [LTS.CanReach] at h2
    cases h2 with
    | intro h2 _
    -- And concrete trace xs from s1 to s2.
    cases h2 with
    | intro xs h2
    -- Then xs must be in the language.
    have h3 : Acceptor.Accepts a xs := by
      simp only [instAcceptor]
      grind
    rw [← Acceptor.mem_language] at h3
    -- But also not in the language.
    have h4 : xs ∉ Acceptor.language a := by exact h1 xs
    -- Which is contradictory.
    exact h4 h3
  -- If no reachable accepting states, then language empty.
  case mpr =>
    -- rw [IsEmpty] at h1
    simp only [not_exists, not_and] at h1
    -- Assume that the language is not empty.
    apply by_contradiction
    intro h2
    rw [Acceptor.language.IsEmpty, not_not] at h2
    -- Then concrete accepted trace xs.
    cases h2 with
    | intro xs h2
    -- Then concrete start and accepting states s1 and s2, resp.,
    -- and s2 reachable from s1.
    have h3 : ∃ s1 s2, s1 ∈ a.start ∧ s2 ∈ a.accept ∧ a.MTr s1 xs s2 := by
      simp at h2
      grind
    cases h3 with
    | intro s1 h3
    cases h3 with
    | intro s2 h3
    have h4 : a.CanReach s1 s2 := by
      rw [LTS.CanReach]
      grind
    -- Premise implies that s2 should not be an accepting state.
    have h5 := h1 s1 s2 h4 h3.left
    -- Which is contradictory.
    exact h5 h3.right.left

end FinAcc

/-- Nondeterministic Buchi automaton. -/
structure Buchi (State Symbol : Type*) extends NA State Symbol where
  /-- The set of accepting states. -/
  accept : Set State

namespace Buchi

/-- An infinite run is accepting iff accepting states occur infinitely many times. -/
@[simp, scoped grind =]
instance : ωAcceptor (Buchi State Symbol) Symbol where
  Accepts (a : Buchi State Symbol) (xs : ωSequence Symbol) :=
    ∃ ss, a.Run xs ss ∧ ∃ᶠ k in atTop, ss k ∈ a.accept

end Buchi

/-- Nondeterministic Muller automaton. -/
structure Muller (State Symbol : Type*) extends NA State Symbol where
  /-- The set of sets of accepting states. -/
  accept : Set (Set State)

namespace Muller

/-- An infinite run is accepting iff the set of states that occur infinitely many times
is one of the sets in `accept`. -/
@[simp, scoped grind =]
instance : ωAcceptor (Muller State Symbol) Symbol where
  Accepts (a : Muller State Symbol) (xs : ωSequence Symbol) :=
    ∃ ss, a.Run xs ss ∧ ss.infOcc ∈ a.accept

end Muller

end NA

end Cslib.Automata
