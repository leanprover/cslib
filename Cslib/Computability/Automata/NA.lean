/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Computability.Languages.OmegaLanguage
import Cslib.Foundations.Semantics.LTS.Basic

/-! # Nondeterministic Automaton

A Nondeterministic Automaton (NA) is an automaton with a set of initial states.

This definition extends `LTS` and thus stores the transition system as a relation `Tr` of the form
`State → Symbol → State → Prop`. Note that you can also instantiate `Tr` by passing an argument of
type `State → Symbol → Set State`; it gets automatically expanded to the former shape.
-/

open Filter

namespace Cslib

structure NA (State Symbol : Type*) extends LTS State Symbol where
  /-- The set of initial states of the automaton. -/
  start : Set State

structure NA.FinAcc (State Symbol : Type*) extends NA State Symbol where
  acc : Set State

structure NA.Buchi (State Symbol : Type*) extends NA State Symbol where
  acc : Set State

structure NA.Muller (State Symbol : Type*) extends NA State Symbol where
  accSet : Set (Set State)

variable {State Symbol : Type*}

namespace NA

/-- Infinite run. -/
@[scoped grind =]
def Run (na : NA State Symbol) (xs : ωSequence Symbol) (ss : ωSequence State) :=
  ss 0 ∈ na.start ∧ ∀ n, na.Tr (ss n) (xs n) (ss (n + 1))

namespace FinAcc

@[scoped grind =]
def Accept (nfa : FinAcc State Symbol) (xl : List Symbol) :=
  ∃ s ∈ nfa.acc, ∃ s0 ∈ nfa.start, nfa.MTr s0 xl s

@[scoped grind =]
def language (nfa : FinAcc State Symbol) : Language Symbol :=
  { xl : List Symbol | nfa.Accept xl }

@[scoped grind =]
theorem mem_language (nfa : FinAcc State Symbol) (xl : List Symbol) :
    xl ∈ nfa.language ↔ ∃ s ∈ nfa.acc, ∃ s0 ∈ nfa.start, nfa.MTr s0 xl s :=
  Iff.rfl

end FinAcc

namespace Buchi

@[scoped grind =]
def Accept (nba : Buchi State Symbol) (ss : ωSequence State) :=
  ∃ᶠ k in atTop, ss k ∈ nba.acc

@[scoped grind =]
def language (nba : Buchi State Symbol) : ωLanguage Symbol :=
  { xs : ωSequence Symbol | ∃ ss, nba.Run xs ss ∧ nba.Accept ss }

@[scoped grind =]
theorem mem_language (nba : Buchi State Symbol) (xs : ωSequence Symbol) :
    xs ∈ nba.language ↔ ∃ ss, nba.Run xs ss ∧ nba.Accept ss :=
  Iff.rfl

end Buchi

namespace Muller

@[scoped grind =]
def Accept (nma : Muller State Symbol) (ss : ωSequence State) :=
  ss.infOcc ∈ nma.accSet

@[scoped grind =]
def language (nma : Muller State Symbol) : ωLanguage Symbol :=
  { xs : ωSequence Symbol | ∃ ss, nma.Run xs ss ∧ nma.Accept ss }

@[scoped grind =]
theorem mem_language (nma : Muller State Symbol) (xs : ωSequence Symbol) :
    xs ∈ nma.language ↔ ∃ ss, nma.Run xs ss ∧ nma.Accept ss :=
  Iff.rfl

end Muller

end NA

end Cslib
