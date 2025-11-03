/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Computability.Automata.Accept
import Cslib.Foundations.Semantics.LTS.Basic

/-! # Nondeterministic Automaton

A Nondeterministic Automaton (NA) is an automaton with a set of initial states.

This definition extends `LTS` and thus stores the transition system as a relation `Tr` of the form
`State → Symbol → State → Prop`. Note that you can also instantiate `Tr` by passing an argument of
type `State → Symbol → Set State`; it gets automatically expanded to the former shape.
-/

namespace Cslib

structure NA (State Symbol : Type*) extends LTS State Symbol where
  /-- The set of initial states of the automaton. -/
  start : Set State

variable {State Symbol : Type*}

namespace NA

@[scoped grind =]
def accept (na : NA State Symbol) (acc : Set State) : Accept State Symbol where
  Run xl s := ∃ s0 ∈ na.start, na.MTr s0 xl s
  acc := acc

@[scoped grind =]
def language (na : NA State Symbol) (acc : Set State) : Language Symbol :=
  (na.accept acc).language

@[scoped grind =]
theorem mem_language (na : NA State Symbol) (acc : Set State) (xl : List Symbol) :
    xl ∈ na.language acc ↔ ∃ s ∈ acc, ∃ s0 ∈ na.start, na.MTr s0 xl s :=
  Iff.rfl

@[scoped grind =]
def buchiAccept (na : NA State Symbol) (acc : Set State) : BuchiAccept State Symbol where
  Run xs ss := ss 0 ∈ na.start ∧ ∀ n, na.Tr (ss n) (xs n) (ss (n + 1))
  acc := acc

@[scoped grind =]
def buchiLanguage (na : NA State Symbol) (acc : Set State) : ωLanguage Symbol :=
  (na.buchiAccept acc).language

end NA

end Cslib
