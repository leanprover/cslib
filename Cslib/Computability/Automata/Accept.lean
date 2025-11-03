/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Languages.OmegaLanguage

/-! # Acceptance conditions

This file defines the various types of acceptance conditions of automata theory.
Each acceptance condition `Accept` consists of a predicate `Accept.Run` defining
the notion of an (finite or infinite) run of an automaton and a data field determining
the acceptance condition (such as a set of accepting states).  Then `Accept.language`
connects these two items together and defines the language (over finite or infinite words)
determined by the acceptance condition `Accept`.
-/

namespace Cslib

open Set Filter ωSequence

/-- Acceptance condition for finite words. -/
structure Accept (State Symbol : Type*) where
  Run : List Symbol → State → Prop
  acc : Set State

namespace Accept

variable {State Symbol : Type*}

@[scoped grind =]
def language (accept : Accept State Symbol) : Language Symbol :=
  { xl : List Symbol | ∃ s ∈ accept.acc, accept.Run xl s }

@[scoped grind =]
theorem mem_language (accept : Accept State Symbol) (xl : List Symbol) :
    xl ∈ accept.language ↔ ∃ s ∈ accept.acc, accept.Run xl s :=
  Iff.rfl

end Accept

/-- Buchi acceptance condition for infinite words. -/
structure BuchiAccept (State Symbol : Type*) where
  Run : ωSequence Symbol → ωSequence State → Prop
  acc : Set State

namespace BuchiAccept

variable {State Symbol : Type*}

@[scoped grind =]
def language (accept : BuchiAccept State Symbol) : ωLanguage Symbol :=
  { xs : ωSequence Symbol |
    ∃ ss : ωSequence State, accept.Run xs ss ∧ (ss.infOcc ∩ accept.acc).Nonempty }

@[scoped grind =]
theorem mem_language (accept : BuchiAccept State Symbol) (xs : ωSequence Symbol) :
    xs ∈ accept.language ↔
    ∃ ss : ωSequence State, accept.Run xs ss ∧ (ss.infOcc ∩ accept.acc).Nonempty :=
  Iff.rfl

end BuchiAccept

/-- Muller acceptance condition for infinite words. -/
structure MullerAccept (State Symbol : Type*) where
  Run : ωSequence Symbol → ωSequence State → Prop
  accSet : Set (Set State)

namespace MullerAccept

variable {State Symbol : Type*}

@[scoped grind =]
def language (accept : MullerAccept State Symbol) : ωLanguage Symbol :=
  { xs : ωSequence Symbol |
    ∃ ss : ωSequence State, accept.Run xs ss ∧ ss.infOcc ∈ accept.accSet }

@[scoped grind =]
theorem mem_language (accept : MullerAccept State Symbol) (xs : ωSequence Symbol) :
    xs ∈ accept.language ↔
    ∃ ss : ωSequence State, accept.Run xs ss ∧ ss.infOcc ∈ accept.accSet :=
  Iff.rfl

end MullerAccept

end Cslib
