/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Languages.OmegaLanguage

/-! # Acceptance conditions
-/

namespace Cslib

open Set Filter ωSequence

/-- Acceptance condition for finite words. -/
structure Accept (State : Type*) (Symbol : Type*) where
  Run : List Symbol → State → Prop
  acc : Set State

namespace Accept

variable {State : Type*} {Symbol : Type*}

@[scoped grind =]
def language (accept : Accept State Symbol) : Language Symbol :=
  { xl : List Symbol | ∃ s ∈ accept.acc, accept.Run xl s }

@[scoped grind =]
theorem mem_language (accept : Accept State Symbol) (xl : List Symbol) :
    xl ∈ accept.language ↔ ∃ s ∈ accept.acc, accept.Run xl s :=
  Iff.rfl

end Accept

/-- Buchi acceptance condition for infinite words. -/
structure BuchiAccept (State : Type*) (Symbol : Type*) where
  Run : ωSequence Symbol → ωSequence State → Prop
  acc : Set State

namespace BuchiAccept

variable {State : Type*} {Symbol : Type*}

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
structure MullerAccept (State : Type*) (Symbol : Type*) where
  Run : ωSequence Symbol → ωSequence State → Prop
  accSet : Set (Set State)

namespace MullerAccept

variable {State : Type*} {Symbol : Type*}

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
