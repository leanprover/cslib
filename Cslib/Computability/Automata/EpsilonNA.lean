/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Computability.Automata.NA
import Cslib.Computability.Languages.Language

/-! # Nondeterministic automata with ε-transitions. -/

namespace Cslib

/-- A nondeterministic finite automaton with ε-transitions (`εNA`) is an `NA` with an `Option`
symbol type. The special symbol ε is represented by the `Option.none` case.

Internally, ε (`Option.none`) is treated as the `τ` label of the underlying transition system,
allowing for reusing the definitions and results on saturated transitions of `LTS` to deal with
ε-closure. -/
def εNA (State : Type*) (Symbol : Type*) := NA State (Option Symbol)

-- structure εNA (State : Type*) (Symbol : Type*) extends NA State (Option Symbol) where
--   /-- The set of accepting states of the automaton. -/
--   accept : Set State
--   /-- The automaton is finite-state. -/
--   finite_state : Finite State
--   /-- The type of symbols (also called 'alphabet') is finite. -/
--   finite_symbol : Finite Symbol

variable {State : Type*} {Symbol : Type*}

@[local grind =]
private instance : HasTau (Option α) := ⟨.none⟩

/-- The `ε`-closure of a set of states `S` is the set of states reachable by any state in `S`
by performing only `ε`-transitions. We use `LTS.τClosure` since `ε` (`Option.none`) is an instance
of `HasTau.τ`. -/
abbrev εNA.εClosure (ena : εNA State Symbol) (S : Set State) := ena.τClosure S

namespace εNA

/-- An εNA accepts a string if there is a saturated multistep accepting derivative with that trace
from the start state. -/
@[scoped grind]
def accept (ena : εNA State Symbol) (acc : Set State) : Accept State Symbol where
  Run xl s := ∃ s0 ∈ ena.εClosure ena.start, ena.saturate.MTr s0 (xl.map (some ·)) s
  acc := acc

-- def Accepts (ena : εNA State Symbol) (xs : List Symbol) :=
--   ∃ s ∈ ena.εClosure ena.start, ∃ s' ∈ ena.accept,
--   ena.saturate.MTr s (xs.map (some ·)) s'

/-- The language of an εDA is the set of strings that it accepts. -/
@[scoped grind =]
def language (ena : εNA State Symbol) (acc : Set State) : Language Symbol :=
  (ena.accept acc).language

--   { xs | ena.Accepts xs }

/-- A string is in the language of an εNA iff it is accepted by the εNA. -/
@[scoped grind =]
theorem mem_language (ena : εNA State Symbol) (acc : Set State) (xl : List Symbol) :
    xl ∈ ena.language acc ↔
    ∃ s ∈ acc, ∃ s0 ∈ ena.εClosure ena.start, ena.saturate.MTr s0 (xl.map (some ·)) s :=
  Iff.rfl

end εNA

end Cslib
