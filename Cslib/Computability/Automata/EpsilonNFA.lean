/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.NA

/-! # Nondeterministic automata with ε-transitions. -/

/-- A nondeterministic finite automaton with ε-transitions (`εNFA`) is an `NA` with an `Option`
symbol type. The special symbol ε is represented by the `Option.none` case.

Internally, ε (`Option.none`) is treated as the `τ` label of the underlying transition system,
allowing for reusing the definitions and results on saturated transitions of `LTS` to deal with
ε-closure. -/
structure εNFA (State : Type _) (Symbol : Type _) extends NA State (Option Symbol) where
  /-- The set of accepting states of the automaton. -/
  accept : Set State
  /-- The automaton is finite-state. -/
  finite_state : Finite State
  /-- The type of symbols (also called 'alphabet') is finite. -/
  finite_symbol : Finite Symbol

@[local grind =]
private instance : HasTau (Option α) := ⟨.none⟩

/-- The `ε`-closure of a set of states `S` is the set of states reachable by any state in `S`
by performing only `ε`-transitions. We use `LTS.τClosure` since `ε` (`Option.none`) is an instance
of `HasTau.τ`. -/
abbrev εNFA.εClosure (enfa : εNFA State Symbol) (S : Set State) := enfa.τClosure S

namespace εNFA

/-- An εNFA accepts a string if there is a saturated multistep accepting derivative with that trace
from the start state. -/
@[scoped grind]
def Accepts (enfa : εNFA State Symbol) (xs : List Symbol) :=
  ∃ s ∈ enfa.εClosure enfa.start, ∃ s' ∈ enfa.accept,
  enfa.saturate.MTr s (xs.map (some ·)) s'

/-- The language of an εDA is the set of strings that it accepts. -/
@[scoped grind =]
def language (enfa : εNFA State Symbol) : Set (List Symbol) :=
  { xs | enfa.Accepts xs }

/-- A string is accepted by an εNFA iff it is in the language of the NA. -/
@[scoped grind =]
theorem accepts_mem_language (enfa : εNFA State Symbol) (xs : List Symbol) :
  enfa.Accepts xs ↔ xs ∈ enfa.language := by rfl

end εNFA
