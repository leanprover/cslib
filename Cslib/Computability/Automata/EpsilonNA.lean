/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

import Cslib.Computability.Automata.NA
import Cslib.Computability.Automata.Acceptor

/-! # Nondeterministic automata with ε-transitions. -/

namespace Cslib.Automata

/-- A nondeterministic finite automaton with ε-transitions (`εNA`) is an `NA` with an `Option`
symbol type. The special symbol ε is represented by the `Option.none` case.

Internally, ε (`Option.none`) is treated as the `τ` label of the underlying transition system,
allowing for reusing the definitions and results on saturated transitions of `LTS` to deal with
ε-closure. -/
structure εNA (State Symbol : Type*) extends NA State (Option Symbol)

variable {State Symbol : Type*}

@[local grind =]
private instance : HasTau (Option α) := ⟨.none⟩

/-- The `ε`-closure of a set of states `S` is the set of states reachable by any state in `S`
by performing only `ε`-transitions. We use `LTS.τClosure` since `ε` (`Option.none`) is an instance
of `HasTau.τ`. -/
abbrev εNA.εClosure (a : εNA State Symbol) (S : Set State) := a.τClosure S

namespace εNA

structure FinAcc (State Symbol : Type*) extends εNA State Symbol where
  accept : Set State

namespace FinAcc

/-- An `εNA.FinAcc` accepts a string if there is a saturated multistep accepting derivative with
that trace from the start state. -/
@[scoped grind =]
instance : Acceptor (FinAcc State Symbol) Symbol where
  Accepts (a : FinAcc State Symbol) (xs : List Symbol) :=
    ∃ s ∈ a.εClosure a.start, ∃ s' ∈ a.accept,
    a.saturate.MTr s (xs.map (some ·)) s'

end FinAcc

end εNA

end Cslib.Automata
