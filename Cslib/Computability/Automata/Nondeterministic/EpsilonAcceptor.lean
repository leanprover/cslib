/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.Nondeterministic.NA
import Cslib.Computability.Automata.Acceptor

namespace Cslib.Automata.NA

variable {Symbol : Type _} {State : Type _}

@[local grind =]
private instance : HasTau (Option α) := ⟨.none⟩

/-- The `ε`-closure of a set of states `S` is the set of states reachable by any state in `S`
by performing only `ε`-transitions. We use `LTS.τClosure` since `ε` (`Option.none`) is an instance
of `HasTau.τ`. -/
abbrev εClosure (na : NA State (Option Symbol)) (S : Set State) := na.τClosure S

/--
Returns an acceptor that accepts a string if there is a saturated multistep accepting derivative
with that trace from the start state.

This is the standard string recognition performed by εNFAs in the literature.
Formally, this is obtained by considering an `NA` with an `Option` symbol type.
The special symbol `ε` is represented by the `Option.none` case.

Internally, `ε` (`Option.none`) is treated as the `τ` label of the transition system of the `NA`,
allowing for reusing the definitions and results on saturated transitions of `LTS` to deal with
ε-closure.
-/
def εAcceptor (na : NA State (Option Symbol)) (acc : Set State) : Acceptor Symbol where
  Accepts (xs : List Symbol) :=
    ∃ s ∈ na.εClosure na.start, ∃ s' ∈ acc, na.saturate.MTr s (xs.map (some ·)) s'

end Cslib.Automata.NA
