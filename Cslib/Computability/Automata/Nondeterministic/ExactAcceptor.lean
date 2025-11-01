/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Automata.Nondeterministic.NA
import Cslib.Computability.Automata.Acceptor

namespace Cslib.Automata.NA

variable {Symbol : Type _} {State : Type _}

/-- Returns the acceptor that matches exactly the sequence of symbols in a string.
That is, a string is accepted if there is a multi-step accepting derivative with that trace from
the start state.

This is the standard string recognition performed by NFAs in the literature. -/
def exactAcceptor (na : NA State Symbol) (acc : Set State) : Acceptor Symbol where
  Accepts (xs : List Symbol) := ∃ s ∈ na.start, ∃ s' ∈ acc, na.MTr s xs s'

end Cslib.Automata.NA
