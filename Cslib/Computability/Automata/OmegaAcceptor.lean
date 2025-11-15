/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Computability.Languages.OmegaLanguage

namespace Cslib.Automata

/-- An `ωAcceptor` is a machine that recognises infinite sequences of symbols. -/
class ωAcceptor (A : Type _) (Symbol : outParam (Type _)) where
  /-- Predicate that establishes whether a string `xs` is accepted. -/
  Accepts (a : A) (xs : ωSequence Symbol) : Prop

namespace ωAcceptor

variable {Symbol : Type _}

/-- The language of an `ωAcceptor` is the set of sequences it `Accepts`. -/
@[scoped grind .]
def language [ωAcceptor A Symbol] (a : A) : ωLanguage Symbol :=
  { xs | Accepts a xs }

/-- A string is in the language of an acceptor iff the acceptor accepts it. -/
@[scoped grind =]
theorem mem_language [ωAcceptor A Symbol] (a : A) (xs : ωSequence Symbol) :
  xs ∈ language a ↔ Accepts a xs := Iff.rfl

end ωAcceptor

end Cslib.Automata
