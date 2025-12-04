/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Init
import Mathlib.Computability.Language

namespace Cslib.Automata

/-- An `Acceptor` is a machine that recognises strings (lists of symbols in an alphabet). -/
class Acceptor (A : Type u) (Symbol : outParam (Type v)) where
  /-- Predicate that establishes whether a string `xs` is accepted. -/
  Accepts (a : A) (xs : List Symbol) : Prop

namespace Acceptor

variable {Symbol : Type v}

/-- The language of an `Acceptor` is the set of strings it `Accepts`. -/
@[scoped grind .]
def language [Acceptor A Symbol] (a : A) : Language Symbol :=
  { xs | Accepts a xs }

/-- A string is in the language of an acceptor iff the acceptor accepts it. -/
@[simp, scoped grind =]
theorem mem_language [Acceptor A Symbol] (a : A) (xs : List Symbol) :
  xs ∈ language a ↔ Accepts a xs := Iff.rfl

end Acceptor

end Cslib.Automata
