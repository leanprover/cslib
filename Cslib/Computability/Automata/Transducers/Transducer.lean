/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! # Transducers -/

@[expose] public section

namespace Cslib.Automata

/-- A `Transducer` is an automaton that translates strings (lists of symbols in an alphabet) into
strings. -/
class Transducer (A : Type u) (InSymbol OutSymbol : outParam (Type v)) where
  /-- Predicate that establishes whether a string `xs` can be translated into `ys`. -/
  Translates (a : A) (xs : List InSymbol) (ys : List OutSymbol) : Prop

scoped notation xs "[" a "]" ys => Transducer.Translates a xs ys

end Cslib.Automata
