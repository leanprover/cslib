/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.Transducers.Transducer

@[expose] public section

namespace Cslib.Automata.DA

/-- A deterministic transducer of finite strings. -/
structure FinTransducer (State InSymbol OutSymbol : Type*)
    extends DA State (InSymbol × OutSymbol) where
  /-- The set of accepting states. -/
  accept : Set State

/-- A `DA.FinTransducer` translates a finite string `xs` into a finite string `ys` if its multistep
transition function maps the start state and the list of pairs  string to an accept state.

This is the standard string translation performed by deterministic transducers without epsilon
symbols. -/
@[simp, scoped grind =]
instance : Transducer (DA.FinTransducer State InSymbol OutSymbol) InSymbol OutSymbol where
  Translates (a : DA.FinTransducer State InSymbol OutSymbol) (xs : List InSymbol) (ys : List OutSymbol) :=
    ∃ μs, a.mtr a.start μs ∈ a.accept ∧ xs = (μs.map Prod.fst) ∧ ys = (μs.map Prod.snd)

end Cslib.Automata.DA
