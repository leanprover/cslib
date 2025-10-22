/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.LTS.Basic

/-! # Nondeterministic Automaton

A Nondeterministic Automaton (NA) is an automaton with a set of initial states.

This definition extends `LTS` and thus stores the transition system as a relation `Tr` of the form
`State → Symbol → State → Prop`. Note that you can also instantiate `Tr` by passing an argument of
type `State → Symbol → Set State`; it gets automatically expanded to the former shape.
-/

namespace Cslib

structure NA (State : Type _) (Symbol : Type _) extends LTS State Symbol where
  /-- The set of initial states of the automaton. -/
  start : Set State

end Cslib
