/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.LTS.Basic

/-! # Nondeterministic Automaton

A Nondeterministic Automaton (NA) is a labelled transition system with a set of initial states.
-/
structure NA State Symbol extends LTS State Symbol where
  start : Set State
