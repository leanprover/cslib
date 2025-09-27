/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.Lts.Basic

/-!
# Rooted Labelled Transition System (Rooted LTS)

A Rooted Labelled Transition System (`RootedLts`) is an `Lts` with an initial state (the 'root').
-/

structure RootedLts (State : Type _) (Label : Type _) extends Lts State Label where
  /-- The root of the labelled transition system. -/
  root : State
