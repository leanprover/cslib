/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.DA
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter

/-! # Deterministic Muller Automata
-/

/-- `xs.infOcc` is the set of elements that occurs infinitely many times in `xs`.
TODO: This definition should be be moved to a different file.
-/
def ωList.infOcc {X : Type*} (xs : ωList X) : Set X :=
  { x | ∃ᶠ k in atTop, xs k = x }

/-- A deterministic Muller automaton consists of a labelled transition function
`tr` over finite sets of states and labels (called symbols), a starting state `start`,
and a finite set of finite accepting sets `accept`. -/
structure MullerDA (State : Type _) (Symbol : Type _) extends DA State Symbol where
  /-- The set of accepting sets of the automaton. -/
  accept : Set (Set State)
  /-- The automaton is finite-state. -/
  finite_state : Finite State
  /-- The type of symbols (also called 'alphabet') is finite. -/
  finite_symbol : Finite Symbol

namespace MullerDA

variable {State : Type _} {Symbol : Type _}

/-- A deterministic Muller automaton `mda` accepts an ω-word `xs` iff the set of states that
occurs infinite often when running `mda` on `xs` is one of the accepting sets.
-/
@[scoped grind →]
def Accepts (mda : MullerDA State Symbol) (xs : ωList Symbol) :=
  (mda.infRun xs).infOcc ∈ mda.accept

/-- The ω-language of a deterministic Muller automaton is the set of ω-words that it accepts. -/
@[scoped grind =]
def language (mda : MullerDA State Symbol) : Set (ωList Symbol) :=
  { xs | mda.Accepts xs }

/-- An ω-word is accepted by a deterministic Muller automaton iff it is in its ω-language. -/
@[scoped grind _=_]
theorem accepts_mem_language (mda : MullerDA State Symbol) (xs : ωList Symbol) :
  mda.Accepts xs ↔ xs ∈ mda.language := by rfl

end MullerDA
