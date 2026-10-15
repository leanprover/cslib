/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

import Cslib.Computability.Automata.EpsilonNA.OfRegularExpression

/-! # Thompson's construction

The automaton of `(ab)*` over `Bool`, with `true` for `a` and `false` for `b`.
-/

namespace CslibTests.Thompson

open Cslib.Automata Cslib.Automata.Acceptor RegularExpression

/-- The regular expression `(ab)*`. -/
abbrev abStar : RegularExpression Bool := (char true * char false).star

-- A hub, and two states for each letter.
example : Fintype.card abStar.State = 5 := by decide

example : [] ∈ language abStar.toεNA := by
  rw [language_toεNA]
  decide

example : [true, false, true, false] ∈ language abStar.toεNA := by
  rw [language_toεNA]
  decide

example : [true] ∉ language abStar.toεNA := by
  rw [language_toεNA]
  decide

example : [false, true] ∉ language abStar.toεNA := by
  rw [language_toεNA]
  decide

end CslibTests.Thompson
