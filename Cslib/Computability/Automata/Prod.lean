/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Cslib.Computability.Automata.DA

/-! # Product of automata. -/

namespace Cslib.Automata

open List
open scoped FLTS

variable {State1 State2 Symbol : Type*}

namespace DA

/-
TODO: This operation could be generalised to FLTS and lifted here.
-/
@[scoped grind =]
def prod (da1 : DA State1 Symbol) (da2 : DA State2 Symbol) : DA (State1 × State2) Symbol where
  start := (da1.start, da2.start)
  tr := fun (s1, s2) x ↦ (da1.tr s1 x, da2.tr s2 x)

@[simp, scoped grind =]
theorem prod_mtr_eq (da1 : DA State1 Symbol) (da2 : DA State2 Symbol)
    (s : State1 × State2) (xs : List Symbol) :
    (da1.prod da2).mtr s xs = (da1.mtr s.fst xs, da2.mtr s.snd xs) := by
  induction xs generalizing s <;> grind

end DA

end Cslib.Automata
