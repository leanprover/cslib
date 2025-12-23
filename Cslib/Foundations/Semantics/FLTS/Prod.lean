/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.FLTS.Basic

/-! # Product of functional labelled transition systems -/

namespace Cslib.FLTS

variable {State Label : Type*}

/-- The product of two FLTS with the same label type. -/
@[scoped grind =]
def prod (flts1 : FLTS State1 Label) (flts2 : FLTS State2 Label) :
    FLTS (State1 × State2) Label where
  tr := fun (s1, s2) μ ↦ (flts1.tr s1 μ, flts2.tr s2 μ)

/-- A state is reachable by the product FLTS iff its components are reachable by
the respective FLTS components. -/
@[simp, scoped grind =]
theorem prod_mtr_eq (flts1 : FLTS State1 Label) (flts2 : FLTS State2 Label)
    (s : State1 × State2) (μs : List Label) :
    (flts1.prod flts2).mtr s μs = (flts1.mtr s.fst μs, flts2.mtr s.snd μs) := by
  induction μs generalizing s <;> grind

end Cslib.FLTS
