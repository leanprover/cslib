/-
Copyright (c) 2026 Malvin Gattinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malvin Gattinger
-/

import Cslib.Logics.PDL.Semantics
import Cslib.Logics.Modal.LogicalEquivalence

namespace CslibTests

open Cslib Logic Modal PDL Model Proposition Satisfies
open scoped InferenceSystem

example (a : Program Nat Nat) (φ : Formula Nat Nat) :
  d⟨a⟩φ = diamond a φ := rfl

example (a : Program Nat Nat) (φ : Formula Nat Nat) :
  d[a]φ = box a φ := rfl

local instance : Coe ℕ (Program ℕ Atom) := ⟨fun k => action k⟩

example :
  let ψ (p q : Nat) (a : Nat) : Formula Nat Nat := d⟨ (?' p ;' a)*⟩ q
  diamond (star (seq (test (.atom 0)) (action 0))) (.atom 1) = ψ 0 1 0 := rfl

theorem test_check_example (m : PDL.Model State Label Atom)
    (h : m.IsStandard) (s : State) :
    ⇓PDL[ m, s ⊨ d⟨?' ⊥ ∪ ?' ⊤⟩ ⊤ ] := by
  -- TODO make and tag enough `grind` lemmas to solve this automatically?
  refine ⟨fun _ => s, ?_, fun _ => fun h => h⟩
  change m.lts.Tr s (?' ⊥ ∪ ?' ⊤) s
  rw [h.regular.union]
  exact .inr ((h.test _ _ _).2 ⟨rfl, fun h => h⟩)

end CslibTests
