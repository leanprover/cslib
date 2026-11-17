/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

import Cslib.Computability.Automata.MPDA.Holes
import Cslib.Computability.Automata.MPDA.StackAgnostic
import Mathlib.Tactic.IntervalCases

namespace CslibTests

open Cslib.Automata.MPDA

/-- Nested pushes and pops on two stacks: `↓₀ ↓₁ ↑₁ ↑₀`. -/
private def nested : List (Unit × Op 2 Unit) :=
  [((), .push 0 ()), ((), .push 1 ()), ((), .pop 1 ()), ((), .pop 0 ())]

/-- Crossing pushes and pops on two stacks: `↓₀ ↓₁ ↑₀ ↑₁`. -/
private def crossing : List (Unit × Op 2 Unit) :=
  [((), .push 0 ()), ((), .push 1 ()), ((), .pop 0 ()), ((), .pop 1 ())]

example : WellNested nested := by decide

example : ¬WellNested crossing := by decide

/-- A push matched by a pop of the wrong symbol does not give a well-nested sequence. -/
example : ¬WellNested ([((), .push 0 true), ((), .pop 0 false)] : List (Unit × Op 1 Bool)) := by
  decide

example : HoleBounded 0 nested := (by decide : WellNested nested).holeBounded_zero

/-- Neither push of `crossing` is closed by a well-nested continuation. -/
theorem crossing_holePush_zero : HolePush crossing 0 := by
  refine ⟨⟨0, (), (), rfl⟩, ?_⟩
  rintro ⟨m, hm, hws⟩
  have h₁ := hm.1
  have h₂ := hm.lt_length
  simp only [crossing, List.length_cons, List.length_nil] at h₂
  interval_cases m <;> revert hws <;> decide

theorem crossing_holePush_one : HolePush crossing 1 := by
  refine ⟨⟨1, (), (), rfl⟩, ?_⟩
  rintro ⟨m, hm, hws⟩
  have h₁ := hm.1
  have h₂ := hm.lt_length
  simp only [crossing, List.length_cons, List.length_nil] at h₂
  interval_cases m <;> revert hws <;> decide

/-- After its second push, `crossing` has two open holes: one for each stack. -/
theorem crossing_openHoles : openHoles crossing 1 = 2 := by
  have hset : {q | OpenHolePush crossing 1 q ∧ ¬∃ p, SameHole crossing 1 p q} = {0, 1} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨_, hq, _⟩, _⟩
      omega
    · rintro (rfl | rfl)
      · refine ⟨⟨crossing_holePush_zero, le_refl _ |>.trans (by omega), by decide, 0,
          ⟨(), (), rfl⟩, ?_⟩, ?_⟩
        · intro k
          rcases k with _ | k <;> simp [crossing, factor, net, Op.net]
        · rintro ⟨p, hp, -⟩
          omega
      · refine ⟨⟨crossing_holePush_one, le_refl _, by decide, 1, ⟨(), (), rfl⟩, ?_⟩, ?_⟩
        · intro k
          simp [crossing, factor, net]
        · rintro ⟨p, hp, -, -, ⟨i, ⟨a, γ, h₀⟩, ⟨a', γ', h₁⟩⟩, -⟩
          have : p = 0 := by omega
          subst this
          simp only [crossing, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
            Prod.mk.injEq, Op.push.injEq] at h₀ h₁
          exact absurd (h₀.2.1.trans h₁.2.1.symm) (by decide)
  rw [openHoles, hset, Set.ncard_pair (by decide)]

example : ¬HoleBounded 1 crossing := fun h => by
  have := h 1 (by decide)
  rw [crossing_openHoles] at this
  omega

end CslibTests
