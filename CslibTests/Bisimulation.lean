/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.LTS.Bisimulation

namespace CslibTests

open Cslib LTS

/- An LTS with two bisimilar states. -/
private inductive tr1 : ℕ → Char → ℕ → Prop where
-- First process, `1`
| one2two : tr1 1 'a' 2
| two2three : tr1 2 'b' 3
| two2four : tr1 2 'c' 4
-- Second process, `5`
| five2six : tr1 5 'a' 6
| six2seven : tr1 6 'b' 7
| six2eight : tr1 6 'c' 8

def lts1 := LTS.mk tr1

private inductive Bisim15 : ℕ → ℕ → Prop where
| oneFive : Bisim15 1 5
| twoSix : Bisim15 2 6
| threeSeven : Bisim15 3 7
| fourEight : Bisim15 4 8

example : 1 ~[lts1] 5 := by
  exists Bisim15
  apply And.intro; constructor
  intro s1 s2 hr μ
  constructor
  case left =>
    intro s1' htr
    cases htr <;> cases hr
    · exists 6
      repeat constructor
    · exists 7
      repeat constructor
    · exists 8
      repeat constructor
  case right =>
    intro s2' htr
    cases htr <;> cases hr
    · exists 2; repeat constructor
    · exists 3; repeat constructor
    · exists 4; repeat constructor

  -- aesop?
  --   (add simp Bisimulation)
  --   (add safe constructors Bisim15)
  --   (add safe cases Bisim15)
  --   (add safe cases [LTS.mtr])
  --   (add simp LTS.tr)
  --   (add safe constructors tr1)
  --   (add unsafe apply Bisimulation.follow_fst)
  --   (add unsafe apply Bisimulation.follow_snd)

section Heterogeneous

variable {State₁ State₂ Label : Type*} {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
variable {s₁ : State₁} {s₂ : State₂}

-- Symmetry must support different state types and universes, as the relations do.
example (h : s₁ ≤≥[lts₁,lts₂] s₂) : s₂ ≤≥[lts₂,lts₁] s₁ := h.symm

example (h : s₁ ~[lts₁,lts₂] s₂) : s₂ ~[lts₂,lts₁] s₁ := h.symm

example (h : s₁ ~[lts₁,lts₂] s₂) : s₂ ~[lts₂,lts₁] s₁ := by
  symm
  exact h

open scoped Bisimilarity in
example (h : s₁ ~[lts₁,lts₂] s₂) : s₂ ~[lts₂,lts₁] s₁ := by grind

-- The named state-type arguments match the heterogeneous symmetry statements.
example (h : s₁ ≤≥[lts₁,lts₂] s₂) : s₂ ≤≥[lts₂,lts₁] s₁ :=
  SimulationEquiv.symm (State₁ := State₁) (s2 := s₂) h

example (h : s₁ ~[lts₁,lts₂] s₂) : s₂ ~[lts₂,lts₁] s₁ :=
  Bisimilarity.symm (State₁ := State₁) h

end Heterogeneous

-- A relation can be a bisimulation up to bisimilarity without itself being a bisimulation.
-- Soundness gives a bisimulation on its closure and bisimilarity of its related states.
private def completeLTS : LTS Bool Unit := ⟨fun _ _ _ => True⟩

private def onlyFalse (s t : Bool) : Prop := s = false ∧ t = false

private theorem completeLTS_bisimilar (s t : Bool) : s ~[completeLTS] t := by
  refine ⟨fun _ _ => True, trivial, ?_⟩
  intro _ _ _ _
  exact ⟨fun _ _ => ⟨false, trivial, trivial⟩, fun _ _ => ⟨false, trivial, trivial⟩⟩

private theorem onlyFalse_closure (s t : Bool) :
    UpToHomBisimilarity completeLTS completeLTS onlyFalse s t :=
  ⟨false, completeLTS_bisimilar s false, false, ⟨rfl, rfl⟩, completeLTS_bisimilar false t⟩

private theorem onlyFalse_upTo : IsBisimulationUpTo completeLTS completeLTS onlyFalse := by
  intro _ _ _ _
  exact ⟨fun s _ => ⟨false, trivial, onlyFalse_closure s false⟩,
    fun t _ => ⟨false, trivial, onlyFalse_closure false t⟩⟩

example : onlyFalse ≤ HomBisimilarity completeLTS := onlyFalse_upTo.le_bisimilarity

example : ¬ IsHomBisimulation completeLTS onlyFalse := by
  intro h
  obtain ⟨_, _, hr⟩ := (h (show onlyFalse false false from ⟨rfl, rfl⟩) ()).1 true trivial
  exact Bool.noConfusion hr.1

end CslibTests
