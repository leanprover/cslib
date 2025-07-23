/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Semantics.LTS.Bisimulation

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
  simp [Bisimulation]
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
