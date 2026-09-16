/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Aviv Bar Natan
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Lattice.Nat

/-!
# Tape head visitation and space-usage lemmas

This file collects lemmas about the set of positions visited by a work-tape head
(`MultiTapeTM.visitedByTapeHead`) and the resulting space-usage measures
(`MultiTapeTM.spaceUsedByTape`, `MultiTapeTM.spaceUsed`) and how the tape head positions
influence the cells that are modified on a tape.

`MultiTapeTM.exists_spaceUsedByTape_max` shows that a computation whose space usage is bounded
attains its per-tape space usage at a single step, which makes a bound that holds at every point
in time usable as a bound for the whole run.

-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ}
variable {State Symbol : Type*}
variable {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}
variable {cfg : Cfg k Symbol State input}

/-- If the work tape head is not at position `z`, then the tape does not change there. -/
lemma step_workTapes_eq_of_ne
    (cfg : Cfg k Symbol State input)
    (j : Fin k)
    (z : ℤ)
    (hz : z ≠ cfg.workTapePos j) :
    (tm.step cfg).workTapes j z = cfg.workTapes j z :=
  (tm.step_step cfg).workTapes_eq_of_ne j z hz

lemma mem_visitedByTapeHead {t : ℕ} {i : Fin k} {z : ℤ} :
    z ∈ tm.visitedByTapeHead cfg t i ↔ ∃ t' < t + 1, (tm.runFrom cfg t').workTapePos i = z := by
  simp [visitedByTapeHead, MultiTapeNTM.ComputationPath.visited, visitedOfCfgs]

lemma mem_visitedByTapeHead_self (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    (tm.runFrom cfg t).workTapePos i ∈ tm.visitedByTapeHead cfg t i :=
  tm.mem_visitedByTapeHead.mpr ⟨t, by omega, rfl⟩

/-- The set of positions visited by a tape head is monotone in the number of steps. -/
lemma visitedByTapeHead_mono (cfg : Cfg k Symbol State input) (i : Fin k) {t t' : ℕ} (h : t ≤ t') :
    tm.visitedByTapeHead cfg t i ⊆ tm.visitedByTapeHead cfg t' i :=
  visitedOfCfgs_mono (List.map_subset _ (List.range_subset.mpr (by omega))) i

/-- Starting from configuration `cfg`, every position between the initial head position of tape
`i` and the one after `t` steps is part of the "visited set" at step `t`. -/
lemma uIcc_workTapePos_subset_visitedByTapeHead
    (cfg : Cfg k Symbol State input) (i : Fin k) (t : ℕ) :
    Finset.uIcc (cfg.workTapePos i) ((tm.runFrom cfg t).workTapePos i)
      ⊆ tm.visitedByTapeHead cfg t i :=
  (tm.runPath cfg t).uIcc_workTapePos_subset_visited i

/-- If a work tape cell is changed after `t` steps, it must have been visited by the tape head. -/
lemma mem_visitedByTapeHead_of_workTapes_ne
    (j : Fin k)
    (t : ℕ)
    (z : ℤ)
    (h : (tm.runFrom cfg t).workTapes j z ≠ cfg.workTapes j z) :
    z ∈ tm.visitedByTapeHead cfg t j :=
  (tm.runPath cfg t).mem_visited_of_workTapes_ne j z h

/-- Every position visited by the head of tape `i` lies within `spaceUsedByTape … i` of the
head's starting position. -/
lemma natAbs_le_spaceUsedByTape_of_mem_visited
    {i : Fin k}
    {z : ℤ}
    {t : ℕ}
    (hz : z ∈ tm.visitedByTapeHead cfg t i) :
    (z - cfg.workTapePos i).natAbs ≤ tm.spaceUsedByTape cfg t i :=
  (tm.runPath cfg t).natAbs_le_spaceByTape_of_mem_visited i hz

/-- Every non-blank cell on work tape `i` lies within `spaceUsedByTape … i t` of the origin. -/
lemma content_natAbs_le_spaceUsedByTape
    {i : Fin k}
    (t : ℕ)
    (z : ℤ)
    (h : (tm.runFrom (tm.initCfg input) t).workTapes i z ≠ none) :
    z.natAbs ≤ tm.spaceUsedByTape (tm.initCfg input) t i := by
  -- The work tapes start out blank, so any non-blank cell has been visited by the head; the
  -- initial head position is `0`, so the displacement bound is a bound on the position itself.
  simpa using tm.natAbs_le_spaceUsedByTape_of_mem_visited
    (tm.mem_visitedByTapeHead_of_workTapes_ne i t z h)

/-- The number of cells touched by a single work tape grows by at most one each step. -/
lemma spaceUsedByTape_le (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ t + 1 := by
  simpa only [spaceUsedByTape, runPath_time] using (tm.runPath cfg t).spaceByTape_le i

/-- The space used by a computation is bounded linearly by the number of steps. -/
lemma spaceUsed_linear (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t ≤ k * t + k := by
  simpa using (tm.runPath cfg t).space_le

/-- The space used by a single tape is monotone in the number of steps. -/
lemma spaceUsedByTape_mono
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input)
    (i : Fin k) :
    Monotone (tm.spaceUsedByTape cfg · i) := by
  intro t t' h
  exact Finset.card_le_card (tm.visitedByTapeHead_mono cfg i h)

/-- The total space used is monotone in the number of steps. -/
lemma spaceUsed_mono (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) :
    Monotone (tm.spaceUsed cfg ·) :=
  fun _ _ h => spaceUsedOfCfgs_mono (List.map_subset _ (List.range_subset.mpr (by omega)))

/-- A computation whose total space usage stays below a bound reaches a step `T` at which the space
usage of *every* tape is maximal. This turns a bound that holds at every point in time into a
bound for the whole run. -/
lemma exists_spaceUsedByTape_max (cfg : Cfg k Symbol State input) {s : ℕ}
    (hs : ∀ t, tm.spaceUsed cfg t ≤ s) :
    ∃ T, ∀ t i, tm.spaceUsedByTape cfg t i ≤ tm.spaceUsedByTape cfg T i := by
  -- The space usage of a single tape is bounded, so it attains its supremum at some step `T i`.
  have h : ∀ i, ∃ Ti, ∀ t, tm.spaceUsedByTape cfg t i ≤ tm.spaceUsedByTape cfg Ti i := by
    intro i
    have hbdd : BddAbove (Set.range (tm.spaceUsedByTape cfg · i)) :=
      ⟨s, by rintro _ ⟨t, rfl⟩; exact (tm.spaceUsedByTape_le_spaceUsed cfg t i).trans (hs t)⟩
    obtain ⟨Ti, hTi⟩ := Nat.sSup_mem (Set.range_nonempty (tm.spaceUsedByTape cfg · i)) hbdd
    exact ⟨Ti, fun t => (le_csSup hbdd ⟨t, rfl⟩).trans hTi.ge⟩
  choose T hT using h
  -- Monotonicity lets us use a single step that is late enough for every tape.
  exact ⟨Finset.univ.sup T, fun t i =>
    (hT i t).trans (tm.spaceUsedByTape_mono cfg i (Finset.le_sup (Finset.mem_univ i)))⟩

end Turing.MultiTapeTM
