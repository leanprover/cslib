/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Tape head visitation and space-usage lemmas

This file collects lemmas about the set of positions visited by a work-tape head
(`MultiTapeTM.visitedByTapeHead`) and the resulting space-usage measures
(`MultiTapeTM.spaceUsedByTape`, `MultiTapeTM.spaceUsed`) and how the tape head positions
influence the cells that are modified on a tape.

Those measures are read off the machine's own run, so results that hold of any run come from
`MultiTapeNTM.ComputationPath` rather than being proved again here.

-/

@[expose] public section

namespace Turing

namespace MultiTapeNTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}
  {ntm : MultiTapeNTM k Symbol State}

/-- A work tape head moves by at most one cell in a step. -/
lemma workTapePos_step_le {c c' : Cfg k Symbol State input} (h : ntm.Step c c') (i : Fin k) :
    |c'.workTapePos i - c.workTapePos i| ≤ 1 := by
  cases hq : c.state with
  | none => simp_all [Step, Cfg.StepWith]
  | some q =>
    simp only [Step, Cfg.StepWith, hq] at h
    obtain ⟨a, -, rfl⟩ := h
    exact workTapePos_apply_le a c i

/-- A step changes no work tape cell but the one its head is on. -/
lemma workTapes_step_eq_of_ne {c c' : Cfg k Symbol State input} (h : ntm.Step c c') (j : Fin k)
    (z : ℤ) (hz : z ≠ c.workTapePos j) : c'.workTapes j z = c.workTapes j z := by
  cases hq : c.state with
  | none => simp_all [Step, Cfg.StepWith]
  | some q =>
    simp only [Step, Cfg.StepWith, hq] at h
    obtain ⟨a, -, rfl⟩ := h
    exact workTapes_apply_eq_of_ne a c j z hz

end MultiTapeNTM

namespace MultiTapeTM

variable {k : ℕ}
variable {State Symbol : Type*}
variable {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}
variable {cfg : Cfg k Symbol State input}

lemma mem_visitedByTapeHead {t : ℕ} {i : Fin k} {z : ℤ} :
    z ∈ tm.visitedByTapeHead cfg t i ↔ ∃ t' < t + 1, (tm.runFrom cfg t').workTapePos i = z := by
  simp [visitedByTapeHead, visitedOfCfgs, runPath_cfgs]

lemma mem_visitedByTapeHead_self (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    (tm.runFrom cfg t).workTapePos i ∈ tm.visitedByTapeHead cfg t i :=
  tm.mem_visitedByTapeHead.mpr ⟨t, by omega, rfl⟩

/-- The set of positions visited by a tape head is monotone in the number of steps. -/
lemma visitedByTapeHead_mono (cfg : Cfg k Symbol State input) (i : Fin k) {t t' : ℕ} (h : t ≤ t') :
    tm.visitedByTapeHead cfg t i ⊆ tm.visitedByTapeHead cfg t' i := by
  intro z hz
  rw [mem_visitedByTapeHead] at hz ⊢
  grind

/-- Starting from configuration `cfg`, every position between the initial head position of tape
`i` and the one after `t` steps is part of the "visited set" at step `t`. -/
lemma uIcc_workTapePos_subset_visitedByTapeHead
    (cfg : Cfg k Symbol State input) (i : Fin k) (t : ℕ) :
    Finset.uIcc (cfg.workTapePos i) ((tm.runFrom cfg t).workTapePos i)
      ⊆ tm.visitedByTapeHead cfg t i := by
  induction t with
  | zero => simpa using tm.mem_visitedByTapeHead_self cfg 0 i
  | succ t ih =>
    intro z hz
    have hstep : |(tm.runFrom cfg (t + 1)).workTapePos i - (tm.runFrom cfg t).workTapePos i| ≤ 1 :=
      runFrom_succ_eq_step' (tm := tm) ▸ MultiTapeNTM.workTapePos_step_le (step_iff.mpr rfl) i
    have hmono := tm.visitedByTapeHead_mono cfg i (Nat.le_succ t)
    have hself := tm.mem_visitedByTapeHead_self cfg (t + 1) i
    grind [Finset.mem_uIcc]

/-- If a work tape cell is changed after `t` steps, it must have been visited by the tape head. -/
lemma mem_visitedByTapeHead_of_workTapes_ne
    (j : Fin k)
    (t : ℕ)
    (z : ℤ)
    (h : (tm.runFrom cfg t).workTapes j z ≠ cfg.workTapes j z) :
    z ∈ tm.visitedByTapeHead cfg t j := by
  induction t with
  | zero => exact absurd (by simp) h
  | succ t ih =>
    rw [runFrom_succ_eq_step'] at h
    by_cases hz : z = (tm.runFrom cfg t).workTapePos j
    · exact hz ▸ tm.visitedByTapeHead_mono cfg j (Nat.le_succ t)
        (tm.mem_visitedByTapeHead_self cfg t j)
    · rw [MultiTapeNTM.workTapes_step_eq_of_ne (step_iff.mpr rfl) j z hz] at h
      exact tm.visitedByTapeHead_mono cfg j (Nat.le_succ t) (ih h)

/-- Every position visited by the head of tape `i` lies within `spaceUsedByTape … i` of the
head's starting position. -/
lemma natAbs_le_spaceUsedByTape_of_mem_visited
    {i : Fin k}
    {z : ℤ}
    {t : ℕ}
    (hz : z ∈ tm.visitedByTapeHead cfg t i) :
    (z - cfg.workTapePos i).natAbs ≤ tm.spaceUsedByTape cfg t i := by
  obtain ⟨t', ht', rfl⟩ := tm.mem_visitedByTapeHead.mp hz
  have h1 := Finset.card_le_card
    ((tm.uIcc_workTapePos_subset_visitedByTapeHead cfg i t').trans
      (tm.visitedByTapeHead_mono cfg i (show t' ≤ t by omega)))
  rw [Int.card_uIcc] at h1
  unfold spaceUsedByTape
  omega

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
  unfold spaceUsedByTape visitedByTapeHead visitedOfCfgs
  exact (List.toFinset_card_le _).trans (by simp [MultiTapeNTM.ComputationPath.length_cfgs])

/-- The space used by a computation is bounded linearly by the number of steps. This is
`ComputationPath.space_le_linear` read off the machine's own run. -/
lemma spaceUsed_linear (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t ≤ k * t + k := by
  simpa using (tm.runPath cfg t).space_le_linear

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
    Monotone (tm.spaceUsed cfg ·) := by
  intro t t' h
  simp only [spaceUsed_eq_spaceUsedOfCfgs]
  exact spaceUsedOfCfgs_mono ((List.range_sublist.mpr (by omega)).map _)

end MultiTapeTM

end Turing
