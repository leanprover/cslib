/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Lattice.Nat

/-!
# Head movement along run paths

This file collects how a step moves the work-tape heads and changes the work tapes, and what this
implies for the cells visited along a run path: a head moves by at most one cell per step, so it
visits every cell between its first and last positions, and a cell changes only under its head.

`MultiTapeNTM.RunPath.inWindow_of_space_le` keeps the heads of a path that starts at cell `0`
within the window given by its space.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k k' : ℕ} {State State' Symbol : Type*} {input input' : List Symbol}
variable {ntm : MultiTapeNTM k Symbol State} {ntm' : MultiTapeNTM k' Symbol State'}

/-- A work-tape head moves by at most one cell in a single step. -/
lemma Step.workTapePos_le {c c' : Cfg k Symbol State input} (h : ntm.Step c c') (i : Fin k) :
    |c'.workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold Step at h
  split at h
  · simp [h]
  · obtain ⟨a, _, rfl⟩ := h
    exact workTapePos_apply_le a c i

/-- A step does not change a work-tape cell away from its head. -/
lemma Step.workTapes_eq_of_ne {c c' : Cfg k Symbol State input} (h : ntm.Step c c') {i : Fin k}
    {z : ℤ} (hz : z ≠ c.workTapePos i) : c'.workTapes i z = c.workTapes i z := by
  unfold Step at h
  split at h
  · simp [h]
  · obtain ⟨a, _, rfl⟩ := h
    rw [Action.apply_workTapes]
    cases ha : (a.workTapes i).1 <;> simp [ha, hz]

namespace RunPath

/-- Every position between the first and the last position of a head along a path is visited,
since the head moves by at most one cell per step. -/
lemma uIcc_workTapePos_subset_visitedByTapeHead (p : ntm.RunPath input) (i : Fin k) :
    Finset.uIcc (p.head.workTapePos i) (p.last.workTapePos i) ⊆ p.visitedByTapeHead i := by
  induction p using RelSeries.inductionOn' with
  | singleton c =>
    simp +instances [visitedByTapeHead, RelSeries.singleton, RelSeries.head, RelSeries.last]
  | snoc p c h ih =>
    have hm := abs_le.mp (Step.workTapePos_le h i)
    rw [RelSeries.head_snoc, RelSeries.last_snoc, visitedByTapeHead_snoc]
    intro z hz
    by_cases he : z = c.workTapePos i
    · exact he ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (ih (by rw [Finset.mem_uIcc] at hz ⊢; omega))

/-- A work-tape cell that differs between the first and the last configuration of a path was
visited by its head. -/
lemma mem_visitedByTapeHead_of_workTapes_ne (p : ntm.RunPath input) {i : Fin k} {z : ℤ}
    (h : p.last.workTapes i z ≠ p.head.workTapes i z) : z ∈ p.visitedByTapeHead i := by
  induction p using RelSeries.inductionOn' with
  | singleton c => exact absurd rfl h
  | snoc p c hs ih =>
    rw [visitedByTapeHead_snoc]
    refine Finset.mem_insert_of_mem ?_
    by_cases hz : z = p.last.workTapePos i
    · exact hz ▸ Finset.mem_image_of_mem _ (Finset.mem_univ (Fin.last _))
    · rw [RelSeries.last_snoc, RelSeries.head_snoc, Step.workTapes_eq_of_ne hs hz] at h
      exact ih h

/-- Every position visited by a head lies within the space of its tape from its first position. -/
lemma natAbs_le_spaceUsedByTape_of_mem_visited (p : ntm.RunPath input) {i : Fin k} {z : ℤ}
    (hz : z ∈ p.visitedByTapeHead i) :
    (z - p.head.workTapePos i).natAbs ≤ p.spaceUsedByTape i := by
  obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hz
  -- the prefix up to `n` visits every position between the first position and the one at `n`
  have hsub : visitedByTapeHead (p.take n) i ⊆ p.visitedByTapeHead i :=
    Finset.image_subset_iff.mpr fun j _ =>
      p.mem_visitedByTapeHead.mpr ⟨_, ⟨Fin.castLE n.isLt j, rfl⟩, rfl⟩
  have h := Finset.card_le_card
    ((uIcc_workTapePos_subset_visitedByTapeHead (p.take n) i).trans hsub)
  rw [RelSeries.head_take, RelSeries.last_take, Int.card_uIcc] at h
  change _ ≤ (p.visitedByTapeHead i).card
  omega

/-- A path that starts with every head at cell `0` and visits at most `s` cells keeps its heads
within `[-s, s]`. -/
lemma inWindow_of_space_le {p : ntm.RunPath input} {s : ℕ} (h0 : ∀ i, p.head.workTapePos i = 0)
    (hs : p.space ≤ s) : p.InWindow s := fun c hc i => by
  have hz := p.natAbs_le_spaceUsedByTape_of_mem_visited
    ((p.mem_visitedByTapeHead (i := i)).mpr ⟨c, hc, rfl⟩)
  rw [h0, sub_zero] at hz
  exact mem_window.mpr <| hz.trans <|
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs

end RunPath

/-- A machine never reads its output tape, so prepending a word to the output preserves steps. -/
@[simps]
def prependOutputHom (ntm : MultiTapeNTM k Symbol State) (pre : List Symbol) :
    (ntm.stepRel input).Hom (ntm.stepRel input) where
  toFun c := c.prependOutput pre
  map_rel' {c c'} h := by
    change ntm.Step c c' at h
    change ntm.Step (c.prependOutput pre) (c'.prependOutput pre)
    unfold Step at h ⊢
    rcases hq : c.state with _ | q <;> simp only [hq, Cfg.prependOutput_state] at h ⊢
    · rw [h]
    · obtain ⟨a, ha, rfl⟩ := h
      exact ⟨a, ha, Cfg.ext rfl rfl rfl rfl (by simp [Action.apply])⟩

end Turing.MultiTapeNTM
