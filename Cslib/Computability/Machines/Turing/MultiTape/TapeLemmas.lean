/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Data.Int.Interval

/-!
# Tape head visitation and space-usage lemmas

This file collects lemmas about the set of positions visited by a work-tape head
(`MultiTapeTM.visitedByTapeHead`) and the resulting space-usage measures
(`MultiTapeTM.spaceUsedByTape`, `MultiTapeTM.spaceUsed`) and how the tape head positions
influence the cells that are modified on a tape.

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
    (tm.step cfg).workTapes j z = cfg.workTapes j z := by
  unfold step
  cases hst : cfg.state with
  | none => simp_all
  | some q =>
    rcases hw : ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workActions j).1 <;> simp_all

lemma mem_visitedByTapeHead {t : ℕ} {i : Fin k} {z : ℤ} :
    z ∈ tm.visitedByTapeHead cfg t i ↔ ∃ t' < t + 1, (tm.runFrom cfg t').workTapePos i = z := by
  simp [visitedByTapeHead]

lemma mem_visitedByTapeHead_self (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    (tm.runFrom cfg t).workTapePos i ∈ tm.visitedByTapeHead cfg t i :=
  tm.mem_visitedByTapeHead.mpr ⟨t, by omega, rfl⟩

/-- The set of positions visited by a tape head is monotone in the number of steps. -/
lemma visitedByTapeHead_mono (cfg : Cfg k Symbol State input) (i : Fin k) {t t' : ℕ} (h : t ≤ t') :
    tm.visitedByTapeHead cfg t i ⊆ tm.visitedByTapeHead cfg t' i := by
  apply Finset.image_subset_image
  grind

/-- Starting from configuration `cfg`, every position between the initial head position of tape
`i` and the one after `t` steps is part of the "visited set" at step `t`. -/
lemma uIcc_workTapePos_subset_visitedByTapeHead
    (cfg : Cfg k Symbol State input) (i : Fin k) (t : ℕ) :
    Finset.uIcc (cfg.workTapePos i) ((tm.runFrom cfg t).workTapePos i)
      ⊆ tm.visitedByTapeHead cfg t i := by
  induction t with
  | zero => simpa [runFrom] using tm.mem_visitedByTapeHead_self cfg 0 i
  | succ t ih =>
    intro z hz
    have hstep : |(tm.runFrom cfg (t + 1)).workTapePos i - (tm.runFrom cfg t).workTapePos i| ≤ 1 :=
      runFrom_succ_eq_step' (tm := tm) ▸ tm.workTapePos_step_le _ i
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
  | zero => exact absurd (by simp [runFrom]) h
  | succ t ih =>
    rw [runFrom_succ_eq_step'] at h
    by_cases hz : z = (tm.runFrom cfg t).workTapePos j
    · exact hz ▸ tm.visitedByTapeHead_mono cfg j (Nat.le_succ t)
        (tm.mem_visitedByTapeHead_self cfg t j)
    · rw [tm.step_workTapes_eq_of_ne _ j z hz] at h
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
  calc
    tm.spaceUsedByTape cfg t i
    _ ≤ (Finset.range (t + 1)).card := Finset.card_image_le
    _ = t + 1 := Finset.card_range _

/-- The space used by a computation is bounded linearly by the number of steps. -/
lemma spaceUsed_linear (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t ≤ k * t + k := by
  calc tm.spaceUsed cfg t
      = ∑ i, (tm.spaceUsedByTape cfg t i) := by rfl
    _ ≤ ∑ i, (t + 1) := Finset.sum_le_sum (fun i _ => tm.spaceUsedByTape_le cfg t i)
    _ = k * t + k := by simp [Nat.mul_succ]

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
  exact Finset.sum_le_sum (fun i _ => spaceUsedByTape_mono tm cfg i h)

/-- The cells a run visits are the ones visited by its two halves. -/
lemma visitedByTapeHead_add (cfg : Cfg k Symbol State input) (a b : ℕ) (i : Fin k) :
    tm.visitedByTapeHead cfg (a + b) i =
      tm.visitedByTapeHead cfg a i ∪ tm.visitedByTapeHead (tm.runFrom cfg a) b i := by
  ext z
  simp only [mem_visitedByTapeHead, Finset.mem_union]
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases Nat.lt_or_ge r (a + 1) with h | h
    · exact Or.inl ⟨r, h, rfl⟩
    · exact Or.inr ⟨r - a, by omega,
        by rw [← runFrom_add, show a + (r - a) = r from by omega]⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨r, by omega, rfl⟩
    · exact ⟨a + r, by omega, by rw [runFrom_add]⟩

/-- Splitting a run into two phases can only overcount the cells it visits, since the two phases
may revisit each other's cells. -/
lemma spaceUsed_add_le (cfg : Cfg k Symbol State input) (a b : ℕ) :
    tm.spaceUsed cfg (a + b) ≤ tm.spaceUsed cfg a + tm.spaceUsed (tm.runFrom cfg a) b := by
  rw [spaceUsed, spaceUsed, spaceUsed, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [spaceUsedByTape, visitedByTapeHead_add]
  exact Finset.card_union_le _ _

/-- Space usage only depends on where the work-tape heads are at each step, so two runs whose head
positions agree use the same space. This is what lets a machine be replaced by a simulation of it,
or by the same machine started with different output already accumulated. -/
lemma spaceUsed_eq_of_workTapePos {State' : Type*} {input' : List Symbol}
    {tm' : MultiTapeTM k Symbol State'} (cfg : Cfg k Symbol State input)
    (cfg' : Cfg k Symbol State' input') (t : ℕ)
    (h : ∀ m ≤ t, (tm.runFrom cfg m).workTapePos = (tm'.runFrom cfg' m).workTapePos) :
    tm.spaceUsed cfg t = tm'.spaceUsed cfg' t := by
  refine Finset.sum_congr rfl fun i _ => congrArg Finset.card (Finset.image_congr fun m hm => ?_)
  exact congrFun (h m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))) i

/-- A run that never takes a head outside the cells another run visits uses no more space than
that other run. This is the sharp form of the space bound for a phase that moves no head: such a
phase visits no new cell at all, rather than one per tape. -/
lemma spaceUsed_le_of_workTapePos_mem {State' : Type*} {input' : List Symbol}
    {tm' : MultiTapeTM k Symbol State'} (cfg : Cfg k Symbol State input)
    (cfg' : Cfg k Symbol State' input') (t t' : ℕ)
    (h : ∀ m ≤ t, ∀ i, (tm.runFrom cfg m).workTapePos i ∈ tm'.visitedByTapeHead cfg' t' i) :
    tm.spaceUsed cfg t ≤ tm'.spaceUsed cfg' t' := by
  refine Finset.sum_le_sum fun i _ => Finset.card_le_card fun z hz => ?_
  obtain ⟨m, hm, rfl⟩ := mem_visitedByTapeHead.mp hz
  exact h m (by omega) i

end Turing.MultiTapeTM
