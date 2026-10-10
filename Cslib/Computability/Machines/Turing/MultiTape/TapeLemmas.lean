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
# Tape head visitation and space-usage lemmas

This file collects lemmas about the set of positions visited by a work-tape head
(`MultiTapeTM.visitedByTapeHead`) and the resulting space-usage measures
(`MultiTapeTM.spaceUsedByTape`, `MultiTapeTM.spaceUsed`) and how the tape head positions
influence the cells that are modified on a tape.

`MultiTapeTM.exists_spaceUsedByTape_max` shows that a computation whose space usage is bounded
attains its per-tape space usage at a single step, which makes a bound that holds at every point
in time usable as a bound for the whole run.

A simulation maps every run path of one machine to a run path of another with `RunPath.map`.
`MultiTapeNTM.RunPath.space_map_le` compares the space of the two paths through the positions of
the work-tape heads.

-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k k' : ℕ} {State State' Symbol : Type*} {input input' : List Symbol}
variable {ntm : MultiTapeNTM k Symbol State} {ntm' : MultiTapeNTM k' Symbol State'}

namespace RunPath

/-- A set containing every position of a head along a path bounds the space used by its tape. -/
lemma spaceUsedByTape_le_card (p : ntm.RunPath input) {i : Fin k} {S : Finset ℤ}
    (h : ∀ c ∈ p, c.workTapePos i ∈ S) : p.spaceUsedByTape i ≤ S.card :=
  Finset.card_le_card (Finset.image_subset_iff.mpr fun n _ => h (p n) ⟨n, rfl⟩)

/-- Sets containing every position of the heads along a path bound its space by their total
size. -/
lemma space_le_sum_card (p : ntm.RunPath input) {S : Fin k → Finset ℤ}
    (h : ∀ c ∈ p, ∀ i, c.workTapePos i ∈ S i) : p.space ≤ ∑ i, (S i).card :=
  Finset.sum_le_sum fun i _ => p.spaceUsedByTape_le_card fun c hc => h c hc i

/-! ### Mapped paths -/

/-- If the head of tape `i'` of a mapped path follows the head of tape `i` of the source path, the
two tapes visit the same cells. -/
lemma visitedByTapeHead_map (p : ntm.RunPath input)
    (f : (ntm.stepRel input).Hom (ntm'.stepRel input')) {i : Fin k} {i' : Fin k'}
    (h : ∀ c ∈ p, (f c).workTapePos i' = c.workTapePos i) :
    (p.map f).visitedByTapeHead i' = p.visitedByTapeHead i :=
  Finset.image_congr fun n _ => h (p n) ⟨n, rfl⟩

/-- A set containing the head position of every image of a configuration on the source path bounds
the space used by that tape of the mapped path. -/
lemma spaceUsedByTape_map_le_card (p : ntm.RunPath input)
    (f : (ntm.stepRel input).Hom (ntm'.stepRel input')) {i : Fin k'} {S : Finset ℤ}
    (h : ∀ c ∈ p, (f c).workTapePos i ∈ S) : (p.map f).spaceUsedByTape i ≤ S.card :=
  (p.map f).spaceUsedByTape_le_card fun _ ⟨n, hn⟩ => hn ▸ h (p n) ⟨n, rfl⟩

/-- **Space of a simulation.** If the heads of the tapes `e j` of a mapped path follow the heads of
the tapes `j` of the source path, and each remaining tape of the mapped path visits at most `b`
cells, then the mapped path uses the space of the source path plus at most `b` cells per remaining
tape. -/
lemma space_map_le (p : ntm.RunPath input) (f : (ntm.stepRel input).Hom (ntm'.stepRel input'))
    (e : Fin k ↪ Fin k') (b : ℕ) (he : ∀ c ∈ p, ∀ j, (f c).workTapePos (e j) = c.workTapePos j)
    (hrest : ∀ l ∉ Set.range e, (p.map f).spaceUsedByTape l ≤ b) :
    (p.map f).space ≤ p.space + (k' - k) * b := by
  classical
  rw [space, space, ← Finset.sum_add_sum_compl (Finset.univ.map e), Finset.sum_map]
  refine add_le_add (Finset.sum_le_sum fun j _ => (congrArg Finset.card
    (p.visitedByTapeHead_map f fun c hc => he c hc j)).le) ?_
  refine (Finset.sum_le_card_nsmul _ _ b fun l hl => hrest l (by simpa using hl)).trans ?_
  simp [Finset.card_compl]

/-- A map preserving every head position preserves space. -/
lemma space_map_eq {ntm' : MultiTapeNTM k Symbol State'} (p : ntm.RunPath input)
    (f : (ntm.stepRel input).Hom (ntm'.stepRel input'))
    (h : ∀ c ∈ p, (f c).workTapePos = c.workTapePos) : (p.map f).space = p.space :=
  Finset.sum_congr rfl fun i _ =>
    congrArg Finset.card (p.visitedByTapeHead_map f fun c hc => congrFun (h c hc) i)

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
  cases hst : cfg.state with
  | none => simp [step_of_halt hst]
  | some q =>
    rw [step_of_state hst, Action.apply_workTapes]
    rcases hw : ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workTapes j).1 <;> simp_all

lemma mem_visitedByTapeHead {t : ℕ} {i : Fin k} {z : ℤ} :
    z ∈ tm.visitedByTapeHead cfg t i ↔ ∃ t' < t + 1, (tm.runFrom cfg t').workTapePos i = z := by
  simp [visitedByTapeHead, Fin.exists_iff]

lemma mem_visitedByTapeHead_self (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    (tm.runFrom cfg t).workTapePos i ∈ tm.visitedByTapeHead cfg t i :=
  tm.mem_visitedByTapeHead.mpr ⟨t, by omega, rfl⟩

/-- The set of positions visited by a tape head is monotone in the number of steps. -/
lemma visitedByTapeHead_mono (cfg : Cfg k Symbol State input) (i : Fin k) {t t' : ℕ} (h : t ≤ t') :
    tm.visitedByTapeHead cfg t i ⊆ tm.visitedByTapeHead cfg t' i := by
  intro z hz
  obtain ⟨n, hn, hz⟩ := tm.mem_visitedByTapeHead.mp hz
  exact tm.mem_visitedByTapeHead.mpr ⟨n, by omega, hz⟩

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
    have hstep :
        |(tm.runFrom cfg (t + 1)).workTapePos i - (tm.runFrom cfg t).workTapePos i| ≤ 1 := by
      simpa only [runFrom, Function.iterate_succ_apply'] using
        tm.workTapePos_step_le (tm.runFrom cfg t) i
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
    rw [runFrom, Function.iterate_succ_apply', ← runFrom] at h
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

/-- The number of cells visited by a single work-tape head grows by at most one each step. -/
lemma spaceUsedByTape_le (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ t + 1 :=
  Finset.card_image_le.trans_eq (by simp)

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
