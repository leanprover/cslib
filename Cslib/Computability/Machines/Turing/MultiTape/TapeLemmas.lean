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

This file collects lemmas about the positions visited by work-tape heads along a run path,
the resulting space usage, and the cells modified on a tape. These lemmas apply to both
deterministic and nondeterministic machines.

`MultiTapeTM.exists_spaceUsedByTape_max` shows that a deterministic computation whose space
usage is bounded attains its per-tape space usage at a single step.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

namespace MultiTapeNTM

variable {ntm : MultiTapeNTM k Symbol State}

/-- A work-tape head moves by at most one cell in a step. -/
lemma Step.workTapePos_le {c c' : Cfg k Symbol State input} (h : ntm.Step c c') (i : Fin k) :
    |c'.workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold Step at h
  split at h
  · simp [h]
  · obtain ⟨action, _, rfl⟩ := h
    exact workTapePos_apply_le action c i

/-- A step changes a work tape only at its head position. -/
lemma Step.workTapes_eq_of_ne {c c' : Cfg k Symbol State input} (h : ntm.Step c c')
    {i : Fin k} {z : ℤ} (hz : z ≠ c.workTapePos i) :
    c'.workTapes i z = c.workTapes i z := by
  unfold Step at h
  split at h
  · simp [h]
  · obtain ⟨action, _, rfl⟩ := h
    simp only [Action.apply_workTapes]
    cases (action.workTapes i).1 <;> simp [hz]

namespace RunPath

lemma mem_visitedByTapeHead (p : ntm.RunPath input) {i : Fin k} {z : ℤ} :
    z ∈ p.visitedByTapeHead i ↔ ∃ n, (p n).workTapePos i = z := by
  simp [visitedByTapeHead]

lemma mem_visitedByTapeHead_self (p : ntm.RunPath input) (n : Fin (p.length + 1)) (i : Fin k) :
    (p n).workTapePos i ∈ p.visitedByTapeHead i :=
  p.mem_visitedByTapeHead.mpr ⟨n, rfl⟩

/-- Every position visited by a prefix is visited by the whole path. -/
lemma visitedByTapeHead_take_subset (p : ntm.RunPath input) (n : Fin (p.length + 1)) (i : Fin k) :
    visitedByTapeHead (p.take n) i ⊆ p.visitedByTapeHead i := by
  intro z hz
  obtain ⟨m, rfl⟩ := (mem_visitedByTapeHead (p.take n)).mp hz
  exact p.mem_visitedByTapeHead.mpr ⟨⟨m, by have := m.isLt; have := n.isLt; simp_all; omega⟩, rfl⟩

/-- Every position between the initial head position and a later position is visited. -/
lemma uIcc_workTapePos_subset_visitedByTapeHead (p : ntm.RunPath input) (i : Fin k)
    (n : Fin (p.length + 1)) :
    Finset.uIcc (p.head.workTapePos i) ((p n).workTapePos i) ⊆ p.visitedByTapeHead i := by
  induction n using Fin.induction with
  | zero => simpa [RelSeries.head] using p.mem_visitedByTapeHead_self 0 i
  | succ n ih =>
    have hstep := Step.workTapePos_le (ntm := ntm) (p.step n) i
    have hself := p.mem_visitedByTapeHead_self n.succ i
    intro z hz
    have hm := abs_le.mp hstep
    by_cases he : z = (p n.succ).workTapePos i
    · exact he ▸ hself
    · apply ih
      rw [Finset.mem_uIcc] at hz ⊢
      omega

/-- A changed work-tape cell has been visited by its head. -/
lemma mem_visitedByTapeHead_of_workTapes_ne (p : ntm.RunPath input)
    (n : Fin (p.length + 1)) (i : Fin k) (z : ℤ)
    (h : (p n).workTapes i z ≠ p.head.workTapes i z) :
    z ∈ p.visitedByTapeHead i := by
  induction n using Fin.induction with
  | zero => exact (h rfl).elim
  | succ n ih =>
    by_cases hz : z = (p n.castSucc).workTapePos i
    · exact hz ▸ p.mem_visitedByTapeHead_self n.castSucc i
    · exact ih (by rwa [Step.workTapes_eq_of_ne (ntm := ntm) (p.step n) hz] at h)

/-- Every visited position lies within the per-tape space bound of the head's starting position. -/
lemma natAbs_le_spaceUsedByTape_of_mem_visited (p : ntm.RunPath input)
    {i : Fin k} {z : ℤ} (hz : z ∈ p.visitedByTapeHead i) :
    (z - p.head.workTapePos i).natAbs ≤ p.spaceUsedByTape i := by
  obtain ⟨n, rfl⟩ := p.mem_visitedByTapeHead.mp hz
  have h := Finset.card_le_card (p.uIcc_workTapePos_subset_visitedByTapeHead i n)
  rw [Int.card_uIcc] at h
  unfold spaceUsedByTape
  omega

/-- The number of cells touched by a tape is bounded by the number of configurations. -/
lemma spaceUsedByTape_le (p : ntm.RunPath input) (i : Fin k) :
    p.spaceUsedByTape i ≤ p.length + 1 :=
  Finset.card_image_le.trans_eq (by simp)

/-- The space used by a path is bounded linearly by its number of steps. -/
lemma space_linear (p : ntm.RunPath input) : p.space ≤ k * p.length + k := by
  calc p.space
      = ∑ i, p.spaceUsedByTape i := rfl
    _ ≤ ∑ i, (p.length + 1) := Finset.sum_le_sum (fun i _ ↦ p.spaceUsedByTape_le i)
    _ = k * p.length + k := by simp [Nat.mul_succ]

/-- A prefix uses no more cells on a tape than the whole path. -/
lemma spaceUsedByTape_take_le (p : ntm.RunPath input) (n : Fin (p.length + 1)) (i : Fin k) :
    spaceUsedByTape (p.take n) i ≤ p.spaceUsedByTape i :=
  Finset.card_le_card (p.visitedByTapeHead_take_subset n i)

/-- A prefix uses no more space than the whole path. -/
lemma space_take_le (p : ntm.RunPath input) (n : Fin (p.length + 1)) :
    space (p.take n) ≤ p.space :=
  Finset.sum_le_sum fun i _ ↦ p.spaceUsedByTape_take_le n i

/-- A set containing every head position contains the visited set. -/
lemma visitedByTapeHead_subset (p : ntm.RunPath input) {i : Fin k} {S : Finset ℤ}
    (h : ∀ n, (p n).workTapePos i ∈ S) : p.visitedByTapeHead i ⊆ S :=
  Finset.image_subset_iff.mpr fun n _ ↦ h n

/-- A set containing every head position bounds the space used by its tape. -/
lemma spaceUsedByTape_le_card (p : ntm.RunPath input) {i : Fin k} {S : Finset ℤ}
    (h : ∀ n, (p n).workTapePos i ∈ S) : p.spaceUsedByTape i ≤ S.card :=
  Finset.card_le_card (p.visitedByTapeHead_subset h)

/-- A head that never moves uses a single cell. -/
lemma spaceUsedByTape_le_one (p : ntm.RunPath input) {i : Fin k}
    (h : ∀ n, (p n).workTapePos i = p.head.workTapePos i) : p.spaceUsedByTape i ≤ 1 := by
  simpa using p.spaceUsedByTape_le_card (S := {p.head.workTapePos i}) fun n ↦ by simp [h n]

/-- The cells a path visits are the union of those visited by its prefix and suffix. -/
lemma visitedByTapeHead_take_union_drop (p : ntm.RunPath input) (n : Fin (p.length + 1))
    (i : Fin k) :
    p.visitedByTapeHead i = visitedByTapeHead (p.take n) i ∪ visitedByTapeHead (p.drop n) i := by
  ext z
  simp only [mem_visitedByTapeHead, Finset.mem_union]
  constructor
  · rintro ⟨m, rfl⟩
    by_cases h : m ≤ n
    · exact Or.inl ⟨⟨m, by simp; omega⟩, rfl⟩
    · refine Or.inr ⟨⟨m - n, by simp; have := m.isLt; omega⟩, ?_⟩
      simp [RelSeries.drop, Nat.sub_add_cancel (by omega : (n : ℕ) ≤ m)]
  · rintro (⟨m, rfl⟩ | ⟨m, rfl⟩)
    · exact ⟨⟨m, by have := m.isLt; have := n.isLt; simp_all; omega⟩, rfl⟩
    · exact ⟨⟨m + n, by have := m.isLt; have := n.isLt; simp_all; omega⟩, rfl⟩

/-- Splitting a path into two phases can only overcount its visited cells. -/
lemma space_le_take_add_drop (p : ntm.RunPath input) (n : Fin (p.length + 1)) :
    p.space ≤ space (p.take n) + space (p.drop n) := by
  rw [space, space, space, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [spaceUsedByTape, p.visitedByTapeHead_take_union_drop n]
  exact Finset.card_union_le _ _

/-- Paths with the same head positions at every step use the same space. -/
lemma space_eq_of_workTapePos {State' : Type*} {input' : List Symbol}
    {ntm' : MultiTapeNTM k Symbol State'} (p : ntm.RunPath input) (q : ntm'.RunPath input')
    (hlen : p.length = q.length)
    (h : ∀ n, (p n).workTapePos = (q (n.cast (congrArg (· + 1) hlen))).workTapePos) :
    p.space = q.space := by
  obtain ⟨n, p, hp⟩ := p
  obtain ⟨m, q, hq⟩ := q
  dsimp only at hlen
  subst m
  refine Finset.sum_congr rfl fun i _ ↦ congrArg Finset.card (Finset.image_congr fun j _ ↦ ?_)
  exact congrFun (h j) i

/-- A simulation uses the original path's space plus a bound for each additional tape. -/
lemma space_le_of_workTapePos_embedding {k' : ℕ} {State' : Type*} {input' : List Symbol}
    {ntm' : MultiTapeNTM k' Symbol State'} (p : ntm.RunPath input) (q : ntm'.RunPath input')
    (hlen : p.length = q.length) (e : Fin k ↪ Fin k') (b : ℕ)
    (he : ∀ n j, (p n).workTapePos j = (q (n.cast (congrArg (· + 1) hlen))).workTapePos (e j))
    (hrest : ∀ l ∉ Set.range e, q.spaceUsedByTape l ≤ b) :
    q.space ≤ p.space + (k' - k) * b := by
  classical
  obtain ⟨n, p, hp⟩ := p
  obtain ⟨m, q, hq⟩ := q
  dsimp only at hlen
  subst m
  rw [space, space, ← Finset.sum_add_sum_compl (Finset.univ.map e), Finset.sum_map]
  refine add_le_add (Finset.sum_le_sum fun j _ ↦ (congrArg Finset.card
    (Finset.image_congr fun m _ ↦ he m j)).ge) ?_
  refine (Finset.sum_le_card_nsmul _ _ b fun l hl ↦ hrest l (by simpa using hl)).trans ?_
  simp [Finset.card_compl]

/-- Once a path has halted, its visited sets stop growing. -/
lemma visitedByTapeHead_eq_take_of_halted (p : ntm.RunPath input) (n : Fin (p.length + 1))
    (hhalt : (p n).Halted) (i : Fin k) :
    p.visitedByTapeHead i = visitedByTapeHead (p.take n) i := by
  refine Finset.Subset.antisymm (p.visitedByTapeHead_subset fun m ↦ ?_)
    (p.visitedByTapeHead_take_subset n i)
  by_cases h : m ≤ n
  · exact (mem_visitedByTapeHead (p.take n)).mpr ⟨⟨m, by simp; omega⟩, rfl⟩
  · have heq : p m = p n := by
      exact last_eq_of_halted (p.take m) ⟨n, by simp; omega⟩ hhalt
    rw [heq]
    exact mem_visitedByTapeHead_self (p.take n) (Fin.last n) i

/-- Once a path has halted, its space usage stops growing. -/
lemma space_eq_take_of_halted (p : ntm.RunPath input) (n : Fin (p.length + 1))
    (hhalt : (p n).Halted) : p.space = space (p.take n) :=
  Finset.sum_congr rfl fun i _ ↦
    congrArg Finset.card (p.visitedByTapeHead_eq_take_of_halted n hhalt i)

/-- A path that never moves a work-tape head visits one cell per tape. -/
lemma space_le_of_workTapePos_const (p : ntm.RunPath input)
    (h : ∀ n, (p n).workTapePos = p.head.workTapePos) : p.space ≤ k := by
  have hcard : ∀ i ∈ Finset.univ, p.spaceUsedByTape i ≤ 1 :=
    fun i _ ↦ p.spaceUsedByTape_le_one fun n ↦ congrFun (h n) i
  simpa [space] using Finset.sum_le_card_nsmul _ _ 1 hcard

end RunPath

/-- Every non-blank cell lies within its tape's space bound of the origin. -/
lemma ComputationPath.content_natAbs_le_spaceUsedByTape (p : ntm.ComputationPath input)
    {i : Fin k} (z : ℤ) (h : p.last.workTapes i z ≠ none) :
    z.natAbs ≤ RunPath.spaceUsedByTape p.toRunPath i := by
  have hne : p.last.workTapes i z ≠ p.head.workTapes i z := by simpa [p.head_eq, initCfg] using h
  simpa [p.head_eq, initCfg] using RunPath.natAbs_le_spaceUsedByTape_of_mem_visited p.toRunPath
    (RunPath.mem_visitedByTapeHead_of_workTapes_ne p.toRunPath (Fin.last p.length) i z hne)

end MultiTapeNTM

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

/-- A computation with bounded space reaches a step at which every tape's space usage is maximal. -/
lemma exists_spaceUsedByTape_max (cfg : Cfg k Symbol State input) {s : ℕ}
    (hs : ∀ t, (tm.runPath cfg t).space ≤ s) :
    ∃ T, ∀ t i, (tm.runPath cfg t).spaceUsedByTape i ≤ (tm.runPath cfg T).spaceUsedByTape i := by
  have hmono (i : Fin k) : Monotone (fun t ↦ (tm.runPath cfg t).spaceUsedByTape i) := by
    intro t t' ht
    exact (tm.runPath cfg t').spaceUsedByTape_take_le ⟨t, by simp; omega⟩ i
  have h : ∀ i, ∃ Ti, ∀ t,
      (tm.runPath cfg t).spaceUsedByTape i ≤ (tm.runPath cfg Ti).spaceUsedByTape i := by
    intro i
    have hbdd : BddAbove (Set.range (fun t ↦ (tm.runPath cfg t).spaceUsedByTape i)) :=
      ⟨s, by rintro _ ⟨t, rfl⟩; exact ((tm.runPath cfg t).spaceUsedByTape_le_space i).trans (hs t)⟩
    obtain ⟨Ti, hTi⟩ := Nat.sSup_mem
      (Set.range_nonempty (fun t ↦ (tm.runPath cfg t).spaceUsedByTape i)) hbdd
    exact ⟨Ti, fun t ↦ (le_csSup hbdd ⟨t, rfl⟩).trans hTi.ge⟩
  choose T hT using h
  exact ⟨Finset.univ.sup T, fun t i ↦
    (hT i t).trans (hmono i (Finset.le_sup (Finset.mem_univ i)))⟩

end MultiTapeTM

end Turing
