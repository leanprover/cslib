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
# Tape head visitation and space usage

These lemmas describe the cells visited and modified along a run path. Comparing space usage
across different computation paths additionally requires determinism.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}
variable {ntm : MultiTapeNTM k Symbol State}

/-- A step changes a tape only at the position of its head. -/
lemma Step.workTapes_eq_of_ne {c c' : Cfg k Symbol State input} (h : ntm.Step c c')
    (i : Fin k) (z : ℤ) (hz : z ≠ c.workTapePos i) : c'.workTapes i z = c.workTapes i z := by
  unfold Step at h
  split at h
  · simp [h]
  · obtain ⟨a, _, rfl⟩ := h
    rw [Action.apply_workTapes]
    cases ha : (a.workTapes i).1 <;> simp [ha, hz]

/-- A work-tape head moves at most one cell per step. -/
lemma Step.workTapePos_le {c c' : Cfg k Symbol State input} (h : ntm.Step c c') (i : Fin k) :
    |c'.workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold Step at h
  split at h
  · simp [h]
  · obtain ⟨a, _, rfl⟩ := h
    exact workTapePos_apply_le a c i

namespace RunPath

@[simp]
lemma mem_visitedByTapeHead (p : ntm.RunPath input) (i : Fin k) (z : ℤ) :
    z ∈ p.visitedByTapeHead i ↔ ∃ c ∈ p, c.workTapePos i = z := by
  simp [visitedByTapeHead, RelSeries.mem_def]

/-- Every configuration on the path contributes its head position to the visited set. -/
lemma workTapePos_mem_visited {p : ntm.RunPath input} {c : Cfg k Symbol State input}
    (h : c ∈ p) (i : Fin k) : c.workTapePos i ∈ p.visitedByTapeHead i :=
  (mem_visitedByTapeHead p i _).mpr ⟨c, h, rfl⟩

/-- A prefix visits only positions visited by the full path. -/
lemma visitedByTapeHead_take_subset (p : ntm.RunPath input) (n : Fin (p.length + 1))
    (i : Fin k) : visitedByTapeHead (p.take n) i ⊆ p.visitedByTapeHead i := by
  intro z hz
  obtain ⟨c, ⟨j, rfl⟩, rfl⟩ := (mem_visitedByTapeHead _ _ _).mp hz
  have hj : j.val < n.val + 1 := j.isLt
  exact workTapePos_mem_visited (p := p) ⟨⟨j.val, by omega⟩, rfl⟩ i

@[simp]
lemma visitedByTapeHead_snoc (p : ntm.RunPath input) (c : Cfg k Symbol State input)
    (h : ntm.Step p.last c) (i : Fin k) :
    visitedByTapeHead (p.snoc c h) i = p.visitedByTapeHead i ∪ {c.workTapePos i} := by
  ext z
  simp [RelSeries.mem_snoc, or_and_right, exists_or, eq_comm, or_comm]

/-- Every position between the initial and final head positions was visited. -/
lemma uIcc_workTapePos_subset_visitedByTapeHead (p : ntm.RunPath input) (i : Fin k) :
    Finset.uIcc (p.head.workTapePos i) (p.last.workTapePos i) ⊆ p.visitedByTapeHead i := by
  induction p using RelSeries.inductionOn' with
  | singleton c =>
    simp +instances [visitedByTapeHead, RelSeries.singleton, RelSeries.head, RelSeries.last]
  | snoc p c h ih =>
    have hm := abs_le.mp (h.workTapePos_le i)
    simp only [RelSeries.head_snoc, RelSeries.last_snoc, visitedByTapeHead_snoc]
    intro z hz
    simp only [Finset.mem_union, Finset.mem_singleton]
    by_cases he : z = c.workTapePos i
    · exact Or.inr he
    · exact Or.inl (ih (by rw [Finset.mem_uIcc] at hz ⊢; omega))

/-- A changed tape cell was visited along the path. -/
lemma mem_visitedByTapeHead_of_workTapes_ne (p : ntm.RunPath input) (i : Fin k) (z : ℤ)
    (h : p.last.workTapes i z ≠ p.head.workTapes i z) : z ∈ p.visitedByTapeHead i := by
  induction p using RelSeries.inductionOn' with
  | singleton c => exact absurd rfl h
  | snoc p c hs ih =>
    by_cases hz : z = p.last.workTapePos i
    · rw [visitedByTapeHead_snoc]
      exact Finset.mem_union_left _ (hz ▸ workTapePos_mem_visited (RelSeries.last_mem p) i)
    · have hc := hs.workTapes_eq_of_ne i z hz
      have hn : p.last.workTapes i z ≠ p.head.workTapes i z := by
        simpa only [RelSeries.last_snoc, RelSeries.head_snoc, hc] using h
      rw [visitedByTapeHead_snoc]
      exact Finset.mem_union_left _ (ih hn)

/-- A visited position is within the tape's space usage of its initial head position. -/
lemma natAbs_le_spaceUsedByTape_of_mem_visited (p : ntm.RunPath input) {i : Fin k} {z : ℤ}
    (hz : z ∈ p.visitedByTapeHead i) :
    (z - p.head.workTapePos i).natAbs ≤ p.spaceUsedByTape i := by
  obtain ⟨c, ⟨n, rfl⟩, rfl⟩ := (mem_visitedByTapeHead _ _ _).mp hz
  have h := Finset.card_le_card
    ((uIcc_workTapePos_subset_visitedByTapeHead (p.take n) i).trans
      (visitedByTapeHead_take_subset p n i))
  simp only [RelSeries.head_take, RelSeries.last_take, Int.card_uIcc] at h
  change _ ≤ (p.visitedByTapeHead i).card
  omega

/-- One tape visits at most one new cell per step. -/
lemma spaceUsedByTape_le (p : ntm.RunPath input) (i : Fin k) :
    p.spaceUsedByTape i ≤ p.length + 1 :=
  Finset.card_image_le.trans_eq (by simp)

/-- Space is bounded linearly by the number of steps. -/
lemma space_linear (p : ntm.RunPath input) : p.space ≤ k * p.length + k := by
  calc p.space
      ≤ ∑ i, (p.length + 1) := Finset.sum_le_sum fun i _ ↦ spaceUsedByTape_le p i
    _ = k * p.length + k := by simp [Nat.mul_succ]

/-- A set containing every head position contains the visited set. -/
lemma visitedByTapeHead_subset (p : ntm.RunPath input) {i : Fin k} {S : Finset ℤ}
    (h : ∀ c ∈ p, c.workTapePos i ∈ S) : p.visitedByTapeHead i ⊆ S := by
  intro z hz
  obtain ⟨c, hc, rfl⟩ := (mem_visitedByTapeHead _ _ _).mp hz
  exact h c hc

/-- Any set containing the head positions bounds the tape's space usage. -/
lemma spaceUsedByTape_le_card (p : ntm.RunPath input) {i : Fin k} {S : Finset ℤ}
    (h : ∀ c ∈ p, c.workTapePos i ∈ S) : p.spaceUsedByTape i ≤ S.card :=
  Finset.card_le_card (visitedByTapeHead_subset p h)

/-- A head that stays at one position uses at most one cell. -/
lemma spaceUsedByTape_le_one (p : ntm.RunPath input) {i : Fin k}
    (h : ∀ c ∈ p, c.workTapePos i = p.head.workTapePos i) : p.spaceUsedByTape i ≤ 1 := by
  simpa using spaceUsedByTape_le_card p (S := {p.head.workTapePos i})
    fun c hc ↦ by simp [h c hc]

/-- Taking a prefix cannot increase space usage. -/
lemma space_take_le (p : ntm.RunPath input) (n : Fin (p.length + 1)) :
    space (p.take n) ≤ p.space :=
  Finset.sum_le_sum fun i _ ↦ Finset.card_le_card (visitedByTapeHead_take_subset p n i)

/-- Joining paths takes the union of their visited positions. -/
lemma visitedByTapeHead_smash (p q : ntm.RunPath input) (h : p.last = q.head) (i : Fin k) :
    visitedByTapeHead (p.smash q h) i = p.visitedByTapeHead i ∪ q.visitedByTapeHead i := by
  ext z
  simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨n, rfl⟩
    induction n using Fin.addCases (m := p.length) (n := q.length + 1) with
    | left n => exact Or.inl ⟨n.castSucc, by simp [RelSeries.smash]⟩
    | right n => exact Or.inr ⟨n, by simp [RelSeries.smash]⟩
  · rintro (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · exact ⟨n.castLE (by simp), congrArg (fun c ↦ c.workTapePos i) (RelSeries.smash_castLE h n)⟩
    · exact ⟨n.natAdd p.length, by simp [RelSeries.smash]⟩

/-- Joining paths can only overcount the space used by both parts. -/
lemma space_smash_le (p q : ntm.RunPath input) (h : p.last = q.head) :
    space (p.smash q h) ≤ p.space + q.space := by
  simp only [space, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦ by
    change (visitedByTapeHead (p.smash q h) i).card ≤ _
    rw [visitedByTapeHead_smash]
    exact Finset.card_union_le _ _

variable {k' : ℕ} {State' : Type*} {input' : List Symbol}
variable {ntm' : MultiTapeNTM k' Symbol State'}

/-- A simulation preserving head positions preserves space. -/
lemma space_map_eq {ntm' : MultiTapeNTM k Symbol State'} (p : ntm.RunPath input)
    (f : Cfg k Symbol State input → Cfg k Symbol State' input')
    (hf : ∀ {c c'}, ntm.Step c c' → ntm'.Step (f c) (f c'))
    (h : ∀ c ∈ p, (f c).workTapePos = c.workTapePos) : space (p.map ⟨f, hf⟩) = p.space := by
  unfold space spaceUsedByTape visitedByTapeHead
  congr 1
  funext i
  congr 1
  apply Finset.image_congr
  intro n _
  exact congrFun (h (p n) ⟨n, rfl⟩) i

/-- A simulation uses the source tapes' space plus the space of its extra tapes. -/
lemma space_map_le (p : ntm.RunPath input)
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input')
    (hf : ∀ {c c'}, ntm.Step c c' → ntm'.Step (f c) (f c'))
    (e : Fin k ↪ Fin k') (b : ℕ)
    (he : ∀ c ∈ p, ∀ i, (f c).workTapePos (e i) = c.workTapePos i)
    (hrest : ∀ i ∉ Set.range e, spaceUsedByTape (p.map ⟨f, hf⟩) i ≤ b) :
    space (p.map ⟨f, hf⟩) ≤ p.space + (k' - k) * b := by
  classical
  unfold space
  rw [← Finset.sum_add_sum_compl (Finset.univ.map e), Finset.sum_map]
  refine add_le_add (Finset.sum_le_sum fun i _ ↦ ?_) ?_
  · change spaceUsedByTape (p.map ⟨f, hf⟩) (e i) ≤ (p.visitedByTapeHead i).card
    apply spaceUsedByTape_le_card (S := p.visitedByTapeHead i)
    rintro _ ⟨n, rfl⟩
    change (f (p n)).workTapePos (e i) ∈ _
    rw [he (p n) ⟨n, rfl⟩ i]
    exact workTapePos_mem_visited (p := p) ⟨n, rfl⟩ i
  · refine (Finset.sum_le_card_nsmul _ _ b fun i hi ↦ hrest i (by simpa using hi)).trans ?_
    simp [Finset.card_compl]

/-- A path whose heads never move uses at most one cell per tape. -/
lemma space_le_of_workTapePos_const (p : ntm.RunPath input)
    (h : ∀ c ∈ p, c.workTapePos = p.head.workTapePos) : p.space ≤ k := by
  have hb : ∀ i ∈ Finset.univ, p.spaceUsedByTape i ≤ 1 :=
    fun i _ ↦ spaceUsedByTape_le_one p fun c hc ↦ congrFun (h c hc) i
  simpa [space] using Finset.sum_le_card_nsmul _ _ 1 hb

end RunPath

/-- Every non-blank cell at the end of a computation lies within its tape's space bound. -/
lemma ComputationPath.content_natAbs_le_spaceUsedByTape (p : ntm.ComputationPath input)
    (i : Fin k) (z : ℤ) (h : p.last.workTapes i z ≠ none) :
    z.natAbs ≤ RunPath.spaceUsedByTape p.toRunPath i := by
  have hh : p.toRunPath.head.workTapes i z = none := by simp [p.head_eq]
  simpa [p.head_eq] using
    RunPath.natAbs_le_spaceUsedByTape_of_mem_visited p.toRunPath
    (RunPath.mem_visitedByTapeHead_of_workTapes_ne p.toRunPath i z (hh ▸ h))

/-- For a deterministic machine, bounded space is attained by one computation path, whose
per-tape windows contain those of every other computation path. -/
lemma IsDeterministic.exists_spaceUsedByTape_max (hd : ntm.IsDeterministic) {s : ℕ}
    (hs : ntm.RunsInSpace input s) :
    ∃ p : ntm.ComputationPath input, ∀ q : ntm.ComputationPath input,
      RunPath.spaceUsedByTape q.toRunPath ≤ RunPath.spaceUsedByTape p.toRunPath := by
  have hsub (p q : ntm.ComputationPath input) (ht : p.time ≤ q.time) (i : Fin k) :
      RunPath.visitedByTapeHead p.toRunPath i ⊆ RunPath.visitedByTapeHead q.toRunPath i := by
    intro z hz
    obtain ⟨c, ⟨n, rfl⟩, rfl⟩ := (RunPath.mem_visitedByTapeHead _ _ _).mp hz
    have hn : n.val < q.toRunPath.length + 1 := lt_of_lt_of_le n.isLt (Nat.add_le_add_right ht 1)
    have he := hd.apply_eq p.toRunPath q.toRunPath (p.head_eq.trans q.head_eq.symm)
      n ⟨n.val, hn⟩ rfl
    rw [he]
    exact RunPath.workTapePos_mem_visited (p := q.toRunPath) ⟨⟨n.val, hn⟩, rfl⟩ i
  have hb : BddAbove (Set.range (ComputationPath.space (ntm := ntm) (input := input))) :=
    ⟨s, by rintro _ ⟨p, rfl⟩; exact hs p⟩
  have hn : (Set.range (ComputationPath.space (ntm := ntm) (input := input))).Nonempty :=
    ⟨_, ⟨⟨RelSeries.singleton _ (ntm.initCfg input), rfl⟩, rfl⟩⟩
  obtain ⟨p, hp⟩ := Nat.sSup_mem hn hb
  refine ⟨p, fun q i ↦ ?_⟩
  rcases le_total q.time p.time with ht | ht
  · exact Finset.card_le_card (hsub q p ht i)
  · have hle : ∀ j, RunPath.spaceUsedByTape p.toRunPath j ≤ RunPath.spaceUsedByTape q.toRunPath j :=
      fun j ↦ Finset.card_le_card (hsub p q ht j)
    have hmax : q.space ≤ p.space := hp ▸ le_csSup hb (Set.mem_range_self q)
    have he : ∑ j, RunPath.spaceUsedByTape p.toRunPath j =
        ∑ j, RunPath.spaceUsedByTape q.toRunPath j :=
      le_antisymm (Finset.sum_le_sum fun j _ ↦ hle j) hmax
    exact ((Finset.sum_eq_sum_iff_of_le (fun j _ ↦ hle j)).mp he i (Finset.mem_univ i)).ge

end Turing.MultiTapeNTM
