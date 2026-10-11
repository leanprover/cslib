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
(`MultiTapeNTM.RunPath.visitedByTapeHead`) and the resulting space-usage measures
(`MultiTapeNTM.RunPath.spaceUsedByTape`, `MultiTapeNTM.RunPath.space`) and how the tape head
positions influence the cells that are modified on a tape.

`MultiTapeTM.exists_spaceUsedByTape_max` shows that a deterministic computation
whose space usage is bounded attains its per-tape space usage on a single path. This makes a bound
on every path from a starting configuration usable as a bound for the whole run.

-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

namespace MultiTapeNTM

variable {ntm : MultiTapeNTM k Symbol State}

/-- If the work tape head is not at position `z`, then the tape does not change there. -/
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

/-- A machine never reads its output tape, so a word already present there is simply carried
along by a step. -/
lemma Step.prependOutput {c c' : Cfg k Symbol State input} (h : ntm.Step c c')
    (pre : List Symbol) : ntm.Step (c.prependOutput pre) (c'.prependOutput pre) := by
  cases hq : c.state with
  | none =>
    obtain rfl := (step_of_halt hq).mp h
    exact (step_of_halt (c := c'.prependOutput pre) hq).mpr rfl
  | some q =>
    obtain ⟨a, ha, rfl⟩ := (step_of_state hq).mp h
    refine (step_of_state (c := c.prependOutput pre) hq).mpr ⟨a, ha, ?_⟩
    exact Cfg.ext rfl rfl rfl rfl (by simp [Cfg.prependOutput, Action.apply])

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

/-- Starting from the first configuration of a path, every position between the initial head
position of tape `i` and the one at the end of the path is part of the visited set. -/
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

/-- If a work tape cell is changed along a path, it must have been visited by the tape head. -/
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

/-- Every position visited by the head of tape `i` lies within `spaceUsedByTape … i` of the
head's starting position. -/
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

/-- The number of cells visited by a single work-tape head grows by at most one each step. -/
lemma spaceUsedByTape_le (p : ntm.RunPath input) (i : Fin k) :
    p.spaceUsedByTape i ≤ p.length + 1 :=
  Finset.card_image_le.trans_eq (by simp)

/-- The space used by a computation is bounded linearly by the number of steps. -/
lemma space_linear (p : ntm.RunPath input) : p.space ≤ k * p.length + k := by
  calc p.space
      ≤ ∑ i, (p.length + 1) := Finset.sum_le_sum fun i _ ↦ spaceUsedByTape_le p i
    _ = k * p.length + k := by simp [Nat.mul_succ]

/-- Every position the head takes along the path lies in `S`, so the whole visited set does. This
is `Finset.image_subset_iff` for the visited set, and the workhorse behind the space bounds
below. -/
lemma visitedByTapeHead_subset (p : ntm.RunPath input) {i : Fin k} {S : Finset ℤ}
    (h : ∀ c ∈ p, c.workTapePos i ∈ S) : p.visitedByTapeHead i ⊆ S := by
  intro z hz
  obtain ⟨c, hc, rfl⟩ := (mem_visitedByTapeHead _ _ _).mp hz
  exact h c hc

/-- A set containing every position of a head bounds the space used by its tape. -/
lemma spaceUsedByTape_le_card (p : ntm.RunPath input) {i : Fin k} {S : Finset ℤ}
    (h : ∀ c ∈ p, c.workTapePos i ∈ S) : p.spaceUsedByTape i ≤ S.card :=
  Finset.card_le_card (visitedByTapeHead_subset p h)

/-- A head that never moves uses a single cell. -/
lemma spaceUsedByTape_le_one (p : ntm.RunPath input) {i : Fin k}
    (h : ∀ c ∈ p, c.workTapePos i = p.head.workTapePos i) : p.spaceUsedByTape i ≤ 1 := by
  simpa using spaceUsedByTape_le_card p (S := {p.head.workTapePos i})
    fun c hc ↦ by simp [h c hc]

/-- A prefix uses no more space on a single tape than the whole path. -/
lemma spaceUsedByTape_take_le (p : ntm.RunPath input) (n : Fin (p.length + 1)) (i : Fin k) :
    spaceUsedByTape (p.take n) i ≤ p.spaceUsedByTape i :=
  Finset.card_le_card (p.visitedByTapeHead_take_subset n i)

/-- Taking a prefix cannot increase space usage. -/
lemma space_take_le (p : ntm.RunPath input) (n : Fin (p.length + 1)) :
    space (p.take n) ≤ p.space :=
  Finset.sum_le_sum fun i _ ↦ p.spaceUsedByTape_take_le n i

/-- The cells a joined path visits are the ones visited by its two parts. -/
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

/-- Splitting a path into two phases can only overcount the cells it visits, since the two phases
may revisit each other's cells. -/
lemma space_smash_le (p q : ntm.RunPath input) (h : p.last = q.head) :
    space (p.smash q h) ≤ p.space + q.space := by
  simp only [space, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦ by
    change (visitedByTapeHead (p.smash q h) i).card ≤ _
    rw [visitedByTapeHead_smash]
    exact Finset.card_union_le _ _

/-- Space usage only depends on where the work-tape heads are at each step, so two paths whose head
positions agree use the same space. This is what lets a machine be replaced by a simulation of
it. -/
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

/-- **Space of a simulation.** If the heads of `q` on the tapes `e j` follow the heads of `p` on
the tapes `j`, and each remaining tape of `q` visits at most `b` cells, then `q` uses the space
of `p` plus at most `b` cells per remaining tape. -/
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

variable {k' : ℕ} {State' : Type*} {input' : List Symbol}
variable {ntm' : MultiTapeNTM k' Symbol State'}

/-- A simulation preserving head positions preserves space. -/
lemma space_map_eq {ntm' : MultiTapeNTM k Symbol State'} (p : ntm.RunPath input)
    (f : RelHom (ntm.Step (input := input)) (ntm'.Step (input := input')))
    (h : ∀ c ∈ p, (f c).workTapePos = c.workTapePos) : space (p.map f) = p.space := by
  apply space_eq_of_workTapePos (p.map f) p rfl
  intro n
  exact h (p n) ⟨n, rfl⟩

/-- A simulation uses the source tapes' space plus the space of its extra tapes. -/
lemma space_map_le (p : ntm.RunPath input)
    (f : RelHom (ntm.Step (input := input)) (ntm'.Step (input := input')))
    (e : Fin k ↪ Fin k') (b : ℕ)
    (he : ∀ c ∈ p, ∀ i, (f c).workTapePos (e i) = c.workTapePos i)
    (hrest : ∀ i ∉ Set.range e, spaceUsedByTape (p.map f) i ≤ b) :
    space (p.map f) ≤ p.space + (k' - k) * b :=
  space_le_of_workTapePos_embedding p (p.map f) rfl e b
    (fun n j ↦ (he (p n) ⟨n, rfl⟩ j).symm) hrest

/-- After the machine has halted the heads no longer move, so the visited set stops growing. -/
lemma visitedByTapeHead_eq_take_of_halted (p : ntm.RunPath input) (n : Fin (p.length + 1))
    (hhalt : (p n).Halted) (i : Fin k) :
    p.visitedByTapeHead i = visitedByTapeHead (p.take n) i := by
  refine Finset.Subset.antisymm (p.visitedByTapeHead_subset fun c hc ↦ ?_)
    (p.visitedByTapeHead_take_subset n i)
  obtain ⟨m, rfl⟩ := hc
  by_cases h : m ≤ n
  · exact workTapePos_mem_visited (p := p.take n) ⟨⟨m, by simp; omega⟩, rfl⟩ i
  · have heq : p m = p n :=
      last_eq_of_halted (p.take m) ⟨n, by simp; omega⟩ hhalt
    rw [heq]
    exact workTapePos_mem_visited (p := p.take n) (RelSeries.last_mem _) i

/-- After the machine has halted the heads no longer move, so the space usage stops growing. -/
lemma space_eq_take_of_halted (p : ntm.RunPath input) (n : Fin (p.length + 1))
    (hhalt : (p n).Halted) : p.space = space (p.take n) :=
  Finset.sum_congr rfl fun i _ ↦
    congrArg Finset.card (p.visitedByTapeHead_eq_take_of_halted n hhalt i)

/-- A path that never moves a work-tape head visits one cell per tape. -/
lemma space_le_of_workTapePos_const (p : ntm.RunPath input)
    (h : ∀ c ∈ p, c.workTapePos = p.head.workTapePos) : p.space ≤ k := by
  have hb : ∀ i ∈ Finset.univ, p.spaceUsedByTape i ≤ 1 :=
    fun i _ ↦ spaceUsedByTape_le_one p fun c hc ↦ congrFun (h c hc) i
  simpa [space] using Finset.sum_le_card_nsmul _ _ 1 hb

/-! ### Output already present -/

/-- **A word already on the output tape is inert.** The path is the path without it, with the word
prepended to whatever the machine emits. -/
def prependOutput (p : ntm.RunPath input) (pre : List Symbol) : ntm.RunPath input :=
  p.map ⟨(·.prependOutput pre), fun h ↦ h.prependOutput pre⟩

/-- A word already on the output tape does not affect the space used. -/
@[simp]
lemma space_prependOutput (p : ntm.RunPath input) (pre : List Symbol) :
    (p.prependOutput pre).space = p.space :=
  p.space_map_eq _ (fun _ _ ↦ rfl)

end RunPath

/-- Every non-blank cell on work tape `i` at the end of a computation path lies within
`spaceUsedByTape … i` of the origin. -/
lemma ComputationPath.content_natAbs_le_spaceUsedByTape (p : ntm.ComputationPath input)
    (i : Fin k) (z : ℤ) (h : p.last.workTapes i z ≠ none) :
    z.natAbs ≤ RunPath.spaceUsedByTape p.toRunPath i := by
  have hh : p.toRunPath.head.workTapes i z = none := by simp [p.head_eq]
  simpa [p.head_eq] using
    RunPath.natAbs_le_spaceUsedByTape_of_mem_visited p.toRunPath
    (RunPath.mem_visitedByTapeHead_of_workTapes_ne p.toRunPath i z (hh ▸ h))

end MultiTapeNTM

namespace MultiTapeTM

open MultiTapeNTM

/-- A machine never reads its output tape, so a word already present there is simply carried
along by a step. -/
lemma step_prependOutput {tm : MultiTapeTM k Symbol State}
    (cfg : Cfg k Symbol State input) (pre : List Symbol) :
    tm.step (cfg.prependOutput pre) = (tm.step cfg).prependOutput pre :=
  step_iff.mp ((step_iff.mpr rfl).prependOutput pre)

/-- **A word already on the output tape is inert.** The run is the run without it, with the word
prepended to whatever the machine emits. -/
lemma runFrom_prependOutput {tm : MultiTapeTM k Symbol State}
    (cfg : Cfg k Symbol State input) (pre : List Symbol) (n : ℕ) :
    tm.runFrom (cfg.prependOutput pre) n = (tm.runFrom cfg n).prependOutput pre :=
  (Function.Semiconj.iterate_right (f := (Cfg.prependOutput · pre))
    (fun c ↦ (step_prependOutput c pre).symm) n cfg).symm

/-- A deterministic computation whose total space usage stays below a bound has a path at which
*every* tape's space usage is maximal. This turns a bound on every path from an arbitrary starting
configuration into common per-tape windows for the whole run. -/
lemma exists_spaceUsedByTape_max (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {s : ℕ}
    (hs : ∀ p : tm.RunPath input, p.head = cfg → p.space ≤ s) :
    ∃ p : tm.RunPath input, p.head = cfg ∧ ∀ q : tm.RunPath input,
      q.head = cfg → q.spaceUsedByTape ≤ p.spaceUsedByTape := by
  let paths := {p : tm.RunPath input // p.head = cfg}
  have hsub (p q : paths) (ht : p.val.length ≤ q.val.length) (i : Fin k) :
      p.val.visitedByTapeHead i ⊆ q.val.visitedByTapeHead i := by
    have he (n : Fin (p.val.length + 1)) :
        p.val n = q.val (n.castLE (Nat.add_le_add_right ht 1)) := by
      induction n using Fin.induction with
      | zero => exact p.property.trans q.property.symm
      | succ n ih =>
        have hp := p.val.step n
        rw [ih] at hp
        exact tm.deterministic.step_rightUnique hp (q.val.step (n.castLE ht))
    intro z hz
    obtain ⟨c, ⟨n, rfl⟩, rfl⟩ := (RunPath.mem_visitedByTapeHead _ _ _).mp hz
    rw [he n]
    exact RunPath.workTapePos_mem_visited (p := q.val) ⟨_, rfl⟩ i
  have hb : BddAbove (Set.range fun p : paths ↦ p.val.space) :=
    ⟨s, by rintro _ ⟨p, rfl⟩; exact hs p.val p.property⟩
  have hn : (Set.range fun p : paths ↦ p.val.space).Nonempty :=
    ⟨_, ⟨⟨RelSeries.singleton _ cfg, rfl⟩, rfl⟩⟩
  obtain ⟨p, hp⟩ := Nat.sSup_mem hn hb
  change p.val.space = _ at hp
  refine ⟨p.val, p.property, fun q hq i ↦ ?_⟩
  rcases le_total q.length p.val.length with ht | ht
  · exact Finset.card_le_card (hsub ⟨q, hq⟩ p ht i)
  · have hle : ∀ j, p.val.spaceUsedByTape j ≤ q.spaceUsedByTape j :=
      fun j ↦ Finset.card_le_card (hsub p ⟨q, hq⟩ ht j)
    have hmax : q.space ≤ p.val.space := by
      rw [hp]
      exact le_csSup hb ⟨⟨q, hq⟩, rfl⟩
    have he : ∑ j, p.val.spaceUsedByTape j = ∑ j, q.spaceUsedByTape j :=
      le_antisymm (Finset.sum_le_sum fun j _ ↦ hle j) hmax
    exact ((Finset.sum_eq_sum_iff_of_le (fun j _ ↦ hle j)).mp he i (Finset.mem_univ i)).ge

end MultiTapeTM

end Turing
