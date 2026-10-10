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

This file collects lemmas about the cells visited by the work-tape heads along a run path
(`MultiTapeNTM.RunPath.visitedByTapeHead`), the resulting space measures, and how the head
positions bound the cells that a path changes.

`MultiTapeNTM.RunPath.InWindow` says that every head of a run path stays within the window
`[-s, s]`, which bounds the space of the path.

`MultiTapeNTM.RunPath.space_map_le` bounds the space of a run path mapped by `RunPath.map` through
the head positions of the original path.
-/

@[expose] public section

namespace Turing

/-- The window `[-s, s]` of tape positions allotted to a tape that uses `s` cells. -/
@[scoped grind =]
def window (s : ℕ) : Finset ℤ := Finset.Icc (-(s : ℤ)) s

@[scoped grind =]
lemma mem_window {s : ℕ} {z : ℤ} : z ∈ window s ↔ z.natAbs ≤ s := by
  grind

@[simp]
lemma card_window (s : ℕ) : (window s).card = 2 * s + 1 := by
  grind [Int.card_Icc]

end Turing

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

/-- A set containing every position of a head along a path bounds the space used by its tape. -/
lemma spaceUsedByTape_le_card (p : ntm.RunPath input) {i : Fin k} {S : Finset ℤ}
    (h : ∀ c ∈ p, c.workTapePos i ∈ S) : p.spaceUsedByTape i ≤ S.card :=
  Finset.card_le_card (Finset.image_subset_iff.mpr fun n _ => h (p n) ⟨n, rfl⟩)

/-- Sets containing every position of the heads along a path bound its space by their total
size. -/
lemma space_le_sum_card (p : ntm.RunPath input) {S : Fin k → Finset ℤ}
    (h : ∀ c ∈ p, ∀ i, c.workTapePos i ∈ S i) : p.space ≤ ∑ i, (S i).card :=
  Finset.sum_le_sum fun i _ => p.spaceUsedByTape_le_card fun c hc => h c hc i

/-- A head visits at most one cell per configuration of the path. -/
lemma spaceUsedByTape_le (p : ntm.RunPath input) (i : Fin k) : p.spaceUsedByTape i ≤ p.time + 1 :=
  Finset.card_image_le.trans_eq (by simp [time])

/-- The space of a path is bounded linearly by its number of steps. -/
lemma space_linear (p : ntm.RunPath input) : p.space ≤ k * p.time + k :=
  (Finset.sum_le_sum fun i _ => p.spaceUsedByTape_le i).trans_eq (by simp [Nat.mul_succ])

/-- A path visits exactly the head positions of its configurations. -/
@[simp]
lemma mem_visitedByTapeHead (p : ntm.RunPath input) {i : Fin k} {z : ℤ} :
    z ∈ p.visitedByTapeHead i ↔ ∃ c ∈ p, c.workTapePos i = z := by
  simp [visitedByTapeHead, RelSeries.mem_def]

/-- A path whose configurations all lie on another path visits no more cells. -/
lemma space_le_of_subset {p q : ntm.RunPath input} (h : ∀ c ∈ q, c ∈ p) : q.space ≤ p.space :=
  q.space_le_sum_card fun c hc _ => p.mem_visitedByTapeHead.mpr ⟨c, h c hc, rfl⟩

/-- Extending a path by a configuration visits its head positions as well. -/
lemma visitedByTapeHead_snoc (p : ntm.RunPath input) (c : Cfg k Symbol State input)
    (h : ntm.Step p.last c) (i : Fin k) :
    visitedByTapeHead (p.snoc c h) i = insert (c.workTapePos i) (p.visitedByTapeHead i) := by
  ext z
  simp [RelSeries.mem_snoc, or_and_right, exists_or, eq_comm, or_comm]

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

/-! ### Windows -/

/-- Every head stays within the window `[-s, s]` along the path. -/
def InWindow (p : ntm.RunPath input) (s : ℕ) : Prop :=
  ∀ c ∈ p, ∀ i, c.workTapePos i ∈ window s

/-- A path whose heads stay within `[-s, s]` visits at most `2 * s + 1` cells on each tape. -/
lemma InWindow.space_le {p : ntm.RunPath input} {s : ℕ} (h : p.InWindow s) :
    p.space ≤ k * (2 * s + 1) := by
  simpa using p.space_le_sum_card h

/-- Joining two paths whose heads stay within `[-s, s]` keeps them there. -/
lemma InWindow.smash {p q : ntm.RunPath input} {h : p.last = q.head} {s : ℕ}
    (hp : p.InWindow s) (hq : q.InWindow s) : InWindow (p.smash q h) s :=
  fun _ hc => (RelSeries.mem_or_mem_of_mem_smash hc).elim (hp _) (hq _)

/-- A path that starts with every head at cell `0` and visits at most `s` cells keeps its heads
within `[-s, s]`. -/
lemma inWindow_of_space_le {p : ntm.RunPath input} {s : ℕ} (h0 : ∀ i, p.head.workTapePos i = 0)
    (hs : p.space ≤ s) : p.InWindow s := fun c hc i => by
  have hz := p.natAbs_le_spaceUsedByTape_of_mem_visited
    ((p.mem_visitedByTapeHead (i := i)).mpr ⟨c, hc, rfl⟩)
  rw [h0, sub_zero] at hz
  exact mem_window.mpr <| hz.trans <|
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs

/-! ### Mapped paths -/

/-- If the head of tape `i'` of a mapped path follows the head of tape `i` of the source path, the
two tapes visit the same cells. -/
lemma visitedByTapeHead_map (p : ntm.RunPath input)
    (f : (ntm.stepRel input).Hom (ntm'.stepRel input')) {i : Fin k} {i' : Fin k'}
    (h : ∀ c ∈ p, (f c).workTapePos i' = c.workTapePos i) :
    (p.map f).visitedByTapeHead i' = p.visitedByTapeHead i :=
  Finset.image_congr fun n _ => h (p n) ⟨n, rfl⟩

/-- **Space of a mapped path.** If tape `e j` of the mapped path follows tape `j` of `p`, and every
other tape `l` stays in `window l`, the mapped path uses the space of `p` plus the cells of
`window l` for every other tape `l`. -/
lemma space_map_le (p : ntm.RunPath input) (f : (ntm.stepRel input).Hom (ntm'.stepRel input'))
    (e : Fin k ↪ Fin k') (window : Fin k' → Finset ℤ)
    (hfollow : ∀ c ∈ p, ∀ j, (f c).workTapePos (e j) = c.workTapePos j)
    (hwindow : ∀ c ∈ p, ∀ l ∉ Set.range e, (f c).workTapePos l ∈ window l) :
    (p.map f).space ≤ p.space + ∑ l ∈ (Finset.univ.map e)ᶜ, (window l).card := by
  rw [space, space, ← Finset.sum_add_sum_compl (Finset.univ.map e), Finset.sum_map]
  refine add_le_add (Finset.sum_le_sum fun j _ => (congrArg Finset.card
    (p.visitedByTapeHead_map f fun c hc => hfollow c hc j)).le) (Finset.sum_le_sum fun l hl => ?_)
  exact (p.map f).spaceUsedByTape_le_card fun _ ⟨n, hn⟩ =>
    hn ▸ hwindow (p n) ⟨n, rfl⟩ l (by simpa using hl)

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
