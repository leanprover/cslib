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

namespace Turing.MultiTapeNTM.RunPath

variable {k k' : ℕ} {State State' Symbol : Type*} {input input' : List Symbol}
variable {ntm : MultiTapeNTM k Symbol State} {ntm' : MultiTapeNTM k' Symbol State'}

/-- A set containing every position of a head along a path bounds the space used by its tape. -/
lemma spaceUsedByTape_le_card (p : ntm.RunPath input) {i : Fin k} {S : Finset ℤ}
    (h : ∀ c ∈ p, c.workTapePos i ∈ S) : p.spaceUsedByTape i ≤ S.card :=
  Finset.card_le_card (Finset.image_subset_iff.mpr fun n _ => h (p n) ⟨n, rfl⟩)

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

end Turing.MultiTapeNTM.RunPath

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

/-- The total space used is monotone in the number of steps. -/
lemma spaceUsed_mono (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) :
    Monotone (tm.spaceUsed cfg ·) := by
  intro t t' h
  exact Finset.sum_le_sum (fun i _ => spaceUsedByTape_mono tm cfg i h)

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


/-- Every position the head takes up to step `t` lies in `S`, so the whole visited set does. This
is `Finset.image_subset_iff` for the visited set, and the workhorse behind the space bounds
below. -/
lemma visitedByTapeHead_subset (cfg : Cfg k Symbol State input) {t : ℕ} {i : Fin k} {S : Finset ℤ}
    (h : ∀ m ≤ t, (tm.runFrom cfg m).workTapePos i ∈ S) :
    tm.visitedByTapeHead cfg t i ⊆ S :=
  Finset.image_subset_iff.mpr fun m _ => h m (Nat.lt_succ_iff.mp m.isLt)

/-- A set containing every position of a head bounds the space used by its tape. -/
lemma spaceUsedByTape_le_card (cfg : Cfg k Symbol State input) {t : ℕ} {i : Fin k} {S : Finset ℤ}
    (h : ∀ m ≤ t, (tm.runFrom cfg m).workTapePos i ∈ S) :
    tm.spaceUsedByTape cfg t i ≤ S.card :=
  (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).spaceUsedByTape_le_card
    fun _ ⟨m, hm⟩ => hm ▸ h m (Nat.lt_succ_iff.mp m.isLt)

/-- A head that never moves uses a single cell. -/
lemma spaceUsedByTape_le_one (cfg : Cfg k Symbol State input) {t : ℕ} {i : Fin k}
    (h : ∀ m ≤ t, (tm.runFrom cfg m).workTapePos i = cfg.workTapePos i) :
    tm.spaceUsedByTape cfg t i ≤ 1 := by
  simpa using tm.spaceUsedByTape_le_card cfg (S := {cfg.workTapePos i})
    fun m hm => by simp [h m hm]

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
        by simp only [runFrom, ← Function.iterate_add_apply,
          Nat.sub_add_cancel (by omega : a ≤ r)]⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨r, by omega, rfl⟩
    · exact ⟨a + r, by omega,
        by simp only [runFrom, ← Function.iterate_add_apply, Nat.add_comm]⟩

/-- Splitting a run into two phases can only overcount the cells it visits, since the two phases
may revisit each other's cells. -/
lemma spaceUsed_add_le (cfg : Cfg k Symbol State input) (a b : ℕ) :
    tm.spaceUsed cfg (a + b) ≤ tm.spaceUsed cfg a + tm.spaceUsed (tm.runFrom cfg a) b := by
  rw [spaceUsed, spaceUsed, spaceUsed, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [spaceUsedByTape, visitedByTapeHead_add]
  exact Finset.card_union_le _ _

/-- Space usage only depends on where the work-tape heads are at each step, so two runs whose head
positions agree use the same space. This is what lets a machine be replaced by a simulation of
it. -/
lemma spaceUsed_eq_of_workTapePos {State' : Type*} {input' : List Symbol}
    {tm' : MultiTapeTM k Symbol State'} (cfg : Cfg k Symbol State input)
    (cfg' : Cfg k Symbol State' input') (t : ℕ)
    (h : ∀ m ≤ t, (tm.runFrom cfg m).workTapePos = (tm'.runFrom cfg' m).workTapePos) :
    tm.spaceUsed cfg t = tm'.spaceUsed cfg' t := by
  refine Finset.sum_congr rfl fun i _ => congrArg Finset.card (Finset.image_congr fun m _ => ?_)
  exact congrFun (h m (Nat.lt_succ_iff.mp m.isLt)) i

/-- After the machine has halted the heads no longer move, so the visited set stops growing. -/
lemma visitedByTapeHead_eq_of_halt (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) (i : Fin k) :
    tm.visitedByTapeHead cfg t i = tm.visitedByTapeHead cfg τ i := by
  refine Finset.Subset.antisymm (visitedByTapeHead_subset cfg fun m hm => ?_)
    (tm.visitedByTapeHead_mono cfg i hle)
  rcases Nat.le_total m τ with h | h
  · exact mem_visitedByTapeHead.mpr ⟨m, by omega, rfl⟩
  · rw [runFrom_eq_of_halt tm cfg h hhalt]
    exact tm.mem_visitedByTapeHead_self cfg τ i

/-- After the machine has halted the heads no longer move, so the space usage stops growing. -/
lemma spaceUsed_eq_of_halt (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    tm.spaceUsed cfg t = tm.spaceUsed cfg τ :=
  Finset.sum_congr rfl fun i _ =>
    congrArg Finset.card (tm.visitedByTapeHead_eq_of_halt cfg hle hhalt i)

/-- A run that never moves a work-tape head visits one cell per tape. -/
lemma spaceUsed_le_of_workTapePos_const (cfg : Cfg k Symbol State input) (u : ℕ)
    (h : ∀ m ≤ u, (tm.runFrom cfg m).workTapePos = cfg.workTapePos) :
    tm.spaceUsed cfg u ≤ k := by
  have hcard : ∀ i ∈ Finset.univ, tm.spaceUsedByTape cfg u i ≤ 1 :=
    fun i _ => tm.spaceUsedByTape_le_one cfg fun m hm => congrFun (h m hm) i
  simpa [spaceUsed] using Finset.sum_le_card_nsmul _ _ 1 hcard

/-! ### Output already present -/

section PrependOutput

/-- A machine never reads its output tape, so a word already present there is simply carried
along by a step. -/
lemma step_prependOutput (cfg : Cfg k Symbol State input) (pre : List Symbol) :
    tm.step (cfg.prependOutput pre) = (tm.step cfg).prependOutput pre := by
  cases hq : cfg.state with
  | none => simp [step_of_halt, hq, Cfg.prependOutput]
  | some q =>
    rw [step_of_state (cfg := cfg.prependOutput pre) (by simpa [Cfg.prependOutput] using hq),
      step_of_state hq]
    exact Cfg.ext rfl rfl rfl rfl (by simp [Cfg.prependOutput, Action.apply]; rfl)

/-- **A word already on the output tape is inert.** The run is the run without it, with the word
prepended to whatever the machine emits. -/
lemma runFrom_prependOutput (cfg : Cfg k Symbol State input) (pre : List Symbol) (n : ℕ) :
    tm.runFrom (cfg.prependOutput pre) n = (tm.runFrom cfg n).prependOutput pre :=
  (Function.Semiconj.iterate_right (f := (Cfg.prependOutput · pre))
    (fun c => (step_prependOutput c pre).symm) n cfg).symm

/-- A word already on the output tape does not affect the space used. -/
lemma spaceUsed_prependOutput (cfg : Cfg k Symbol State input) (pre : List Symbol) (n : ℕ) :
    tm.spaceUsed (cfg.prependOutput pre) n = tm.spaceUsed cfg n :=
  spaceUsed_eq_of_workTapePos _ _ n fun m _ => by rw [runFrom_prependOutput]; rfl

end PrependOutput

end Turing.MultiTapeTM
