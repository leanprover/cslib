/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Aviv Bar Natan
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic
public import Mathlib.Data.Int.Interval

/-!
# Tape head visitation and space-usage lemmas

Work tape heads move by at most one cell per step, and a cell can change only when visited.
The `RunPath` lemmas relate visited positions and changed cells to the space used along a path.
Space depends on the configurations of a chosen path. Inclusion of configuration lists gives
monotonicity; splitting a path gives subadditivity; repeating its halted endpoint preserves space.
These facts also apply to paths of deterministic machines.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}
variable {ntm : MultiTapeNTM k Symbol State} {start : Cfg k Symbol State input}

/-- A work tape head moves by at most one cell in a step. -/
lemma Step.workTapePos_le {c c' : Cfg k Symbol State input} (h : ntm.Step c c') (i : Fin k) :
    |c'.workTapePos i - c.workTapePos i| ≤ 1 := by
  cases hs : c.state with
  | none => obtain rfl := (step_of_halt hs).mp h; simp
  | some q =>
    obtain ⟨action, _, rfl⟩ := (show ∃ action, ntm.Tr q c.inputSymbol c.workTapeSymbols action ∧
      c' = action.apply c from by simpa [Step, hs] using h)
    exact workTapePos_apply_le action c i

/-- A step preserves every work tape cell away from its head. -/
lemma Step.workTapes_eq_of_ne {c c' : Cfg k Symbol State input} (h : ntm.Step c c')
    (i : Fin k) (z : ℤ) (hz : z ≠ c.workTapePos i) : c'.workTapes i z = c.workTapes i z := by
  cases hs : c.state with
  | none => obtain rfl := (step_of_halt hs).mp h; rfl
  | some q =>
    obtain ⟨action, _, rfl⟩ := (show ∃ action, ntm.Tr q c.inputSymbol c.workTapeSymbols action ∧
      c' = action.apply c from by simpa [Step, hs] using h)
    exact action.apply_workTapes_eq_of_ne c i z hz

namespace RunPath

/-- Membership in the visited set is witnessed by a configuration on the path. -/
lemma mem_visited (p : ntm.RunPath start) {i : Fin k} {z : ℤ} :
    z ∈ p.visited i ↔ ∃ n, ∃ hn : n < p.cfgs.length, p.cfgs[n].workTapePos i = z := by
  simp only [visited, visitedOfCfgs, List.mem_toFinset, List.mem_iff_getElem]
  grind

/-- Every final head position belongs to the visited set. -/
lemma last_workTapePos_mem_visited (p : ntm.RunPath start) (i : Fin k) :
    p.last.workTapePos i ∈ p.visited i :=
  p.mem_visited.mpr ⟨p.time, by rw [p.length_eq_time_add_one]; omega, by simp⟩

/-- Every position between the starting head and any later head position is visited. -/
lemma uIcc_workTapePos_getElem_subset_visited (p : ntm.RunPath start)
    (i : Fin k) (n : ℕ) (h : n < p.cfgs.length) :
    Finset.uIcc (start.workTapePos i) (p.cfgs[n].workTapePos i) ⊆ p.visited i := by
  induction n with
  | zero => simpa using (p.mem_visited (i := i)).mpr ⟨0, h, rfl⟩
  | succ n ih =>
    have hprev := ih (by omega)
    have hstep := (p.step_getElem n h).workTapePos_le i
    have hself : p.cfgs[n + 1].workTapePos i ∈ p.visited i :=
      p.mem_visited.mpr ⟨n + 1, h, rfl⟩
    intro z hz
    grind [Finset.mem_uIcc]

/-- Any cell whose final contents differ from its initial contents has been visited. -/
lemma mem_visited_of_workTapes_ne (p : ntm.RunPath start) (i : Fin k) (z : ℤ)
    (h : p.last.workTapes i z ≠ start.workTapes i z) : z ∈ p.visited i := by
  have visited (n : ℕ) (hn : n < p.cfgs.length)
      (h : p.cfgs[n].workTapes i z ≠ start.workTapes i z) : z ∈ p.visited i := by
    induction n with
    | zero => simp at h
    | succ n ih =>
      by_cases hz : z = p.cfgs[n].workTapePos i
      · exact p.mem_visited.mpr ⟨n, by omega, hz.symm⟩
      · rw [(p.step_getElem n hn).workTapes_eq_of_ne i z hz] at h
        exact ih (by omega) h
  exact visited p.time (by rw [p.length_eq_time_add_one]; omega) (by simpa using h)

/-- The displacement of a visited cell is bounded by the tape's space usage. -/
lemma natAbs_le_spaceByTape_of_mem_visited (p : ntm.RunPath start)
    (i : Fin k) {z : ℤ} (hz : z ∈ p.visited i) :
    (z - start.workTapePos i).natAbs ≤ p.spaceByTape i := by
  obtain ⟨n, hn, rfl⟩ := p.mem_visited.mp hz
  have h := Finset.card_le_card (p.uIcc_workTapePos_getElem_subset_visited i n hn)
  rw [Int.card_uIcc] at h
  exact (Nat.le_succ _).trans h

/-- Each tape visits at most one additional cell per step. -/
lemma spaceByTape_le (p : ntm.RunPath start) (i : Fin k) :
    p.spaceByTape i ≤ p.time + 1 := by
  simpa only [spaceByTape, visited, ← p.length_eq_time_add_one] using
    card_visitedOfCfgs_le p.cfgs i

/-- Total space is at most the number of configurations times the number of tapes. -/
lemma space_le (p : ntm.RunPath start) : p.space ≤ k * p.time + k := by
  simpa only [space, p.length_eq_time_add_one, Nat.mul_succ] using spaceUsedOfCfgs_le p.cfgs

/-- A path of a zero-work-tape machine uses no work space. -/
@[simp]
lemma space_zero_tapes (p : ntm.RunPath start) (h : k = 0) : p.space = 0 := by
  subst k
  simp [space, spaceUsedOfCfgs]

/-- Including configurations includes their visited positions. -/
lemma visited_mono {start' : Cfg k Symbol State input}
    (p : ntm.RunPath start) (q : ntm.RunPath start') (h : p.cfgs ⊆ q.cfgs) (i : Fin k) :
    p.visited i ⊆ q.visited i := visitedOfCfgs_mono h i

/-- Including configurations cannot decrease the space used on any tape. -/
lemma spaceByTape_mono {start' : Cfg k Symbol State input}
    (p : ntm.RunPath start) (q : ntm.RunPath start') (h : p.cfgs ⊆ q.cfgs) (i : Fin k) :
    p.spaceByTape i ≤ q.spaceByTape i := Finset.card_le_card (p.visited_mono q h i)

/-- Including configurations cannot decrease total space. -/
lemma space_mono {start' : Cfg k Symbol State input}
    (p : ntm.RunPath start) (q : ntm.RunPath start') (h : p.cfgs ⊆ q.cfgs) :
    p.space ≤ q.space := spaceUsedOfCfgs_mono h

/-- Every nonblank cell of a computation lies within its tape's space bound of the origin. -/
lemma content_natAbs_le_spaceByTape (p : ntm.ComputationPath input) (i : Fin k) (z : ℤ)
    (h : p.last.workTapes i z ≠ none) : z.natAbs ≤ p.spaceByTape i := by
  simpa using p.natAbs_le_spaceByTape_of_mem_visited i (p.mem_visited_of_workTapes_ne i z h)

/-- A set containing every head position contains the visited set. -/
lemma visited_subset (p : ntm.RunPath start) {i : Fin k} {S : Finset ℤ}
    (h : ∀ n (hn : n < p.cfgs.length), p.cfgs[n].workTapePos i ∈ S) : p.visited i ⊆ S := by
  intro z hz
  obtain ⟨n, hn, rfl⟩ := p.mem_visited.mp hz
  exact h n hn

/-- A finite set of possible head positions bounds the space of a tape. -/
lemma spaceByTape_le_card (p : ntm.RunPath start) {i : Fin k} {S : Finset ℤ}
    (h : ∀ n (hn : n < p.cfgs.length), p.cfgs[n].workTapePos i ∈ S) :
    p.spaceByTape i ≤ S.card := Finset.card_le_card (p.visited_subset h)

/-- A stationary head uses at most one cell. -/
lemma spaceByTape_le_one (p : ntm.RunPath start) {i : Fin k}
    (h : ∀ n (hn : n < p.cfgs.length), p.cfgs[n].workTapePos i = start.workTapePos i) :
    p.spaceByTape i ≤ 1 := by
  simpa using p.spaceByTape_le_card (S := {start.workTapePos i}) fun n hn => by simp [h n hn]

/-- Stationary work tape heads use at most one cell per tape. -/
lemma space_le_of_workTapePos_const (p : ntm.RunPath start)
    (h : ∀ n (hn : n < p.cfgs.length), p.cfgs[n].workTapePos = start.workTapePos) :
    p.space ≤ k := by
  simpa [space_eq_sum] using Finset.sum_le_card_nsmul Finset.univ _ 1
    (fun i _ => p.spaceByTape_le_one fun n hn => congrFun (h n hn) i)

/-- Splitting a path splits its visited set into the union of the two parts. -/
lemma visited_take_union_drop (p : ntm.RunPath start) (n : ℕ) (hn : n < p.cfgs.length)
    (i : Fin k) : p.visited i = (p.take n hn).visited i ∪ (p.drop n hn).visited i := by
  ext z
  simp only [mem_visited, take_cfgs, drop_cfgs, List.length_take, List.length_drop,
    List.getElem_take, List.getElem_drop, Finset.mem_union]
  constructor
  · rintro ⟨m, hm, hz⟩
    by_cases hmn : m ≤ n
    · exact Or.inl ⟨m, by omega, hz⟩
    · exact Or.inr ⟨m - n, by omega, by simpa [Nat.add_sub_cancel' (by omega : n ≤ m)] using hz⟩
  · rintro (⟨m, hm, hz⟩ | ⟨m, hm, hz⟩)
    · exact ⟨m, by omega, hz⟩
    · exact ⟨n + m, by omega, hz⟩

/-- The sum of the spaces of two parts bounds the space of the whole path. -/
lemma space_le_take_add_drop (p : ntm.RunPath start) (n : ℕ) (hn : n < p.cfgs.length) :
    p.space ≤ (p.take n hn).space + (p.drop n hn).space := by
  simp only [space_eq_sum, ← Finset.sum_add_distrib, spaceByTape]
  exact Finset.sum_le_sum fun i _ => by
    rw [p.visited_take_union_drop n hn i]
    exact Finset.card_union_le _ _

/-- Paths with the same work tape head positions use the same space, even in different machines. -/
lemma space_eq_of_workTapePos {State' : Type*} {input' : List Symbol}
    {ntm' : MultiTapeNTM k Symbol State'} {start' : Cfg k Symbol State' input'}
    (p : ntm.RunPath start) (q : ntm'.RunPath start') (hlen : p.time = q.time)
    (h : ∀ n (hn : n < p.cfgs.length) (hn' : n < q.cfgs.length),
      p.cfgs[n].workTapePos = q.cfgs[n].workTapePos) : p.space = q.space := by
  simp only [space_eq_sum, spaceByTape]
  refine Finset.sum_congr rfl fun i _ => congrArg Finset.card (Finset.ext fun z => ?_)
  simp only [mem_visited]
  have hlen' : p.cfgs.length = q.cfgs.length := by
    rw [p.length_eq_time_add_one, q.length_eq_time_add_one, hlen]
  constructor <;> rintro ⟨n, hn, hz⟩
  · exact ⟨n, by omega, by rw [← h n hn (by omega)]; exact hz⟩
  · exact ⟨n, by omega, by rw [h n (by omega) hn]; exact hz⟩

/-- A simulation preserving head positions preserves space. -/
@[simp]
lemma space_map {State' : Type*} {input' : List Symbol} {ntm' : MultiTapeNTM k Symbol State'}
    (p : ntm.RunPath start) (f : Cfg k Symbol State input → Cfg k Symbol State' input')
    (h : ∀ n (hn : n + 1 < p.cfgs.length), ntm'.Step (f p.cfgs[n]) (f p.cfgs[n + 1]))
    (hpos : ∀ c, (f c).workTapePos = c.workTapePos) : (p.map f h).space = p.space := by
  simp [space, spaceUsedOfCfgs, visitedOfCfgs, map, List.map_map, Function.comp_def, hpos]

/-- Joining two paths uses at most the sum of their spaces. -/
lemma space_append_le {middle : Cfg k Symbol State input}
    (p : ntm.RunPath start) (q : ntm.RunPath middle) (h : p.last = middle) :
    (p.append q h).space ≤ p.space + q.space := by
  calc (p.append q h).space ≤ spaceUsedOfCfgs (p.cfgs ++ q.cfgs) := by
        apply spaceUsedOfCfgs_mono
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact List.mem_append_left _ hc
        · exact List.mem_append_right _ (List.mem_of_mem_tail hc)
    _ ≤ p.space + q.space := by
        simp only [space, spaceUsedOfCfgs, visitedOfCfgs, List.map_append,
          List.toFinset_append, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => Finset.card_union_le _ _

/-- A halted prefix has already visited every position of the full path. -/
lemma visited_take_eq_of_halt (p : ntm.RunPath start) (n : ℕ) (hn : n < p.cfgs.length)
    (hhalt : p.cfgs[n].Halted) (i : Fin k) : p.visited i = (p.take n hn).visited i := by
  apply Finset.Subset.antisymm _ (visitedOfCfgs_mono (List.take_subset _ _) i)
  apply p.visited_subset
  intro m hm
  by_cases hmn : m ≤ n
  · exact (p.take n hn).mem_visited.mpr ⟨m, by simp; omega, by simp⟩
  · rw [p.getElem_eq_of_halt (by omega : n ≤ m) hm hhalt]
    exact (p.take n hn).last_workTapePos_mem_visited i

/-- A halted prefix uses the same space as the full path. -/
lemma space_take_eq_of_halt (p : ntm.RunPath start) (n : ℕ) (hn : n < p.cfgs.length)
    (hhalt : p.cfgs[n].Halted) : p.space = (p.take n hn).space := by
  simp only [space_eq_sum, spaceByTape, p.visited_take_eq_of_halt n hn hhalt]

/-- Padding a halted path visits no new cells. -/
@[simp]
lemma visited_pad (p : ntm.RunPath start) (n : ℕ) (hhalt : p.last.Halted) (i : Fin k) :
    (p.pad n hhalt).visited i = p.visited i := by
  simp only [visited, visitedOfCfgs, pad_cfgs, List.map_append, List.map_replicate,
    List.toFinset_append]
  apply Finset.union_eq_left.mpr
  intro z hz
  simp only [List.mem_toFinset, List.mem_replicate] at hz
  obtain ⟨_, rfl⟩ := hz
  exact p.last_workTapePos_mem_visited i

/-- Padding a halted path preserves its space. -/
@[simp]
lemma space_pad (p : ntm.RunPath start) (n : ℕ) (hhalt : p.last.Halted) :
    (p.pad n hhalt).space = p.space := by simp [space_eq_sum, spaceByTape]

end RunPath

end Turing.MultiTapeNTM
