/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Basic

/-!
# Input shortening for multi-tape Turing machines

A visit sequence records the storages seen at a fixed input position during a finite run.
Up to the first halt, these storages are distinct: repeating a core would repeat the rest of the
computation, regardless of the write-only output.

`InputCut` describes a deletion between input-symbol indices. Its position map relates
configurations on the original and shortened inputs, allowing the run segments on either side
to be joined.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

/-- Runs starting with the same core keep the same core. -/
lemma core_runFrom_eq_of_core_eq {c₁ c₂ : Cfg k Symbol State input}
    (h : c₁.core = c₂.core) (t : ℕ) :
    (tm.runFrom c₁ t).core = (tm.runFrom c₂ t).core := by
  induction t with
  | zero => exact h
  | succ t ih =>
    simpa only [runFrom_succ_eq_step'] using core_step_eq_of_core_eq (tm := tm) ih

/-- The cores up to and including the first halt are pairwise distinct. -/
lemma core_runFrom_injOn {cfg : Cfg k Symbol State input} {T : ℕ}
    (hhalt : (tm.runFrom cfg T).Halted)
    (hfirst : ∀ t < T, ¬ (tm.runFrom cfg t).Halted) :
    Set.InjOn (fun t => (tm.runFrom cfg t).core) (Set.Iic T) := by
  intro a ha b hb heq
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha heq.symm (le_of_not_ge hab)).symm
  by_contra hne
  change b ≤ T at hb
  have heq' := tm.core_runFrom_eq_of_core_eq heq (T - b)
  rw [← runFrom_add, ← runFrom_add, Nat.add_sub_of_le hb] at heq'
  exact hfirst (a + (T - b)) (by omega) ((congrArg (fun c => c.2.state) heq').trans hhalt)

/-- Times up to `T` at which the input head is at `p`. -/
def visitTimes (cfg : Cfg k Symbol State input) (T p : ℕ) : Finset ℕ :=
  (Finset.range (T + 1)).filter fun t => (tm.runFrom cfg t).inputPos.val = p

@[simp]
lemma mem_visitTimes {cfg : Cfg k Symbol State input} {T p t : ℕ} :
    t ∈ tm.visitTimes cfg T p ↔ t ≤ T ∧ (tm.runFrom cfg t).inputPos.val = p := by
  simp [visitTimes]

/-- The chronological list of storages encountered at input position `p` through time `T`. -/
def visitSequence (cfg : Cfg k Symbol State input) (T p : ℕ) : List (Storage Symbol State k) :=
  ((tm.visitTimes cfg T p).sort (· ≤ ·)).map fun t => (tm.runFrom cfg t).storage

@[simp]
lemma length_visitSequence (cfg : Cfg k Symbol State input) (T p : ℕ) :
    (tm.visitSequence cfg T p).length = (tm.visitTimes cfg T p).card := by
  simp [visitSequence]

/-- No storage occurs twice at one input position before the first halt. -/
lemma visitSequence_nodup {cfg : Cfg k Symbol State input} {T : ℕ}
    (hhalt : (tm.runFrom cfg T).Halted)
    (hfirst : ∀ t < T, ¬ (tm.runFrom cfg t).Halted) (p : ℕ) :
    (tm.visitSequence cfg T p).Nodup := by
  classical
  apply List.Nodup.map_on _ (Finset.sort_nodup _ _)
  intro a ha b hb h
  have ha' := tm.mem_visitTimes.mp (by simpa using ha)
  have hb' := tm.mem_visitTimes.mp (by simpa using hb)
  apply tm.core_runFrom_injOn hhalt hfirst ha'.1 hb'.1
  exact Prod.ext (Fin.ext (ha'.2.trans hb'.2.symm)) h

/-- If every work head stays in `[-R, R]`, the run visits at most `k * (2 * R + 1)` cells. -/
lemma spaceUsed_le_of_workTapePos_natAbs_le (cfg : Cfg k Symbol State input) (T R : ℕ)
    (h : ∀ t ≤ T, ∀ i, ((tm.runFrom cfg t).workTapePos i).natAbs ≤ R) :
    tm.spaceUsed cfg T ≤ k * (2 * R + 1) := by
  calc tm.spaceUsed cfg T
    _ ≤ ∑ _ : Fin k, (window R).card := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.card_le_card
      intro z hz
      obtain ⟨t, ht, rfl⟩ := tm.mem_visitedByTapeHead.mp hz
      exact mem_window.mpr (h t (by omega) i)
    _ = k * (2 * R + 1) := by simp

/-- Equal storages and scanned input symbols give equal next storages, and both input heads
execute the same move. For halted configurations, this is the stationary move. -/
lemma exists_step_move_of_storage_eq {input' : List Symbol}
    {c : Cfg k Symbol State input} {c' : Cfg k Symbol State input'}
    (hstore : c.storage = c'.storage) (hsym : c.inputSymbol = c'.inputSymbol) :
    ∃ m, (tm.step c).storage = (tm.step c').storage ∧
      (tm.step c).inputPos = moveInputPos c.inputPos m ∧
      (tm.step c').inputPos = moveInputPos c'.inputPos m := by
  rcases c with ⟨state, pos, tapes, heads, out⟩
  rcases c' with ⟨state', pos', tapes', heads', out'⟩
  simp only [Cfg.storage, Storage.mk.injEq] at hstore
  rcases hstore with ⟨rfl, rfl, rfl⟩
  cases state with
  | none => exact ⟨0, rfl, (moveInputPos_zero _).symm, (moveInputPos_zero _).symm⟩
  | some state =>
    dsimp only [step]
    unfold Cfg.workTapeSymbols
    rw [hsym]
    exact ⟨_, rfl, rfl, rfl⟩

/-- Propagate a predicate from `u` to `v` using steps within `[u, v]`. -/
private lemma propagate {P : ℕ → Prop} {u v : ℕ} (huv : u ≤ v) (hu : P u)
    (hstep : ∀ t, u ≤ t → t < v → P t → P (t + 1)) : P v := by
  induction v, huv using Nat.le_induction with
  | base => exact hu
  | succ v huv ih =>
    exact hstep v huv (Nat.lt_succ_self _) (ih fun t hut htv => hstep t hut (by omega))

/-- After staying left of `a` for one step, a walk cannot cross `a` without revisiting it. -/
private lemma walk_left {p : ℕ → ℕ} {u v a : ℕ}
    (hstep : ∀ t, u ≤ t → t < v → p (t + 1) ≤ p t + 1)
    (hu : p u ≤ a) (hu' : p (u + 1) ≤ a)
    (hno : ∀ t, u < t → t < v → p t ≠ a) :
    ∀ t, u ≤ t → t ≤ v → p t ≤ a := by
  intro t hut htv
  apply propagate hut hu
  intro r hur hrt hr
  by_cases heq : r = u
  · simpa [heq] using hu'
  · have := hstep r hur (by omega)
    have := hno r (by omega) (by omega)
    omega

/-- After staying right of `b` for one step, a walk cannot cross `b` without revisiting it. -/
private lemma walk_right {p : ℕ → ℕ} {u v b : ℕ}
    (hstep : ∀ t, u ≤ t → t < v → p t ≤ p (t + 1) + 1)
    (hu : b ≤ p u) (hu' : b ≤ p (u + 1))
    (hno : ∀ t, u < t → t < v → p t ≠ b) :
    ∀ t, u ≤ t → t ≤ v → b ≤ p t := by
  intro t hut htv
  apply propagate hut hu
  intro r hur hrt hr
  by_cases heq : r = u
  · simpa [heq] using hu'
  · have := hstep r hur (by omega)
    have := hno r (by omega) (by omega)
    omega

/-- The entry at index `i` is the storage at the `i`th visit time. -/
private lemma visitSequence_get {cfg : Cfg k Symbol State input} {T p m : ℕ}
    (h : (tm.visitTimes cfg T p).card = m) (i : Fin m) :
    (tm.visitSequence cfg T p)[i.val]'(by rw [length_visitSequence, h]; exact i.isLt) =
      (tm.runFrom cfg ((tm.visitTimes cfg T p).orderEmbOfFin h i)).storage := by
  simp [visitSequence, Finset.orderEmbOfFin_apply]

/-- An ordered pair of input-symbol indices. The cut deletes the symbols after the first
through the second; equal endpoints give an empty deletion. -/
abbrev InputCut (input : List Symbol) := NonemptyInterval (Fin input.length)

namespace InputCut

variable (cut : InputCut input)

/-- The one-based input-head position of the retained endpoint. -/
def left : ℕ := cut.fst.val + 1

/-- The one-based input-head position of the right endpoint. -/
def right : ℕ := cut.snd.val + 1

/-- The input obtained by deleting the cells after `left` through `right`. -/
def shortened : List Symbol :=
  input.take cut.left ++ input.drop cut.right

/-- Collapse the deleted interval to its left endpoint and shift subsequent positions left. -/
def position (p : ℕ) : ℕ :=
  min p cut.left + (p - cut.right)

/-- Corresponding configurations have equal storage and input positions related by the cut. -/
def Matches (c : Cfg k Symbol State input)
    (c' : Cfg k Symbol State cut.shortened) : Prop :=
  c'.inputPos.val = cut.position c.inputPos.val ∧ c'.storage = c.storage

/-- A corresponding configuration is reachable on the shortened input. -/
def Reachable (tm : MultiTapeTM k Symbol State)
    (c : Cfg k Symbol State input) : Prop :=
  ∃ t, cut.Matches c (tm.runFrom (tm.initCfg cut.shortened) t)

/-- Adding back the deleted cells recovers the original input length. -/
private lemma length_shortened_add :
    cut.shortened.length + (cut.right - cut.left) = input.length := by
  simp only [shortened, List.length_append, List.length_take, List.length_drop]
  dsimp only [left, right]
  have := cut.fst_le_snd
  omega

/-- Positions at or left of the cut do not move. -/
private lemma position_left {p : ℕ} (hp : p ≤ cut.left) : cut.position p = p := by
  simp only [position, left, right] at *
  have := cut.fst_le_snd
  omega

/-- Positions at or right of the cut shift by the number of deleted cells. -/
private lemma position_right {p : ℕ} (hp : cut.right ≤ p) :
    cut.position p = p - (cut.right - cut.left) := by
  simp only [position, left, right] at *
  have := cut.fst_le_snd
  omega

/-- Corresponding input positions on the left read the same symbol. -/
private lemma inputSymbol_left (c : Cfg k Symbol State input)
    (c' : Cfg k Symbol State cut.shortened)
    (hc : c.inputPos.val ≤ cut.left) (hp : c'.inputPos.val = c.inputPos.val) :
    c.inputSymbol = c'.inputSymbol := by
  rw [inputSymbol_eq_getElem?, inputSymbol_eq_getElem?, hp]
  split_ifs with h
  · rfl
  · have hi : c.inputPos.val - 1 < cut.left := by omega
    have hle : cut.left ≤ input.length := cut.fst.isLt
    simp [shortened, List.getElem?_append, hle, hi]

/-- Corresponding input positions on the right read the same symbol, including at the cut. -/
private lemma inputSymbol_right (hsym : input[cut.fst] = input[cut.snd])
    (c : Cfg k Symbol State input)
    (c' : Cfg k Symbol State cut.shortened)
    (hc : cut.right ≤ c.inputPos.val)
    (hp : c'.inputPos.val + (cut.right - cut.left) = c.inputPos.val) :
    c.inputSymbol = c'.inputSymbol := by
  have ha : 0 < cut.left := Nat.succ_pos _
  have hab : cut.left ≤ cut.right := Nat.add_le_add_right cut.fst_le_snd 1
  have hb : cut.right ≤ input.length := cut.snd.isLt
  have hp₀ : c.inputPos.val ≠ 0 := by omega
  have hp'₀ : c'.inputPos.val ≠ 0 := by omega
  rw [inputSymbol_eq_getElem?, inputSymbol_eq_getElem?, ite_eq_right hp₀,
    ite_eq_right hp'₀]
  have htake : (input.take cut.left).length = cut.left := by simp; omega
  by_cases heq : c.inputPos.val = cut.right
  · have hpa : c'.inputPos.val = cut.left := by omega
    simpa [shortened, hpa, heq, List.getElem?_append,
      left, right, Fin.getElem_fin] using hsym.symm
  · have hi : cut.left ≤ c'.inputPos.val - 1 := by omega
    have he : cut.right + (c'.inputPos.val - 1 - cut.left) = c.inputPos.val - 1 := by omega
    simp [shortened, List.getElem?_append, htake, not_lt.mpr hi, he]

/-- A step staying on the left preserves reachability on the shortened input. -/
private lemma reachable_step_left {c : Cfg k Symbol State input}
    (hc : c.inputPos.val ≤ cut.left) (hc' : (tm.step c).inputPos.val ≤ cut.left)
    (h : cut.Reachable tm c) : cut.Reachable tm (tm.step c) := by
  obtain ⟨u, hp, hs⟩ := h
  rw [cut.position_left hc] at hp
  obtain ⟨m, hs', hm, hm'⟩ := tm.exists_step_move_of_storage_eq hs.symm
    (cut.inputSymbol_left _ _ hc hp)
  refine ⟨u + 1, ?_, ?_⟩
  · rw [runFrom_succ_eq_step', hm', cut.position_left hc', hm]
    exact (moveInputPos_same _ _ hp.symm (hc.trans cut.fst.isLt)
      (by
        have := cut.length_shortened_add
        dsimp only [left, right] at *
        have := cut.fst_le_snd
        omega) m).symm
  · simpa only [runFrom_succ_eq_step'] using hs'.symm

/-- A step staying on the right preserves reachability on the shortened input. -/
private lemma reachable_step_right (hsym : input[cut.fst] = input[cut.snd])
    {c : Cfg k Symbol State input}
    (hc : cut.right ≤ c.inputPos.val) (hc' : cut.right ≤ (tm.step c).inputPos.val)
    (h : cut.Reachable tm c) : cut.Reachable tm (tm.step c) := by
  obtain ⟨u, hp, hs⟩ := h
  rw [cut.position_right hc] at hp
  have hpos : (tm.runFrom (tm.initCfg cut.shortened) u).inputPos.val +
      (cut.right - cut.left) = c.inputPos.val := by omega
  obtain ⟨m, hs', hm, hm'⟩ := tm.exists_step_move_of_storage_eq hs.symm
    (cut.inputSymbol_right hsym _ _ hc hpos)
  refine ⟨u + 1, ?_, ?_⟩
  · rw [runFrom_succ_eq_step', hm', cut.position_right hc', hm]
    have he := moveInputPos_shift c.inputPos
      (tm.runFrom (tm.initCfg cut.shortened) u).inputPos hpos cut.length_shortened_add
      (by dsimp only [left, right] at *; omega) m
    omega
  · simpa only [runFrom_succ_eq_step'] using hs'.symm

/-- Equal visit sequences allow the run segments on either side of the cut to be joined.
Every configuration outside the cut through time `T` has a reachable counterpart. -/
private lemma reachable_of_visitSequence_eq {T : ℕ}
    (hsym : input[cut.fst] = input[cut.snd])
    (hseq : tm.visitSequence (tm.initCfg input) T cut.left =
      tm.visitSequence (tm.initCfg input) T cut.right)
    {t : ℕ} (ht : t ≤ T)
    (hp : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ cut.left ∨
      cut.right ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val) :
    cut.Reachable tm (tm.runFrom (tm.initCfg input) t) := by
  let c := tm.runFrom (tm.initCfg input)
  let p := fun u => (c u).inputPos.val
  have hc (u) : c (u + 1) = tm.step (c u) := runFrom_succ_eq_step'
  let m := (tm.visitTimes (tm.initCfg input) T cut.left).card
  have hcard : (tm.visitTimes (tm.initCfg input) T cut.right).card = m := by
    simpa [m] using (congrArg List.length hseq).symm
  let A : Fin m ↪o ℕ := (tm.visitTimes (tm.initCfg input) T cut.left).orderEmbOfFin rfl
  let B := (tm.visitTimes (tm.initCfg input) T cut.right).orderEmbOfFin hcard
  have hA : ∀ i, A i ≤ T ∧ (c (A i)).inputPos.val = cut.left := fun i =>
    tm.mem_visitTimes.mp (Finset.orderEmbOfFin_mem _ _ i)
  have hB : ∀ i, B i ≤ T ∧ (c (B i)).inputPos.val = cut.right := fun i =>
    tm.mem_visitTimes.mp (Finset.orderEmbOfFin_mem _ _ i)
  have hAc : ∀ u ≤ T, p u = cut.left → ∃ i, A i = u := by
    intro u hu hpu
    change u ∈ Set.range A
    simpa only [A, Finset.range_orderEmbOfFin, Finset.mem_coe] using
      tm.mem_visitTimes.mpr ⟨hu, hpu⟩
  have hBc : ∀ u ≤ T, p u = cut.right → ∃ i, B i = u := by
    intro u hu hpu
    change u ∈ Set.range B
    simpa only [B, Finset.range_orderEmbOfFin, Finset.mem_coe] using
      tm.mem_visitTimes.mpr ⟨hu, hpu⟩
  have hq : ∀ i, (c (A i)).storage = (c (B i)).storage := by
    intro i
    have heq := List.getElem_of_eq hseq (i := i.val)
      (by rw [length_visitSequence]; exact i.isLt)
    exact (visitSequence_get rfl i).symm.trans (heq.trans (visitSequence_get hcard i))
  have hmove (i) : p (A i + 1) + cut.right = p (B i + 1) + cut.left := by
    have hsy : (c (A i)).inputSymbol = (c (B i)).inputSymbol := by
      rw [inputSymbol_eq_getElem?, inputSymbol_eq_getElem?, (hA i).2, (hB i).2]
      simpa [left, right, Fin.getElem_fin] using hsym
    obtain ⟨dir, _, hleft, hright⟩ := tm.exists_step_move_of_storage_eq (hq i) hsy
    change (c (A i + 1)).inputPos.val + cut.right =
      (c (B i + 1)).inputPos.val + cut.left
    rw [hc, hc, hleft, hright]
    simpa only [(hA i).2, (hB i).2] using
      moveInputPos_interior (c (A i)).inputPos (c (B i)).inputPos
        (by rw [(hA i).2]; exact Nat.succ_pos _)
        (by rw [(hA i).2]; exact cut.fst.isLt)
        (by rw [(hB i).2]; exact Nat.succ_pos _)
        (by rw [(hB i).2]; exact cut.snd.isLt) dir
  have hmatch (i) : cut.Reachable tm (c (A i)) ↔ cut.Reachable tm (c (B i)) := by
    have hba : cut.right - (cut.right - cut.left) = cut.left :=
      Nat.sub_sub_self (Nat.add_le_add_right cut.fst_le_snd 1)
    simp only [Reachable, Matches, (hA i).2, (hB i).2,
      cut.position_left le_rfl, cut.position_right le_rfl, hba, hq i]
  have hstep (u) : p (u + 1) ≤ p u + 1 ∧ p u ≤ p (u + 1) + 1 := by
    simpa only [p, c, runFrom_succ_eq_step'] using tm.inputPos_step_bounds (c u)
  have hleft {u} (hu : p u ≤ cut.left) (hu' : p (u + 1) ≤ cut.left) :
      cut.Reachable tm (c u) → cut.Reachable tm (c (u + 1)) := by
    rw [hc]
    exact cut.reachable_step_left hu (by simpa only [p, hc] using hu')
  have hright {u} (hu : cut.right ≤ p u) (hu' : cut.right ≤ p (u + 1)) :
      cut.Reachable tm (c u) → cut.Reachable tm (c (u + 1)) := by
    rw [hc]
    exact cut.reachable_step_right hsym hu (by simpa only [p, hc] using hu')
  have hp₀ : p 0 ≤ cut.left := by simp [p, c, left]
  have hinit : cut.Reachable tm (c 0) := by
    refine ⟨0, ?_, ?_⟩
    · rw [cut.position_left hp₀]
      rfl
    · rfl
  have boundary : ∀ i, cut.Reachable tm (c (A i)) := by
    clear_value A B m
    cases m with
    | zero => exact fun i => Fin.elim0 i
    | succ m =>
      intro i
      induction i using Fin.induction with
      | zero =>
        have hno : ∀ u < A 0, p u ≠ cut.left := by
          intro u hu hpu
          obtain ⟨j, rfl⟩ := hAc u (hu.le.trans (hA 0).1) hpu
          exact (not_lt_of_ge (A.monotone (Fin.zero_le j))) hu
        have hside : ∀ u ≤ A 0, p u ≤ cut.left := by
          intro u hu
          apply propagate (Nat.zero_le u) hp₀
          intro r _ hru hr
          have := (hstep r).1
          have := hno r (by omega)
          omega
        exact propagate (P := fun u => cut.Reachable tm (c u)) (Nat.zero_le (A 0)) hinit
          fun u _ hu => hleft (hside u hu.le) (hside (u + 1) hu)
      | succ i ih =>
        have hAj := A.strictMono i.castSucc_lt_succ
        have hBj := B.strictMono i.castSucc_lt_succ
        have hnoA : ∀ u, A i.castSucc < u → u < A i.succ → p u ≠ cut.left := by
          intro u hju hui hpu
          obtain ⟨r, rfl⟩ := hAc u (hui.le.trans (hA i.succ).1) hpu
          exact (not_lt_of_ge (Fin.le_castSucc_iff.mpr (A.lt_iff_lt.mp hui)))
            (A.lt_iff_lt.mp hju)
        have hnoB : ∀ u, B i.castSucc < u → u < B i.succ → p u ≠ cut.right := by
          intro u hju hui hpu
          obtain ⟨r, rfl⟩ := hBc u (hui.le.trans (hB i.succ).1) hpu
          exact (not_lt_of_ge (Fin.le_castSucc_iff.mpr (B.lt_iff_lt.mp hui)))
            (B.lt_iff_lt.mp hju)
        by_cases hdir : p (A i.castSucc + 1) ≤ cut.left
        · have hside := walk_left (fun u _ _ => (hstep u).1)
            (le_of_eq (hA i.castSucc).2) hdir hnoA
          exact propagate (P := fun u => cut.Reachable tm (c u)) hAj.le ih fun u hju hui =>
            hleft (hside u hju hui.le) (hside (u + 1) (by omega) hui)
        · have hdir' : cut.right ≤ p (B i.castSucc + 1) := by
            have := hmove i.castSucc
            omega
          have hside := walk_right (fun u _ _ => (hstep u).2)
            (ge_of_eq (hB i.castSucc).2) hdir' hnoB
          apply (hmatch i.succ).mpr
          exact propagate (P := fun u => cut.Reachable tm (c u)) hBj.le
            ((hmatch i.castSucc).mp ih) fun u hju hui =>
              hright (hside u hju hui.le) (hside (u + 1) (by omega) hui)
  change cut.Reachable tm (c t)
  induction t with
  | zero => exact hinit
  | succ t ih =>
    have hst := hstep t
    by_cases hl : p (t + 1) ≤ cut.left
    · by_cases heq : p (t + 1) = cut.left
      · obtain ⟨i, hi⟩ := hAc (t + 1) ht heq
        simpa only [hi] using boundary i
      · have hprev : p t ≤ cut.left := by omega
        exact hleft hprev hl (ih (by omega) (Or.inl hprev))
    · have hr : cut.right ≤ p (t + 1) := hp.resolve_left hl
      by_cases heq : p (t + 1) = cut.right
      · obtain ⟨i, hi⟩ := hBc (t + 1) ht heq
        simpa only [hi] using (hmatch i).mp (boundary i)
      · have hprev : cut.right ≤ p t := by omega
        exact hright hprev hr (ih (by omega) (Or.inr hprev))

end InputCut

/-- Equal symbols and visit sequences at the endpoints of a cut preserve every storage reached
outside the deleted interval through time `T`. -/
theorem exists_storage_cut (cut : InputCut input) {T : ℕ}
    (hsym : input[cut.fst] = input[cut.snd])
    (hseq : tm.visitSequence (tm.initCfg input) T cut.left =
      tm.visitSequence (tm.initCfg input) T cut.right)
    {t : ℕ} (ht : t ≤ T)
    (hp : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ cut.left ∨
      cut.right ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val) :
    ∃ u, (tm.runFrom (tm.initCfg cut.shortened) u).storage =
      (tm.runFrom (tm.initCfg input) t).storage := by
  obtain ⟨u, _, hs⟩ := cut.reachable_of_visitSequence_eq hsym hseq ht hp
  exact ⟨u, hs⟩

/-- Every entry of a visit sequence is a storage reached by the run. -/
lemma mem_range_of_mem_visitSequence {cfg : Cfg k Symbol State input} {T p : ℕ}
    {s : Storage Symbol State k} (h : s ∈ tm.visitSequence cfg T p) :
    s ∈ Set.range (fun t => (tm.runFrom cfg t).storage) := by
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
  exact ⟨t, rfl⟩

/-- A visit sequence of a halting space-bounded run has length at most the storage bound. -/
lemma length_visitSequence_le [Fintype Symbol] [Fintype State] {T s : ℕ}
    (hhalt : (tm.runFrom (tm.initCfg input) T).Halted)
    (hfirst : ∀ t < T, ¬ (tm.runFrom (tm.initCfg input) t).Halted)
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) (p : ℕ) :
    (tm.visitSequence (tm.initCfg input) T p).length ≤ storageBound Symbol State k s := by
  classical
  have hn := tm.visitSequence_nodup hhalt hfirst p
  have hsub : ((tm.visitSequence (tm.initCfg input) T p).toFinset : Set _) ⊆
      Set.range (fun t => (tm.runFrom (tm.initCfg input) t).storage) := by
    intro x hx
    exact tm.mem_range_of_mem_visitSequence (List.mem_toFinset.mp hx)
  have hle := (Set.encard_le_encard hsub).trans (tm.encard_storages_le hs)
  rw [Set.encard_coe_eq_coe_finsetCard, List.toFinset_card_of_nodup hn] at hle
  exact_mod_cast hle

/-- A sufficiently long input to a halting space-bounded machine can be shortened while
preserving any designated storage reached by the run. -/
theorem exists_shorter_input_storage [Fintype Symbol] [Fintype State] {s : ℕ}
    (hhalt : ∃ T, (tm.runFrom (tm.initCfg input) T).Halted)
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s)
    (hlen : 2 * Fintype.card Symbol *
      (storageBound Symbol State k s + 1) ^ storageBound Symbol State k s < input.length)
    (t : ℕ) :
    ∃ input' : List Symbol, input'.length < input.length ∧
      ∃ u, (tm.runFrom (tm.initCfg input') u).storage =
        (tm.runFrom (tm.initCfg input) t).storage := by
  classical
  obtain ⟨T, hT, hfirst⟩ := Nat.findX hhalt
  wlog ht : t ≤ T generalizing t
  · simpa only [tm.runFrom_eq_of_halt (Nat.le_of_not_ge ht) hT] using this T le_rfl
  let B := storageBound Symbol State k s
  let S := Set.range (fun u => (tm.runFrom (tm.initCfg input) u).storage)
  have hbound : S.encard ≤ B := tm.encard_storages_le hs
  let : Fintype S := (Set.finite_of_encard_le_coe hbound).fintype
  have hcard : Fintype.card S ≤ B := by
    have h := hbound
    rw [← Set.coe_fintypeCard] at h
    exact_mod_cast h
  let seq := tm.visitSequence (tm.initCfg input) T
  let enc (p : ℕ) : List S := (seq p).attachWith (· ∈ S)
    (fun _ h => tm.mem_range_of_mem_visitSequence h)
  have henc (p : ℕ) : (enc p).map Subtype.val = seq p :=
    List.attachWith_map_subtype_val _
  have hlength (p : ℕ) : (enc p).length ≤ B := by
    simpa only [enc, List.length_attachWith] using tm.length_visitSequence_le hT hfirst hs p
  let f (i : Fin input.length) : Symbol × (Fin B → Option S) :=
    (input[i], fun j => (enc (i.val + 1))[j.val]?)
  have heq {i j : Fin input.length} (h : f i = f j) :
      input[i] = input[j] ∧ seq (i.val + 1) = seq (j.val + 1) := by
    refine ⟨congrArg Prod.fst h, ?_⟩
    have hh : enc (i.val + 1) = enc (j.val + 1) := by
      apply List.ext_getElem?
      intro r
      by_cases hr : r < B
      · exact congrFun (congrArg Prod.snd h) ⟨r, hr⟩
      · rw [List.getElem?_eq_none (by have := hlength (i.val + 1); omega),
          List.getElem?_eq_none (by have := hlength (j.val + 1); omega)]
    simpa only [henc] using congrArg (List.map Subtype.val) hh
  have hsig : Fintype.card (Symbol × (Fin B → Option S)) ≤
      Fintype.card Symbol * (B + 1) ^ B := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_option]
    gcongr
    omega
  obtain ⟨v, hv⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (n := 2) (by
    rw [Fintype.card_fin]
    change 2 * Fintype.card Symbol * (B + 1) ^ B < input.length at hlen
    calc Fintype.card (Symbol × (Fin B → Option S)) * 2
      _ ≤ (Fintype.card Symbol * (B + 1) ^ B) * 2 := Nat.mul_le_mul_right 2 hsig
      _ = 2 * Fintype.card Symbol * (B + 1) ^ B := by ring
      _ < input.length := hlen)
  let e := (Finset.univ.filter (fun i => f i = v)).orderEmbOfCardLe
    (show 3 ≤ (Finset.univ.filter (fun i => f i = v)).card by omega)
  have he (i : Fin 3) : f (e i) = v := by
    have hmem : e i ∈ Finset.univ.filter (fun i => f i = v) :=
      Finset.orderEmbOfCardLe_mem _ _ i
    exact (Finset.mem_filter.mp hmem).2
  have hab : (e 0).val + 1 < (e 1).val + 1 :=
    Nat.add_lt_add_right (e.strictMono (by decide)) 1
  have hbc : (e 1).val + 1 < (e 2).val + 1 :=
    Nat.add_lt_add_right (e.strictMono (by decide)) 1
  have hab' := heq ((he 0).trans (he 1).symm)
  have hbc' := heq ((he 1).trans (he 2).symm)
  have cut {i j : Fin input.length} (hij : i.val + 1 < j.val + 1)
      (hij' : input[i] = input[j] ∧ seq (i.val + 1) = seq (j.val + 1))
      (hpos : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ i.val + 1 ∨
        j.val + 1 ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val) :
      ∃ input' : List Symbol, input'.length < input.length ∧
        ∃ u, (tm.runFrom (tm.initCfg input') u).storage =
          (tm.runFrom (tm.initCfg input) t).storage := by
    refine ⟨input.take (i.val + 1) ++ input.drop (j.val + 1), ?_, ?_⟩
    · simp only [List.length_append, List.length_take, List.length_drop]
      have := i.isLt
      have := j.isLt
      omega
    · exact tm.exists_storage_cut ⟨⟨i, j⟩, by change i.val ≤ j.val; omega⟩
        hij'.1 hij'.2 ht hpos
  by_cases hpos : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ (e 0).val + 1 ∨
      (e 1).val + 1 ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val
  · exact cut hab hab' hpos
  · exact cut hbc hbc' (Or.inl (by omega))

end Turing.MultiTapeTM
