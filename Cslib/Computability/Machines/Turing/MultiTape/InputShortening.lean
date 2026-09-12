/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Cover
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

open Relation

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

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

/-- Equal visit sequences pair the visit times in order, with equal storage at each pair. -/
lemma exists_visitTimes_orderIso {cfg : Cfg k Symbol State input} {T p q : ℕ}
    (hseq : tm.visitSequence cfg T p = tm.visitSequence cfg T q) :
    ∃ e : tm.visitTimes cfg T p ≃o tm.visitTimes cfg T q,
      ∀ t : tm.visitTimes cfg T p,
        (tm.runFrom cfg t).storage = (tm.runFrom cfg (e t)).storage := by
  have hcard : (tm.visitTimes cfg T q).card = (tm.visitTimes cfg T p).card := by
    simpa using (congrArg List.length hseq).symm
  let A := (tm.visitTimes cfg T p).orderIsoOfFin rfl
  let B := (tm.visitTimes cfg T q).orderIsoOfFin hcard
  refine ⟨A.symm.trans B, ?_⟩
  intro t
  obtain ⟨i, rfl⟩ := A.surjective t
  have heq := List.getElem_of_eq hseq (i := i.val)
    (by rw [length_visitSequence]; exact i.isLt)
  simpa only [visitSequence, List.getElem_map, OrderIso.trans_apply,
    OrderIso.symm_apply_apply, A, B, Finset.coe_orderIsoOfFin_apply,
    Finset.orderEmbOfFin_apply, Fin.getElem_fin] using heq

/-- No earlier time visits the position of a minimal visit. -/
private lemma not_visit_before {cfg : Cfg k Symbol State input} {T p t : ℕ}
    {u : tm.visitTimes cfg T p} (hu : IsMin u) (ht : t < u.val) :
    (tm.runFrom cfg t).inputPos.val ≠ p := by
  intro hp
  have hT := (tm.mem_visitTimes.mp u.property).1
  exact ht.not_ge (hu (b := ⟨t, tm.mem_visitTimes.mpr ⟨ht.le.trans hT, hp⟩⟩) ht.le)

/-- The covering relation on visit times means that no visit occurs strictly between them. -/
private lemma not_visit_between {cfg : Cfg k Symbol State input} {T p t : ℕ}
    {u v : tm.visitTimes cfg T p} (h : u ⋖ v) (hlo : u.val < t) (hhi : t < v.val) :
    (tm.runFrom cfg t).inputPos.val ≠ p := by
  intro hp
  have hT := (tm.mem_visitTimes.mp v.property).1
  exact h.2 (c := ⟨t, tm.mem_visitTimes.mpr ⟨hhi.le.trans hT, hp⟩⟩) hlo hhi

/-- Between consecutive visits, a first step to the left keeps the input head on the left. -/
private lemma inputPos_le_of_covBy {cfg : Cfg k Symbol State input} {T p : ℕ}
    {u v : tm.visitTimes cfg T p} (h : u ⋖ v)
    (hdir : (tm.runFrom cfg (u.val + 1)).inputPos.val ≤ p) :
    ∀ t, u.val ≤ t → t ≤ v.val → (tm.runFrom cfg t).inputPos.val ≤ p := by
  intro t hut htv
  rcases eq_or_lt_of_le hut with rfl | hut
  · exact (tm.mem_visitTimes.mp u.property).2.le
  · exact tm.inputPos_le_of_forall_ne hut hdir fun r hur hrt =>
      not_visit_between h (Nat.lt_of_succ_le hur) (hrt.trans_le htv)

/-- Between consecutive visits, a first step to the right keeps the input head on the right. -/
private lemma le_inputPos_of_covBy {cfg : Cfg k Symbol State input} {T p : ℕ}
    {u v : tm.visitTimes cfg T p} (h : u ⋖ v)
    (hdir : p ≤ (tm.runFrom cfg (u.val + 1)).inputPos.val) :
    ∀ t, u.val ≤ t → t ≤ v.val → p ≤ (tm.runFrom cfg t).inputPos.val := by
  intro t hut htv
  rcases eq_or_lt_of_le hut with rfl | hut
  · exact (tm.mem_visitTimes.mp u.property).2.ge
  · exact tm.le_inputPos_of_forall_ne hut hdir fun r hur hrt =>
      not_visit_between h (Nat.lt_of_succ_le hur) (hrt.trans_le htv)

/-- An ordered pair of input-symbol indices. The cut deletes the symbols after the first
through the second; equal endpoints give an empty deletion.
`fst` and `snd` are zero-based list indices; `left` and `right` are the corresponding
input-head positions, offset by one because position `0` is the left endmarker. -/
abbrev InputCut (input : List Symbol) := NonemptyInterval (Fin input.length)

namespace InputCut

variable (cut : InputCut input)

/-- The head position of the retained endpoint: position `0` is the left endmarker. -/
def left : ℕ := cut.fst.val + 1

/-- The head position of the right endpoint: input symbol `i` is read at position `i + 1`. -/
def right : ℕ := cut.snd.val + 1

/-- The input obtained by deleting the cells after `left` through `right`. -/
def shortened : List Symbol :=
  input.take cut.left ++ input.drop cut.right

/-- Collapse the deleted interval to its left endpoint and shift subsequent positions left. -/
def position (p : ℕ) : ℕ :=
  min p cut.left + (p - cut.right)

/-- Two input positions lie on the same retained side of the cut. -/
def SameSide (p q : ℕ) : Prop :=
  (p ≤ cut.left ∧ q ≤ cut.left) ∨ (cut.right ≤ p ∧ cut.right ≤ q)

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

/-- The cut preserves the left endmarker and maps positive positions to positive positions. -/
@[simp]
lemma position_eq_zero {p : ℕ} : cut.position p = 0 ↔ p = 0 := by
  simp only [position, left, right]
  omega

/-- Indexing the retained prefix is unchanged. -/
lemma getElem?_left {i : ℕ} (hi : i < cut.left) : cut.shortened[i]? = input[i]? := by
  have hle : cut.left ≤ input.length := cut.fst.isLt
  simp [shortened, List.getElem?_append, hle, hi]

/-- Indexing the retained suffix shifts by the number of deleted symbols. -/
lemma getElem?_right (i : ℕ) :
    cut.shortened[cut.left + i]? = input[cut.right + i]? := by
  have hle : cut.left ≤ input.length := cut.fst.isLt
  simp [shortened, List.getElem?_append, hle]

/-- The removed right endpoint is represented by the retained left endpoint. -/
lemma getElem?_boundary (hsym : input[cut.fst] = input[cut.snd]) :
    cut.shortened[cut.left - 1]? = input[cut.right - 1]? := by
  rw [cut.getElem?_left (Nat.sub_lt (Nat.succ_pos _) (by decide))]
  simpa [left, right, Fin.getElem_fin] using congrArg some hsym

/-- Outside the deleted interval, the position map preserves the indexed symbol. -/
lemma getElem?_position (hsym : input[cut.fst] = input[cut.snd]) {p : ℕ}
    (hp : p ≤ cut.left ∨ cut.right ≤ p) :
    cut.shortened[cut.position p - 1]? = input[p - 1]? := by
  have ha : 0 < cut.left := Nat.succ_pos _
  have hab : cut.left ≤ cut.right := Nat.add_le_add_right cut.fst_le_snd 1
  rcases hp with hp | hp
  · rw [cut.position_left hp]
    exact cut.getElem?_left (by omega)
  · rw [cut.position_right hp]
    by_cases heq : p = cut.right
    · subst p
      rw [Nat.sub_sub_self hab]
      exact cut.getElem?_boundary hsym
    · convert cut.getElem?_right (p - cut.right - 1) using 2 <;> omega

/-- On either retained side, mapping positions commutes with an input-head move. -/
lemma position_moveInputPos {p : Fin (input.length + 2)}
    {p' : Fin (cut.shortened.length + 2)} (hp : p'.val = cut.position p.val) (m : SignType)
    (hside : cut.SameSide p.val (moveInputPos p m).val) :
    cut.position (moveInputPos p m).val = (moveInputPos p' m).val := by
  have hlen := cut.length_shortened_add
  have hbounds : 0 < cut.left ∧ cut.left ≤ cut.right ∧ cut.right ≤ input.length :=
    ⟨Nat.succ_pos _, Nat.add_le_add_right cut.fst_le_snd 1, cut.snd.isLt⟩
  rcases hside with ⟨hc, hn⟩ | ⟨hc, hn⟩
  · rw [cut.position_left hc] at hp
    rw [cut.position_left hn]
    exact moveInputPos_same _ _ hp.symm (by omega) (by omega) m
  · rw [cut.position_right hc] at hp
    rw [cut.position_right hn]
    have he := moveInputPos_shift p p' (by omega) hlen (by omega) m
    omega

/-- Corresponding configurations have equal storage and input positions related by the cut. -/
def Matches (c : Cfg k Symbol State input)
    (c' : Cfg k Symbol State cut.shortened) : Prop :=
  c'.inputPos.val = cut.position c.inputPos.val ∧ c'.storage = c.storage

namespace Matches

variable {cut}

/-- Matching configurations outside the cut scan the same symbol when its endpoints agree. -/
lemma inputSymbol (hsym : input[cut.fst] = input[cut.snd])
    {c : Cfg k Symbol State input} {c' : Cfg k Symbol State cut.shortened}
    (h : cut.Matches c c') (hp : c.inputPos.val ≤ cut.left ∨ cut.right ≤ c.inputPos.val) :
    c.inputSymbol = c'.inputSymbol := by
  simp only [inputSymbol_eq_getElem?, h.1, cut.position_eq_zero,
    cut.getElem?_position hsym hp]

/-- A step whose endpoints lie on the same retained side preserves matching configurations. -/
lemma step (hsym : input[cut.fst] = input[cut.snd])
    {c : Cfg k Symbol State input} {c' : Cfg k Symbol State cut.shortened}
    (h : cut.Matches c c') (hside : cut.SameSide c.inputPos.val (tm.step c).inputPos.val) :
    cut.Matches (tm.step c) (tm.step c') := by
  obtain ⟨m, hs, hm, hm'⟩ := tm.exists_step_move_of_storage_eq h.2.symm
    (h.inputSymbol hsym (hside.imp And.left And.left))
  rw [hm] at hside
  refine ⟨?_, hs.symm⟩
  rw [hm, hm']
  exact (cut.position_moveInputPos h.1 m hside).symm

/-- Simulate a run segment in which every step stays on a retained side of the cut. -/
lemma reaches_runFrom (hsym : input[cut.fst] = input[cut.snd])
    {cfg : Cfg k Symbol State input} {c' : Cfg k Symbol State cut.shortened} {u v : ℕ}
    (h : cut.Matches (tm.runFrom cfg u) c') (huv : u ≤ v)
    (hside : ∀ t, u ≤ t → t < v →
      cut.SameSide (tm.runFrom cfg t).inputPos.val (tm.runFrom cfg (t + 1)).inputPos.val) :
    ∃ d, ReflTransGen tm.TransitionRelation c' d ∧ cut.Matches (tm.runFrom cfg v) d := by
  induction v, huv using Nat.le_induction with
  | base => exact ⟨c', .refl, h⟩
  | succ v huv ih =>
    obtain ⟨d, hd, hm⟩ := ih fun t hut htv => hside t hut (by omega)
    refine ⟨tm.step d, hd.tail rfl, ?_⟩
    rw [runFrom_succ_eq_step']
    exact hm.step hsym (by simpa only [runFrom_succ_eq_step'] using hside v huv (by omega))

end Matches

/-- The initial configurations match because the cut retains the first input symbol. -/
lemma matches_init : cut.Matches (tm.initCfg input) (tm.initCfg cut.shortened) := by
  constructor
  · exact (cut.position_left (p := 1) (Nat.succ_le_succ (Nat.zero_le _))).symm
  · rfl

/-- Equal storages at the two boundary positions match the same shortened configurations. -/
private lemma matches_boundary_iff
    {c₁ c₂ : Cfg k Symbol State input} {c' : Cfg k Symbol State cut.shortened}
    (h₁ : c₁.inputPos.val = cut.left) (h₂ : c₂.inputPos.val = cut.right)
    (hs : c₁.storage = c₂.storage) : cut.Matches c₁ c' ↔ cut.Matches c₂ c' := by
  have hba : cut.right - (cut.right - cut.left) = cut.left :=
    Nat.sub_sub_self (Nat.add_le_add_right cut.fst_le_snd 1)
  simp only [Matches, h₁, h₂, cut.position_left le_rfl, cut.position_right le_rfl,
    hba, hs]

/-- Of two boundary configurations with equal storage, at least one steps into a retained side. -/
private lemma step_boundary_sides (hsym : input[cut.fst] = input[cut.snd])
    {c₁ c₂ : Cfg k Symbol State input}
    (h₁ : c₁.inputPos.val = cut.left) (h₂ : c₂.inputPos.val = cut.right)
    (hs : c₁.storage = c₂.storage) :
    (tm.step c₁).inputPos.val ≤ cut.left ∨ cut.right ≤ (tm.step c₂).inputPos.val := by
  have hsy : c₁.inputSymbol = c₂.inputSymbol := by
    rw [inputSymbol_eq_getElem?, inputSymbol_eq_getElem?, h₁, h₂]
    simpa [left, right, Fin.getElem_fin] using hsym
  obtain ⟨dir, _, hm₁, hm₂⟩ := tm.exists_step_move_of_storage_eq hs hsy
  have hm := moveInputPos_interior c₁.inputPos c₂.inputPos
    (by rw [h₁]; exact Nat.succ_pos _) (by rw [h₁]; exact cut.fst.isLt)
    (by rw [h₂]; exact Nat.succ_pos _) (by rw [h₂]; exact cut.snd.isLt) dir
  rw [← hm₁, ← hm₂, h₁, h₂] at hm
  omega

/-- Paired boundary visits have reachable matching configurations: at each pair, follow the
next excursion on whichever side its first step retains. -/
private lemma exists_matches_visit {T : ℕ}
    (hsym : input[cut.fst] = input[cut.snd])
    (hseq : tm.visitSequence (tm.initCfg input) T cut.left =
      tm.visitSequence (tm.initCfg input) T cut.right)
    {t : ℕ} (ht : t ≤ T)
    (hp : (tm.runFrom (tm.initCfg input) t).inputPos.val = cut.left ∨
      (tm.runFrom (tm.initCfg input) t).inputPos.val = cut.right) :
    ∃ c', ReflTransGen tm.TransitionRelation (tm.initCfg cut.shortened) c' ∧
      cut.Matches (tm.runFrom (tm.initCfg input) t) c' := by
  let c := tm.runFrom (tm.initCfg input)
  let p := fun u => (c u).inputPos.val
  let P := fun u => ∃ c',
    ReflTransGen tm.TransitionRelation (tm.initCfg cut.shortened) c' ∧ cut.Matches (c u) c'
  obtain ⟨e, hstore⟩ := tm.exists_visitTimes_orderIso hseq
  have hleft (u : tm.visitTimes (tm.initCfg input) T cut.left) :=
    (tm.mem_visitTimes.mp u.property).2
  have hright (u : tm.visitTimes (tm.initCfg input) T cut.right) :=
    (tm.mem_visitTimes.mp u.property).2
  have hmatch (u : tm.visitTimes (tm.initCfg input) T cut.left) : P u ↔ P (e u) :=
    exists_congr fun c' => and_congr_right fun _ =>
      cut.matches_boundary_iff (hleft u) (hright (e u)) (hstore u)
  have follow {u v} (huv : u ≤ v) (hu : P u)
      (hside : ∀ r, u ≤ r → r < v → cut.SameSide (p r) (p (r + 1))) : P v := by
    obtain ⟨c', hr, hm⟩ := hu
    obtain ⟨d, hd, hm'⟩ := hm.reaches_runFrom hsym huv hside
    exact ⟨d, hr.trans hd, hm'⟩
  have boundary (u : tm.visitTimes (tm.initCfg input) T cut.left) : P u := by
    induction u using WellFoundedLT.induction with | ind u ih =>
    by_cases hu : IsMin u
    · have hside (v) (hv : v ≤ u.val) : p v ≤ cut.left := by
        apply tm.inputPos_le_of_forall_ne (Nat.zero_le v) (by simp [left])
        intro r _ hrv
        exact not_visit_before hu (hrv.trans_le hv)
      exact follow (Nat.zero_le _) ⟨_, .refl, cut.matches_init⟩ fun v _ hv =>
        Or.inl ⟨hside v hv.le, hside (v + 1) hv⟩
    · obtain ⟨v, hvu⟩ := exists_covBy_of_wellFoundedGT hu
      have hdir := cut.step_boundary_sides hsym (tm := tm) (hleft v) (hright (e v))
        (hstore v)
      simp only [← runFrom_succ_eq_step'] at hdir
      rcases hdir with hdir | hdir
      · have hside := inputPos_le_of_covBy hvu hdir
        exact follow hvu.le (ih v hvu.lt) fun r hlo hhi =>
          Or.inl ⟨hside r hlo hhi.le, hside (r + 1) (hlo.trans (Nat.le_succ _)) hhi⟩
      · have he := (apply_covBy_apply_iff e).mpr hvu
        have hside := le_inputPos_of_covBy he hdir
        exact (hmatch u).mpr (follow he.le ((hmatch v).mp (ih v hvu.lt)) fun r hlo hhi =>
          Or.inr ⟨hside r hlo hhi.le, hside (r + 1) (hlo.trans (Nat.le_succ _)) hhi⟩)
  rcases hp with hp | hp
  · exact boundary ⟨t, tm.mem_visitTimes.mpr ⟨ht, hp⟩⟩
  · let u : tm.visitTimes (tm.initCfg input) T cut.right := ⟨t, tm.mem_visitTimes.mpr ⟨ht, hp⟩⟩
    simpa only [e.apply_symm_apply] using (hmatch (e.symm u)).mp (boundary (e.symm u))

/-- Equal boundary visit sequences give every configuration outside the cut a reachable
matching configuration on the shortened input. -/
theorem exists_matches_of_visitSequence_eq {T : ℕ}
    (hsym : input[cut.fst] = input[cut.snd])
    (hseq : tm.visitSequence (tm.initCfg input) T cut.left =
      tm.visitSequence (tm.initCfg input) T cut.right)
    {t : ℕ} (ht : t ≤ T)
    (hp : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ cut.left ∨
      cut.right ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val) :
    ∃ c', ReflTransGen tm.TransitionRelation (tm.initCfg cut.shortened) c' ∧
      cut.Matches (tm.runFrom (tm.initCfg input) t) c' := by
  induction t with
  | zero => exact ⟨_, .refl, cut.matches_init⟩
  | succ t ih =>
    by_cases hb : (tm.runFrom (tm.initCfg input) (t + 1)).inputPos.val = cut.left ∨
        (tm.runFrom (tm.initCfg input) (t + 1)).inputPos.val = cut.right
    · exact cut.exists_matches_visit hsym hseq ht hb
    have hbounds := tm.inputPos_step_bounds (tm.runFrom (tm.initCfg input) t)
    have hside : cut.SameSide (tm.runFrom (tm.initCfg input) t).inputPos.val
        (tm.runFrom (tm.initCfg input) (t + 1)).inputPos.val := by
      dsimp only [SameSide]
      rw [← runFrom_succ_eq_step'] at hbounds
      omega
    obtain ⟨c', hr, hm⟩ := ih (by omega) (hside.imp And.left And.left)
    refine ⟨tm.step c', hr.tail rfl, ?_⟩
    rw [runFrom_succ_eq_step']
    exact hm.step hsym (by simpa only [runFrom_succ_eq_step'] using hside)

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
  obtain ⟨c', hr, _, hs⟩ := cut.exists_matches_of_visitSequence_eq hsym hseq ht hp
  obtain ⟨u, hu⟩ := hr.relatesInSteps
  refine ⟨u, ?_⟩
  rwa [(tm.relatesInSteps_iff_runFrom_eq _ _ _).mp hu]

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
