/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import Mathlib.Data.Fintype.Pigeonhole
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

`InputCut.VisitPairing` pairs boundary visits in order with equal symbols and storages.
The shortened run first follows the retained prefix. Between consecutive pairs, the common
head move selects an excursion on a retained side. Induction over the pairs reaches every
boundary visit; subsequent retained steps reach every configuration outside the cut.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Relation Set

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

/-- Between consecutive visits, a first step to the left keeps the input head on the left. -/
private lemma inputPos_mapsTo_Iic_of_covBy {cfg : Cfg k Symbol State input} {T p : ℕ}
    {u v : tm.visitTimes cfg T p} (h : u ⋖ v)
    (hdir : (tm.runFrom cfg (u.val + 1)).inputPos.val ≤ p) :
    MapsTo (fun t => (tm.runFrom cfg t).inputPos.val) (Icc u.val v.val) (Iic p) := by
  have hT := (tm.mem_visitTimes.mp v.property).1
  rintro t ⟨hut, htv⟩
  rcases eq_or_lt_of_le hut with rfl | hut
  · exact (tm.mem_visitTimes.mp u.property).2.le
  · apply tm.inputPos_le_of_forall_ne hut hdir
    intro r hur hrt hp
    exact h.2 (c := ⟨r, tm.mem_visitTimes.mpr ⟨by omega, hp⟩⟩)
      (Nat.lt_of_succ_le hur) (hrt.trans_le htv)

/-- Between consecutive visits, a first step to the right keeps the input head on the right. -/
private lemma inputPos_mapsTo_Ici_of_covBy {cfg : Cfg k Symbol State input} {T p : ℕ}
    {u v : tm.visitTimes cfg T p} (h : u ⋖ v)
    (hdir : p ≤ (tm.runFrom cfg (u.val + 1)).inputPos.val) :
    MapsTo (fun t => (tm.runFrom cfg t).inputPos.val) (Icc u.val v.val) (Ici p) := by
  have hT := (tm.mem_visitTimes.mp v.property).1
  rintro t ⟨hut, htv⟩
  rcases eq_or_lt_of_le hut with rfl | hut
  · exact (tm.mem_visitTimes.mp u.property).2.ge
  · apply tm.le_inputPos_of_forall_ne hut hdir
    intro r hur hrt hp
    exact h.2 (c := ⟨r, tm.mem_visitTimes.mpr ⟨by omega, hp⟩⟩)
      (Nat.lt_of_succ_le hur) (hrt.trans_le htv)

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

/-- A one-cell move ending outside the cut, away from its boundaries, stays on a retained side. -/
lemma sameSide_of_not_boundary {p q : ℕ} (hstep : q ≤ p + 1 ∧ p ≤ q + 1)
    (hq : q ≤ cut.left ∨ cut.right ≤ q) (hne : ¬ (q = cut.left ∨ q = cut.right)) :
    cut.SameSide p q := by
  dsimp only [SameSide]
  omega

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

/-- Matching configurations on the retained prefix scan the same symbol. -/
lemma inputSymbol_left {c : Cfg k Symbol State input} {c' : Cfg k Symbol State cut.shortened}
    (h : cut.Matches c c') (hp : c.inputPos.val ≤ cut.left) :
    c.inputSymbol = c'.inputSymbol := by
  have hi : c.inputPos.val - 1 < cut.left := by
    have : 0 < cut.left := Nat.succ_pos _
    omega
  simp only [inputSymbol_eq_getElem?, h.1, cut.position_left hp, cut.getElem?_left hi]

/-- Matching configurations scanning the same symbol stay matched across a retained step. -/
lemma step {c : Cfg k Symbol State input} {c' : Cfg k Symbol State cut.shortened}
    (h : cut.Matches c c') (hsym : c.inputSymbol = c'.inputSymbol)
    (hside : cut.SameSide c.inputPos.val (tm.step c).inputPos.val) :
    cut.Matches (tm.step c) (tm.step c') := by
  obtain ⟨m, hs, hm, hm'⟩ := tm.exists_step_move_of_storage_eq h.2.symm hsym
  rw [hm] at hside
  refine ⟨?_, hs.symm⟩
  rw [hm, hm']
  exact (cut.position_moveInputPos h.1 m hside).symm

/-- Simulate a segment in the retained prefix, without any assumption on the boundary symbols. -/
lemma reaches_runFrom_left
    {cfg : Cfg k Symbol State input} {c' : Cfg k Symbol State cut.shortened} {u v : ℕ}
    (h : cut.Matches (tm.runFrom cfg u) c') (huv : u ≤ v)
    (hside : MapsTo (fun t => (tm.runFrom cfg t).inputPos.val) (Icc u v) (Iic cut.left)) :
    ∃ d, ReflTransGen tm.TransitionRelation c' d ∧ cut.Matches (tm.runFrom cfg v) d := by
  induction v, huv using Nat.le_induction with
  | base => exact ⟨c', .refl, h⟩
  | succ v huv ih =>
    obtain ⟨d, hd, hm⟩ := ih (hside.mono_left (Icc_subset_Icc_right (Nat.le_succ _)))
    have hv := hside ⟨huv, Nat.le_succ _⟩
    refine ⟨tm.step d, hd.tail rfl, ?_⟩
    rw [runFrom_succ_eq_step']
    exact hm.step (hm.inputSymbol_left hv) (.inl ⟨hv, by
      simpa only [mem_Iic, runFrom_succ_eq_step'] using hside ⟨by omega, le_rfl⟩⟩)

/-- Simulate a segment in the retained suffix when the boundary symbols agree. -/
lemma reaches_runFrom_right (hsym : input[cut.fst] = input[cut.snd])
    {cfg : Cfg k Symbol State input} {c' : Cfg k Symbol State cut.shortened} {u v : ℕ}
    (h : cut.Matches (tm.runFrom cfg u) c') (huv : u ≤ v)
    (hside : MapsTo (fun t => (tm.runFrom cfg t).inputPos.val) (Icc u v) (Ici cut.right)) :
    ∃ d, ReflTransGen tm.TransitionRelation c' d ∧ cut.Matches (tm.runFrom cfg v) d := by
  induction v, huv using Nat.le_induction with
  | base => exact ⟨c', .refl, h⟩
  | succ v huv ih =>
    obtain ⟨d, hd, hm⟩ := ih (hside.mono_left (Icc_subset_Icc_right (Nat.le_succ _)))
    have hv := hside ⟨huv, Nat.le_succ _⟩
    refine ⟨tm.step d, hd.tail rfl, ?_⟩
    rw [runFrom_succ_eq_step']
    exact hm.step (hm.inputSymbol hsym (.inr hv)) (.inr ⟨hv, by
      simpa only [mem_Ici, runFrom_succ_eq_step'] using hside ⟨by omega, le_rfl⟩⟩)

end Matches

/-- The initial configurations match because the cut retains the first input symbol. -/
lemma matches_init : cut.Matches (tm.initCfg input) (tm.initCfg cut.shortened) := by
  constructor
  · exact (cut.position_left (p := 1) (Nat.succ_le_succ (Nat.zero_le _))).symm
  · rfl

/-- An order-preserving pairing of boundary visits with equal symbols and storages. -/
structure VisitPairing (tm : MultiTapeTM k Symbol State) (T : ℕ) where
  /-- The paired boundary positions carry the same input symbol. -/
  symbol_eq : input[cut.fst] = input[cut.snd]
  /-- The visits to the two boundaries correspond in chronological order. -/
  orderIso : tm.visitTimes (tm.initCfg input) T cut.left ≃o
    tm.visitTimes (tm.initCfg input) T cut.right
  /-- Corresponding visits have the same storage. -/
  storage_eq (u : tm.visitTimes (tm.initCfg input) T cut.left) :
    (tm.runFrom (tm.initCfg input) u).storage =
      (tm.runFrom (tm.initCfg input) (orderIso u)).storage

/-- The retained prefix reaches the first visit to the left boundary. -/
private lemma exists_matches_first_visit {T : ℕ}
    {u : tm.visitTimes (tm.initCfg input) T cut.left} (hu : IsMin u) :
    ∃ c', ReflTransGen tm.TransitionRelation (tm.initCfg cut.shortened) c' ∧
      cut.Matches (tm.runFrom (tm.initCfg input) u) c' := by
  apply cut.matches_init.reaches_runFrom_left (cfg := tm.initCfg input) (u := 0) (Nat.zero_le _)
  have hT := (tm.mem_visitTimes.mp u.property).1
  rintro v ⟨_, hv⟩
  apply tm.inputPos_le_of_forall_ne (Nat.zero_le v) (by simp [left])
  intro r _ hrv hp
  exact hu.not_lt (b := ⟨r, tm.mem_visitTimes.mpr ⟨by omega, hp⟩⟩) (hrv.trans_le hv)

namespace VisitPairing

variable {cut} {T : ℕ} (pairing : cut.VisitPairing tm T)

include pairing

/-- Paired visits represent the same storage at the collapsed boundary. -/
private lemma matches_iff (u : tm.visitTimes (tm.initCfg input) T cut.left)
    {c' : Cfg k Symbol State cut.shortened} :
    cut.Matches (tm.runFrom (tm.initCfg input) u) c' ↔
      cut.Matches (tm.runFrom (tm.initCfg input) (pairing.orderIso u)) c' := by
  have hleft := (tm.mem_visitTimes.mp u.property).2
  have hright := (tm.mem_visitTimes.mp (pairing.orderIso u).property).2
  have hba : cut.right - (cut.right - cut.left) = cut.left :=
    Nat.sub_sub_self (Nat.add_le_add_right cut.fst_le_snd 1)
  simp only [Matches, hleft, hright, cut.position_left le_rfl,
    cut.position_right le_rfl, hba, pairing.storage_eq u]

/-- At a paired visit, at least one of the two next steps enters a retained side. -/
private lemma step_sides (u : tm.visitTimes (tm.initCfg input) T cut.left) :
    (tm.runFrom (tm.initCfg input) (u.val + 1)).inputPos.val ≤ cut.left ∨
      cut.right ≤ (tm.runFrom (tm.initCfg input) ((pairing.orderIso u).val + 1)).inputPos.val := by
  have hleft := (tm.mem_visitTimes.mp u.property).2
  have hright := (tm.mem_visitTimes.mp (pairing.orderIso u).property).2
  have hsym : (tm.runFrom (tm.initCfg input) u).inputSymbol =
      (tm.runFrom (tm.initCfg input) (pairing.orderIso u)).inputSymbol := by
    rw [inputSymbol_eq_getElem?, inputSymbol_eq_getElem?, hleft, hright]
    simpa [left, right, Fin.getElem_fin] using pairing.symbol_eq
  obtain ⟨m, _, hm, hm'⟩ := tm.exists_step_move_of_storage_eq (pairing.storage_eq u) hsym
  rw [runFrom_succ_eq_step', runFrom_succ_eq_step', hm, hm',
    moveInputPos_val, moveInputPos_val, hleft, hright]
  have hb : cut.right ≤ input.length := cut.snd.isLt
  cases m <;> simp [SignType.cast]; omega

/-- Between consecutive paired visits, follow the excursion on a retained side. -/
private lemma reaches_next_visit {u v : tm.visitTimes (tm.initCfg input) T cut.left}
    (huv : u ⋖ v) {c' : Cfg k Symbol State cut.shortened}
    (h : cut.Matches (tm.runFrom (tm.initCfg input) u) c') :
    ∃ d, ReflTransGen tm.TransitionRelation c' d ∧
      cut.Matches (tm.runFrom (tm.initCfg input) v) d := by
  rcases pairing.step_sides u with hleft | hright
  · exact h.reaches_runFrom_left huv.le (inputPos_mapsTo_Iic_of_covBy huv hleft)
  · have he := (apply_covBy_apply_iff pairing.orderIso).mpr huv
    obtain ⟨d, hd, hm⟩ := ((pairing.matches_iff u).mp h).reaches_runFrom_right
      pairing.symbol_eq he.le (inputPos_mapsTo_Ici_of_covBy he hright)
    exact ⟨d, hd, (pairing.matches_iff v).mpr hm⟩

/-- Induct over the paired visits, starting with the retained prefix. -/
private lemma exists_matches_left_visit (u : tm.visitTimes (tm.initCfg input) T cut.left) :
    ∃ c', ReflTransGen tm.TransitionRelation (tm.initCfg cut.shortened) c' ∧
      cut.Matches (tm.runFrom (tm.initCfg input) u) c' := by
  induction u using WellFoundedLT.induction with | ind u ih =>
  by_cases hu : IsMin u
  · exact cut.exists_matches_first_visit hu
  · obtain ⟨v, hvu⟩ := exists_covBy_of_wellFoundedGT hu
    obtain ⟨c', hr, hm⟩ := ih v hvu.lt
    obtain ⟨d, hd, hm'⟩ := pairing.reaches_next_visit hvu hm
    exact ⟨d, hr.trans hd, hm'⟩

/-- Every boundary visit has a reachable matching configuration on the shortened input. -/
lemma exists_matches_visit
    (u : (tm.visitTimes (tm.initCfg input) T cut.left ∪
      tm.visitTimes (tm.initCfg input) T cut.right : Finset ℕ)) :
    ∃ c', ReflTransGen tm.TransitionRelation (tm.initCfg cut.shortened) c' ∧
      cut.Matches (tm.runFrom (tm.initCfg input) u) c' := by
  rcases Finset.mem_union.mp u.property with hu | hu
  · exact pairing.exists_matches_left_visit ⟨u.val, hu⟩
  · let v := pairing.orderIso.symm ⟨u.val, hu⟩
    obtain ⟨c', hr, hm⟩ := pairing.exists_matches_left_visit v
    exact ⟨c', hr, by
      simpa only [v, pairing.orderIso.apply_symm_apply] using (pairing.matches_iff v).mp hm⟩

/-- A pairing of boundary visits gives every configuration outside the cut a reachable
matching configuration on the shortened input. -/
theorem exists_matches {t : ℕ} (ht : t ≤ T)
    (hp : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ cut.left ∨
      cut.right ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val) :
    ∃ c', ReflTransGen tm.TransitionRelation (tm.initCfg cut.shortened) c' ∧
      cut.Matches (tm.runFrom (tm.initCfg input) t) c' := by
  induction t with
  | zero => exact ⟨_, .refl, cut.matches_init⟩
  | succ t ih =>
    by_cases hb : (tm.runFrom (tm.initCfg input) (t + 1)).inputPos.val = cut.left ∨
        (tm.runFrom (tm.initCfg input) (t + 1)).inputPos.val = cut.right
    · exact pairing.exists_matches_visit ⟨t + 1, by
        simp only [Finset.mem_union, tm.mem_visitTimes]
        exact hb.imp (fun h => ⟨ht, h⟩) (fun h => ⟨ht, h⟩)⟩
    have hbounds := tm.inputPos_step_bounds (tm.runFrom (tm.initCfg input) t)
    rw [← runFrom_succ_eq_step'] at hbounds
    have hside := cut.sameSide_of_not_boundary hbounds hp hb
    obtain ⟨c', hr, hm⟩ := ih (by omega) (hside.imp And.left And.left)
    refine ⟨tm.step c', hr.tail rfl, ?_⟩
    rw [runFrom_succ_eq_step']
    exact hm.step (hm.inputSymbol pairing.symbol_eq (hside.imp And.left And.left))
      (by simpa only [runFrom_succ_eq_step'] using hside)

end VisitPairing

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
  obtain ⟨e, hstore⟩ := tm.exists_visitTimes_orderIso hseq
  let pairing : cut.VisitPairing tm T := ⟨hsym, e, hstore⟩
  obtain ⟨c', hr, _, hs⟩ := pairing.exists_matches ht hp
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
  · simpa only [tm.runFrom_eq_of_halt _ (Nat.le_of_not_ge ht) hT] using this T le_rfl
  let B := storageBound Symbol State k s
  let S := Set.range (fun u => (tm.runFrom (tm.initCfg input) u).storage)
  have hbound : S.encard ≤ B := tm.encard_storages_le hs
  let : Fintype S := (Set.finite_of_encard_le_coe hbound).fintype
  have hcard : Fintype.card S ≤ B := by
    exact_mod_cast (Set.coe_fintypeCard (s := S)).le.trans hbound
  let seq := tm.visitSequence (tm.initCfg input) T
  let enc (p : ℕ) : List S := (seq p).attachWith (· ∈ S)
    (fun _ h => tm.mem_range_of_mem_visitSequence h)
  have henc (p : ℕ) : (enc p).map Subtype.val = seq p :=
    List.attachWith_map_subtype_val _
  have hlength (p : ℕ) : (enc p).length ≤ B := by
    simpa only [enc, List.length_attachWith] using tm.length_visitSequence_le hT hfirst hs p
  let p := (tm.runFrom (tm.initCfg input) t).inputPos.val
  -- Matching positions on the same side of `p` give a cut that avoids `p`.
  let f (i : Fin input.length) : Bool × Symbol × (Fin B → Option S) :=
    (decide (i.val + 1 < p), input[i], fun j => (enc (i.val + 1))[j.val]?)
  have hsig : Fintype.card (Bool × Symbol × (Fin B → Option S)) < input.length := by
    calc
      _ = 2 * Fintype.card Symbol * (Fintype.card S + 1) ^ B := by
        simp [mul_assoc]
      _ ≤ 2 * Fintype.card Symbol * (B + 1) ^ B := by gcongr; omega
      _ < input.length := hlen
  obtain ⟨i, j, hij, hf⟩ : ∃ i j, i < j ∧ f i = f j := by
    obtain ⟨i, j, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hsig)
    grind
  obtain ⟨hside, hsym, hseq⟩ := (by simpa only [f, Prod.mk.injEq, decide_eq_decide] using hf)
  have hseq' : enc (i.val + 1) = enc (j.val + 1) := by
    apply List.ext_getElem?
    intro r
    by_cases hr : r < B
    · exact congrFun hseq ⟨r, hr⟩
    · rw [List.getElem?_eq_none (by have := hlength (i.val + 1); omega),
        List.getElem?_eq_none (by have := hlength (j.val + 1); omega)]
  let cut : InputCut input := ⟨⟨i, j⟩, hij.le⟩
  refine ⟨cut.shortened, ?_, tm.exists_storage_cut cut hsym ?_ ht ?_⟩
  · have := cut.length_shortened_add
    change cut.shortened.length + (j.val + 1 - (i.val + 1)) = input.length at this
    omega
  · change seq (i.val + 1) = seq (j.val + 1)
    simpa only [henc] using congrArg (List.map Subtype.val) hseq'
  · change p ≤ i.val + 1 ∨ j.val + 1 ≤ p
    omega

end Turing.MultiTapeTM
