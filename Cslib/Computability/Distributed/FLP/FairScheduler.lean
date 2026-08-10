/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.FLP.Consensus
public import Cslib.Foundations.Data.OmegaSequence.InfOcc
public import Mathlib.Data.List.ReduceOption

/-! # Machinery for constructing infinite fair executions

The main goal of this file is to define a `fairScheduler` that, given a function `d`
of type `DeliverMsg`, a state predicate `q`, and a state `s0` of an algorithm `a`,
constructs an infinite execution of `a` starting from state `s0` in which all processes
from a set `ps` are fair and `q` is true infinitely often.  With additional assumptions,
we may also want to require that all actions in the infinite execution satisfy an action
predicate `r`.
-/

@[expose] public section

namespace Cslib.FLP

open Function Set Multiset Filter ωSequence

variable {P M S : Type*} [DecidableEq P] [DecidableEq M]

/-- Given a state `s` and a message `m`, a function `d` of type `DeliverMsg` is supposed to
return `(xs, t)` where `xs` is a finite execution from `s` to `t` in which `m` is delivered. -/
def DeliverMsg P M S := State P M S → Message P M → List (Action P M) × State P M S

/-- `d.ForallActions r` requires that all actions returned by `d` satisfy `r`. -/
def DeliverMsg.ForallActions (d : DeliverMsg P M S) (r : Action P M → Prop) : Prop :=
  ∀ s m, (d s m).fst.Forall r

/-- `d.foldList s ml ms` uses `d` to deliver all messages that are in `ml` but not in `ms` from
state `s`. Note that if a message `m` in `ml` is delivered during the delivery of an earlier
message, `m` is added to `ms` so that it is not processed again. -/
def DeliverMsg.foldList (d : DeliverMsg P M S) (s : State P M S) :
    List (Message P M) → Finset (Message P M) → List (Action P M) × State P M S
  | [], _ => ([], s)
  | m :: ml, ms =>
    if m ∈ ms then
      d.foldList s ml ms
    else
      let (xl1, s1) := d s m
      let ms' := ms ∪ xl1.reduceOption.toFinset
      let (xl2, s2) := d.foldList s1 ml ms'
      (xl1 ++ xl2, s2)

open scoped Classical in
/-- `d.scheduleMsgs ps s` schedules and delivers all messages which are in-flight in state `s`
and have destinations in `ps` in some order (as determined by choice).  If no such message exists,
then the the stuttering step is taken. -/
noncomputable def DeliverMsg.scheduleMsgs (d : DeliverMsg P M S) (ps : Set P)
    (s : State P M S) : List (Action P M) × State P M S :=
  let ms := s.msgs.filter (fun m ↦ m.dest ∈ ps)
  if ms = 0 then
    ([none], s)
  else
    d.foldList s ms.toList ∅

namespace DeliverMsg

variable {d : DeliverMsg P M S}

/-- If `d.ForallActions r`, then `d.foldList s ml ms` can only use actions satisfying `r`. -/
theorem foldList_forallActions {r : Action P M → Prop}
    (s : State P M S) (ml : List (Message P M)) (ms : Finset (Message P M))
    (h : d.ForallActions r) : (d.foldList s ml ms).fst.Forall r := by
  induction ml generalizing s ms <;>
    grind [DeliverMsg.foldList, DeliverMsg.ForallActions, List.Forall, List.forall_append]

end DeliverMsg

/-- Starting from state `s0`, `a.fairSchedular d ps s0` constructs an infinite sequence of
finite executions of `a` by repeatedly applying `d.scheduleMsgs ps`. -/
noncomputable def Algorithm.fairScheduler (a : Algorithm P M S) (d : DeliverMsg P M S) (ps : Set P)
    (s0 : State P M S) : ℕ → List (Action P M) × State P M S
  | 0 => ([], s0)
  | k + 1 => d.scheduleMsgs ps (a.fairScheduler d ps s0 k).snd

/-- The infinite sequence of states forming the end states of the finite executions constructed
by `Algorithm.fairScheduler`. -/
noncomputable def Algorithm.fairSegEnds (a : Algorithm P M S) (d : DeliverMsg P M S)
    (ps : Set P) (s0 : State P M S) : ωSequence (State P M S) :=
  ωSequence.mk (fun k ↦ (a.fairScheduler d ps s0 k).snd)

/-- The infinite sequence of finite action sequences from the finite executions constructed
by `Algorithm.fairScheduler`. -/
noncomputable def Algorithm.fairSegActions (a : Algorithm P M S) (d : DeliverMsg P M S)
    (ps : Set P) (s0 : State P M S) : ωSequence (List (Action P M)) :=
  (ωSequence.mk (fun k ↦ (a.fairScheduler d ps s0 k).fst)).tail

/-- `a.FairDeliverMsg d ps q` says that for any state `s` of `a` satisfying `q` and
any message `m` which is in-flight in `s` and whose destination is in `ps`, `d s m`
produces a legal finite execution of `a` in which `m` is delivered and which ends in
a state satisfying `q` again. -/
def Algorithm.FairDeliverMsg (a : Algorithm P M S) (d : DeliverMsg P M S)
    (ps : Set P) (q : State P M S → Prop) : Prop :=
  ∀ s m, m ∈ s.msgs ∧ m.dest ∈ ps ∧ q s →
    let (xl, t) := d s m
    a.lts.MTr s xl t ∧ some m ∈ xl ∧ q t

namespace FairScheduler

variable {a : Algorithm P M S}

/-- Re-stating the definition of `Algorithm.fairScheduler` as a mutual recursion of
`Algorithm.fairSegEnds` and `Algorithm.fairSegActions`. -/
theorem fairScheduler_init {d : DeliverMsg P M S} (ps : Set P) (s0 : State P M S) :
    a.fairSegEnds d ps s0 0 = s0 := by
  grind [Algorithm.fairScheduler, Algorithm.fairSegEnds]

/-- Re-stating the definition of `Algorithm.fairScheduler` as a mutual recursion of
`Algorithm.fairSegEnds` and `Algorithm.fairSegActions`. -/
theorem fairScheduler_step {d : DeliverMsg P M S} (ps : Set P) (s0 : State P M S) (k : ℕ) :
    d.scheduleMsgs ps (a.fairSegEnds d ps s0 k) =
    (a.fairSegActions d ps s0 k, a.fairSegEnds d ps s0 (k + 1)) := by
  grind [Algorithm.fairScheduler, Algorithm.fairSegEnds, Algorithm.fairSegActions]

/-- If `d.ForallActions r`, then `a.fairSegActions d ps s0` can only use actions satisfying `r`. -/
theorem fairSeg_forallActions {d : DeliverMsg P M S} {r : Action P M → Prop}
    (ps : Set P) (s0 : State P M S) (k : ℕ) (ha : d.ForallActions r) (hn : r none) :
    (a.fairSegActions d ps s0 k).Forall r := by
  grind [fairScheduler_step (a := a) (d := d) ps s0 k,
    DeliverMsg.scheduleMsgs, DeliverMsg.foldList_forallActions, List.Forall]

/-- The correctness of `d.foldList s ml ms` under the assumption `a.FairDeliverMsg d ps q`. -/
theorem fairDeliverMsg_foldList {d : DeliverMsg P M S} {ps : Set P} {q : State P M S → Prop}
    (hd : a.FairDeliverMsg d ps q) (s : State P M S)
    (ml : List (Message P M)) (ms : Finset (Message P M))
    (hs : q s ∧ ∀ m, m ∈ ml → ¬ m ∈ ms → m ∈ s.msgs ∧ m.dest ∈ ps) :
    let (xl, t) := d.foldList s ml ms
    a.lts.MTr s xl t ∧ q t ∧ ∀ m, m ∈ ml → ¬ m ∈ ms → some m ∈ xl := by
  induction ml generalizing s ms
  case nil => grind [DeliverMsg.foldList, LTS.MTr]
  case cons m ml h_ind =>
    by_cases h_m : m ∈ ms
    · grind [DeliverMsg.foldList]
    · let xl1 := (d s m).fst
      let s1 := (d s m).snd
      let ms' := ms ∪ xl1.reduceOption.toFinset
      have (m' : Message P M) : m' ∈ xl1.reduceOption.toFinset ↔ some m' ∈ xl1 := by
        simp [List.mem_toFinset, List.reduceOption_mem_iff]
      have (m' : Message P M) : m' ∈ ml → ¬ m' ∈ ms' → m' ∈ s1.msgs := by
        grind [Algorithm.FairDeliverMsg, Algorithm.mTr_notRcvd_enabled]
      grind [DeliverMsg.foldList, Algorithm.FairDeliverMsg, LTS.MTr.comp]

/-- The correctness of `d.scheduleMsgs ps s` under the assumption `a.FairDeliverMsg d ps q`. -/
theorem fairDeliverMsg_scheduleMsgs {d : DeliverMsg P M S} {ps : Set P} {q : State P M S → Prop}
    (hd : a.FairDeliverMsg d ps q) (s : State P M S) (hs : q s) :
    let xl := (d.scheduleMsgs ps s).fst
    let t := (d.scheduleMsgs ps s).snd
    q t ∧ a.lts.MTr s xl t ∧ xl.length > 0 ∧ ∀ m, m ∈ s.msgs → m.dest ∈ ps → some m ∈ xl := by
  classical
  intro xl t
  let ms := s.msgs.filter (fun m ↦ m.dest ∈ ps)
  by_cases h_ms : ms = 0
  · have h1 : xl = [none] ∧ t = s := by grind [DeliverMsg.scheduleMsgs]
    simp [ms, eq_zero_iff_forall_notMem] at h_ms
    simp only [h1, hs, List.length_cons, List.length_nil, zero_add, Order.lt_one_iff, true_and]
    split_ands
    · apply LTS.MTr.single
      grind [Algorithm.lts]
    · grind
  · have : q t ∧ a.lts.MTr s xl t ∧ ∀ m, m ∈ ms.toList → some m ∈ xl := by
      grind [DeliverMsg.scheduleMsgs, fairDeliverMsg_foldList hd s ms.toList ∅ (by simp [ms, hs])]
    obtain ⟨m, _⟩ := exists_mem_of_ne_zero h_ms
    have : some m ∈ xl := by grind [mem_toList]
    split_ands <;> grind [mem_toList, mem_filter]

/-- The correctness of `a.fairSegEnds d ps s0` and `a.fairSegActions d ps s0`
under the assumption `a.FairDeliverMsg d ps q`. -/
theorem fair_fairSegs {d : DeliverMsg P M S} {ps : Set P} {q : State P M S → Prop}
    (hd : a.FairDeliverMsg d ps q) (s0 : State P M S) (hs0 : q s0) :
    let ts := a.fairSegEnds d ps s0
    let xls := a.fairSegActions d ps s0
    ∀ k, q (ts k) ∧ a.lts.MTr (ts k) (xls k) (ts (k + 1)) ∧ (xls k).length > 0 ∧
      ∀ m, m ∈ (ts k).msgs → m.dest ∈ ps → some m ∈ xls k := by
  classical
  intro ts xls k
  induction k <;> grind [fairScheduler_init, fairScheduler_step, fairDeliverMsg_scheduleMsgs]

/-- Given an infinite sequence of non-empty finite executions of algorithm `a`,
if all messages with destinations in `ps` that are in-flight at the beginning of each
finite execution are delivered in that finite execution, then those finite executions can
be concatenated into an infinite execution of `a` in which every process in `ps` is fair. -/
theorem flatten_fairSegs {ps : Set P}
    {ts : ωSequence (State P M S)} {xls : ωSequence (List (Action P M))}
    (hmtr : ∀ k, a.lts.MTr (ts k) (xls k) (ts (k + 1)))
    (hpos : ∀ k, (xls k).length > 0)
    (hsch : ∀ k m, m ∈ (ts k).msgs → m.dest ∈ ps → some m ∈ xls k) :
    ∃ ss, a.lts.OmegaExecution ss xls.flatten ∧ (∀ k, ss (xls.cumLen k) = ts k) ∧
      ∀ p, p ∈ ps → ProcFair p ss xls.flatten := by
  obtain ⟨ss, h_omega, h_ts⟩ := LTS.OmegaExecution.flatten_mTr hmtr hpos
  use ss, h_omega, h_ts
  rintro p h_m m ⟨rfl⟩
  by_contra! ⟨k, h_k, h_k'⟩
  have h_xls : ∃ᶠ n in atTop, n ∈ xls.cumLen '' univ := by
    apply frequently_iff_strictMono.mpr
    use xls.cumLen
    grind [cumLen_strictMono]
  obtain ⟨j, _, h_j⟩ : ∃ j, k ≤ xls.cumLen j ∧ m ∈ (ts j).msgs := by
    obtain ⟨n, _, j, _, _⟩ := frequently_atTop.mp h_xls k
    grind [Algorithm.omega_notRcvd_enabled h_omega h_k h_k']
  obtain ⟨i, _, _⟩ := List.getElem_of_mem <| hsch j m h_j h_m
  grind [extract_flatten hpos j]

/-- Under the assumption `a.FairDeliverMsg d ps q`, the infinite sequence of finite executions
of `a` represented by `a.fairSegEnds d ps s0` and `a.fairSegActions d ps s0` can be concatenated
into an infinite execution of `a` in which every process in `ps` is fair and `q` is true at
the ends of all those finite executions. -/
theorem fair_omegaExecution {d : DeliverMsg P M S} {ps : Set P} {q : State P M S → Prop}
    (hd : a.FairDeliverMsg d ps q) (s0 : State P M S) (hs0 : q s0) :
    let ts := a.fairSegEnds d ps s0
    let xls := a.fairSegActions d ps s0
    ∃ ss, a.lts.OmegaExecution ss xls.flatten ∧
      ss 0 = s0 ∧ (∀ k, ss (xls.cumLen k) = ts k) ∧
      (∀ k, q (ss (xls.cumLen k))) ∧ (∀ k, (xls k).length > 0) ∧
      ∀ p, p ∈ ps → ProcFair p ss xls.flatten := by
  intro ts xls
  obtain ⟨h_q, hmtr, hpos, hsch⟩ :
      (∀ k, q (ts k)) ∧
      (∀ k, a.lts.MTr (ts k) (xls k) (ts (k + 1))) ∧
      (∀ k, (xls k).length > 0) ∧
      (∀ k m, m ∈ (ts k).msgs → m.dest ∈ ps → some m ∈ xls k) := by
    grind [fair_fairSegs hd s0 hs0]
  obtain ⟨ss, _, _, _⟩ := flatten_fairSegs hmtr hpos hsch
  have : ss 0 = s0 := by grind [fairScheduler_init]
  use ss
  grind

/-- If `d.ForallActions r`, then the concatenation of all `a.fairSegActions d ps s0` segments
can only use actions satisfying `r`. -/
theorem omega_forall_actions {d : DeliverMsg P M S} {ps : Set P}
    {q : State P M S → Prop} {r : Action P M → Prop}
    (hd : a.FairDeliverMsg d ps q) (s0 : State P M S) (hs0 : q s0)
    (ha : d.ForallActions r) (hn : r none) :
    ∀ k, r ((a.fairSegActions d ps s0).flatten k) := by
  have hpos : ∀ k, (a.fairSegActions d ps s0 k).length > 0 := by grind [fair_fairSegs hd s0 hs0]
  simp only [forall_flatten_iff hpos]
  grind [fairSeg_forallActions]

end FairScheduler

end Cslib.FLP
