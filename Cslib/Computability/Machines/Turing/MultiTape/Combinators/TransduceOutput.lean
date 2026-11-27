/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.DA.Transducer
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Set.Finite.List

/-!
# Transducing the output of a machine

`tm.transduceOutput tr n` behaves like `tm`, but pipes its output through the subsequential
transducer `tr`. Each step of `tm` is performed together with emitting the first symbol of the
word that `tr` emits on the output of this step; the rest of the word is emitted one symbol per
step, with the input and work heads standing still. The word still to be emitted is stored in the
state, so it has to be of length at most `n`. On the step where `tm` halts, the final output of
`tr` is appended to this word, and the machine halts with its last symbol. A step of `tm` thus
takes at most `max 1 m` steps, where `m` bounds the words emitted on transitions, and the final
output adds its length.

## Main definitions

* `Turing.MultiTapeTM.transduceOutput`: the machine with transduced output.

## Main results

* `Turing.MultiTapeTM.ComputesInTimeAndSpace.transduceOutput`: if `tm` outputs `out` in time `t`
  and space `s`, and the words emitted by `tr` on transitions and at the end have length at most
  `m` and `l`, then `tm.transduceOutput tr (m + l)` outputs `tr.eval out` in time
  `max 1 m * t + l` and space `s`.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.transduce`: the same for computable functions.
-/

public section

namespace Turing.MultiTapeTM

open Cslib.Automata

variable {k : ℕ} {Symbol State StateT : Type*} {input : List Symbol}

/-- The output of `tr` on `w` from state `q`, including the final output if and only if
`halted` holds. -/
def transduced (tr : SubsequentialTransducer StateT Symbol Symbol) (halted : Bool) (q : StateT)
    (w : List Symbol) : List Symbol :=
  if halted then tr.evalFrom q w else tr.toSequentialTransducer.evalFrom q w

/-- The state of `tm.transduceOutput tr n` in which `w` is still to be emitted, where `s` is the
state of `tm` and `qT` the state of `tr`. If `tm` has halted and nothing is left to emit, this is
the halting state `none`. -/
def TransduceOutput.nextState {n : ℕ} (s : Option State) (qT : StateT) (w : List Symbol)
    (hw : w.length ≤ n) : Option ((Option State × StateT) × {w : List Symbol // w.length ≤ n}) :=
  if s.isNone && w.isEmpty then none else some ((s, qT), ⟨w, hw⟩)

open TransduceOutput in
/-- The machine that behaves like `tm`, but pipes its output through the subsequential
transducer `tr`. Its state consists of the state of `tm` (`none` once `tm` has halted), the state
of `tr`, and the word still to be emitted, of length at most `n`. If this word is nonempty, the
machine emits its first symbol. Otherwise, it performs the step of `tm`, computes the word that
`tr` emits on the output of this step (including the final output if `tm` halts), emits its first
symbol and stores the rest. The machine halts as soon as `tm` has halted and everything is
emitted. -/
noncomputable def transduceOutput (tm : MultiTapeTM k Symbol State)
    (tr : SubsequentialTransducer StateT Symbol Symbol) (n : ℕ) :
    MultiTapeTM k Symbol ((Option State × StateT) × {w : List Symbol // w.length ≤ n}) :=
  ofTr ((some tm.q₀, tr.start), ⟨[], by simp⟩) fun st inp work =>
    match st with
    | ((s, qT), ⟨b :: w, hw⟩) => ⟨0, fun _ => (none, 0), some b, nextState s qT w (by grind)⟩
    | ((none, _), ⟨[], _⟩) => ⟨0, fun _ => (none, 0), none, none⟩
    | ((some q, qT), ⟨[], _⟩) =>
      let a := tm.tr q inp work
      let w := (transduced tr a.state.isNone qT a.output.toList).take n
      ⟨a.inputTape, a.workTapes, w.head?,
        nextState a.state (a.output.toList.foldl tr.tr qT) w.tail (by grind)⟩

namespace TransduceOutput

variable (tr : SubsequentialTransducer StateT Symbol Symbol) {n m : ℕ}
  {tm : MultiTapeTM k Symbol State}

private lemma evalFrom_append (q : StateT) (x y : List Symbol) :
    tr.evalFrom q (x ++ y) =
      tr.toSequentialTransducer.evalFrom q x ++ tr.evalFrom (x.foldl tr.tr q) y := by
  induction x generalizing q <;> simp_all

@[simp]
private lemma transduced_true (q : StateT) (w : List Symbol) :
    transduced tr true q w = tr.evalFrom q w := rfl

@[simp]
private lemma transduced_false (q : StateT) (w : List Symbol) :
    transduced tr false q w = tr.toSequentialTransducer.evalFrom q w := rfl

variable {m l : ℕ} (hemit : ∀ q b, (tr.emit q b).length ≤ m)
  (hfinal : ∀ q, (tr.finalOut q).length ≤ l)
include hemit hfinal in
/-- The word that `tr` emits on the output of a step of `tm` is short. -/
private lemma length_transduced_le (halted : Bool) (q : StateT) (b : Option Symbol) :
    (transduced tr halted q b.toList).length ≤ m + if halted then l else 0 := by
  rcases b <;> cases halted <;> simp <;> grind

private lemma transduced_append (halted : Bool) (q : StateT) (x y : List Symbol) :
    transduced tr halted q (x ++ y) =
      tr.toSequentialTransducer.evalFrom q x ++ transduced tr halted (x.foldl tr.tr q) y := by
  cases halted
  · exact evalFrom_append tr.toSequentialTransducer.toSubsequential q x y
  · exact evalFrom_append tr q x y

private lemma runFrom_succ {tm : MultiTapeTM k Symbol State} (c : Cfg k Symbol State input)
    (t : ℕ) : tm.runFrom c (t + 1) = tm.step (tm.runFrom c t) :=
  Function.iterate_succ_apply' ..

private lemma runFrom_add {tm : MultiTapeTM k Symbol State} (c : Cfg k Symbol State input)
    (a b : ℕ) : tm.runFrom c (a + b) = tm.runFrom (tm.runFrom c a) b := by
  simp [runFrom, Nat.add_comm a b, Function.iterate_add_apply]

private lemma head?_toList_append_tail (w : List Symbol) : w.head?.toList ++ w.tail = w := by
  cases w <;> rfl

/-- Once a run path has halted, every configuration of the run from its head lies on it. -/
private lemma runFrom_mem {tm : MultiTapeTM k Symbol State} {p : tm.RunPath input}
    (h : p.last.Halted) (t : ℕ) : tm.runFrom p.head t ∈ p := by
  rcases le_or_gt t p.length with ht | ht
  · exact ⟨⟨t, by lia⟩, runPath_apply_eq_runFrom ..⟩
  · rw [runFrom_eq_of_halt _ _ ht.le (runPath_last_eq_runFrom p ▸ h), ← runPath_last_eq_runFrom]
    exact p.last_mem

@[simp]
lemma nextState_cons {s : Option State} {qT : StateT} {b : Symbol} {w : List Symbol}
    {hw : (b :: w).length ≤ n} : nextState s qT (b :: w) hw = some ((s, qT), ⟨b :: w, hw⟩) := by
  simp [nextState]

@[simp]
lemma nextState_some {q : State} {qT : StateT} {w : List Symbol} {hw : w.length ≤ n} :
    nextState (some q) qT w hw = some ((some q, qT), ⟨w, hw⟩) := by
  simp [nextState]

@[simp]
lemma nextState_none_nil {qT : StateT} {hw : [].length ≤ n} :
    nextState (State := State) (Symbol := Symbol) none qT [] hw = none := by
  simp [nextState]

lemma fst_of_mem_nextState {s : Option State} {qT : StateT} {w : List Symbol}
    {hw : w.length ≤ n} : ∀ x ∈ nextState s qT w hw, x.1.1 = s := by
  unfold nextState
  split <;> simp

/-- The configuration of `tm.transduceOutput tr n` with nothing to emit that simulates the
configuration `c` of `tm`. It is halted if `c` is. -/
def cfg (c : Cfg k Symbol State input) :
    Cfg k Symbol ((Option State × StateT) × {w : List Symbol // w.length ≤ n}) input :=
  ⟨nextState c.state (c.output.foldl tr.tr tr.start) [] (by simp), c.inputPos, c.workTapes,
    c.workTapePos, transduced tr c.state.isNone tr.start c.output⟩

section Steps

variable {e : Cfg k Symbol ((Option State × StateT) × {w : List Symbol // w.length ≤ n}) input}

/-- With a nonempty pending word, the machine emits its first symbol. -/
lemma step_of_pending {s : Option State} {qT : StateT} {b : Symbol} {w : List Symbol}
    {hw : (b :: w).length ≤ n} (he : e.state = some ((s, qT), ⟨b :: w, hw⟩)) :
    (tm.transduceOutput tr n).step e =
      { e with state := nextState s qT w (by grind), output := e.output ++ [b] } := by
  rw [step_of_state he, transduceOutput, tr_ofTr]
  ext <;> simp [Action.apply]

/-- With nothing pending, the machine halts once `tm` has halted. -/
lemma step_of_halted {qT : StateT} {hw : [].length ≤ n}
    (he : e.state = some ((none, qT), ⟨[], hw⟩)) :
    (tm.transduceOutput tr n).step e = { e with state := none } := by
  rw [step_of_state he, transduceOutput, tr_ofTr]
  ext <;> simp [Action.apply]

/-- With nothing pending, the machine performs the step `a` of `tm`, emits the first symbol of
the word that `tr` emits on the output of `a`, and stores the rest. -/
lemma step_of_running {q : State} {qT : StateT} {hw : [].length ≤ n}
    (he : e.state = some ((some q, qT), ⟨[], hw⟩)) {a : Action k Symbol State}
    (ha : tm.tr q e.inputSymbol e.workTapeSymbols = a) :
    (tm.transduceOutput tr n).step e =
      let w := (transduced tr a.state.isNone qT a.output.toList).take n
      Action.apply ⟨a.inputTape, a.workTapes, w.head?,
        nextState a.state (a.output.toList.foldl tr.tr qT) w.tail (by grind)⟩ e := by
  rw [step_of_state he, transduceOutput, tr_ofTr]
  ext <;> simp [Action.apply, ha]

/-- Emitting the pending word `w` takes `w.length` steps. -/
lemma runFrom_of_pending {s : Option State} {qT : StateT} {w : List Symbol} {hw : w.length ≤ n}
    (he : e.state = nextState s qT w hw) :
    (tm.transduceOutput tr n).runFrom e w.length =
      { e with state := nextState s qT [] (by simp), output := e.output ++ w } := by
  induction w generalizing e with
  | nil => simp [runFrom, ← he]
  | cons b w ih =>
    rw [List.length_cons, runFrom, Function.iterate_succ_apply, ← runFrom,
      ih (by rw [step_of_pending tr (he.trans nextState_cons)]),
      step_of_pending tr (he.trans nextState_cons)]
    simp

end Steps

include hemit hfinal in
/-- A step of `tm` is simulated by at most `max 1 m` steps, plus `l` steps if `tm` halts. -/
lemma exists_runFrom_cfg_step {c : Cfg k Symbol State input} (hc : ¬c.Halted) :
    ∃ j ≤ max 1 m + if (tm.step c).Halted then l else 0,
      (tm.transduceOutput tr (m + l)).runFrom (cfg tr c) j = cfg tr (tm.step c) := by
  obtain ⟨_ | q, pos, tapes, heads, out⟩ := c
  · exact absurd rfl hc
  set c : Cfg k Symbol State input := ⟨some q, pos, tapes, heads, out⟩
  set a := tm.tr q c.inputSymbol c.workTapeSymbols
  set w := transduced tr a.state.isNone (out.foldl tr.tr tr.start) a.output.toList
  have hw := length_transduced_le tr hemit hfinal a.state.isNone (out.foldl tr.tr tr.start) a.output
  have hw' : w.length ≤ m + l := hw.trans (by split <;> lia)
  have hc' : tm.step c = a.apply c := step_of_state rfl
  refine ⟨(w.take (m + l)).tail.length + 1, ?_, ?_⟩
  · rw [hc']
    simp only [List.take_of_length_le hw', List.length_tail, Cfg.Halted, Action.apply_state]
    split <;> simp_all <;> lia
  · rw [runFrom, Function.iterate_succ_apply, ← runFrom, step_of_running tr (a := a) rfl rfl,
      runFrom_of_pending tr rfl, hc']
    ext <;> simp [cfg, Action.apply, transduced_append, List.take_of_length_le hw',
      head?_toList_append_tail, w, c]

include hemit hfinal in
/-- `t` steps of `tm` are simulated by at most `max 1 m * t` steps, plus `l` steps if `tm`
halts. -/
lemma exists_runFrom_cfg (c : Cfg k Symbol State input) (t : ℕ) :
    ∃ j ≤ max 1 m * t + if (tm.runFrom c t).Halted then l else 0,
      (tm.transduceOutput tr (m + l)).runFrom (cfg tr c) j = cfg tr (tm.runFrom c t) := by
  induction t with
  | zero => exact ⟨0, by simp, rfl⟩
  | succ t ih =>
    obtain ⟨j, hj, h⟩ := ih
    rw [runFrom_succ, Nat.mul_succ]
    by_cases hc : (tm.runFrom c t).Halted
    · rw [step_of_halt hc]
      exact ⟨j, by lia, h⟩
    · obtain ⟨j', hj', h'⟩ := exists_runFrom_cfg_step tr hemit hfinal hc
      simp only [hc, ↓reduceIte] at hj
      exact ⟨j + j', by omega, by rw [runFrom_add, h, h']⟩

/-- The configuration `e` of `tm.transduceOutput tr n` has the heads and tapes of the
configuration `c` of `tm`, and it is halted or in the state of `c`. -/
def Tracks (c : Cfg k Symbol State input)
    (e : Cfg k Symbol ((Option State × StateT) × {w : List Symbol // w.length ≤ n}) input) :
    Prop :=
  e.inputPos = c.inputPos ∧ e.workTapes = c.workTapes ∧ e.workTapePos = c.workTapePos ∧
    ∀ x ∈ e.state, x.1.1 = c.state

/-- A step of `tm.transduceOutput tr n` keeps tracking `c` or tracks the successor of `c`. -/
lemma Tracks.step {c : Cfg k Symbol State input}
    {e : Cfg k Symbol ((Option State × StateT) × {w : List Symbol // w.length ≤ n}) input}
    (h : Tracks c e) :
    Tracks c ((tm.transduceOutput tr n).step e) ∨
      Tracks (tm.step c) ((tm.transduceOutput tr n).step e) := by
  obtain ⟨hi, hw, hp, hs⟩ := h
  rcases he : e.state with _ | ⟨⟨s, qT⟩, ⟨_ | ⟨b, w⟩, hw'⟩⟩
  · exact .inl (by rw [step_of_halt he]; exact ⟨hi, hw, hp, hs⟩)
  · obtain rfl : s = c.state := hs _ he
    rcases hq : c.state with _ | q
    · rw [hq] at he
      exact .inl (by simp [step_of_halted tr he, Tracks, hi, hw, hp])
    · rw [hq] at he
      have hi' : e.inputSymbol = c.inputSymbol := by simp [Cfg.inputSymbol, hi]
      have hw' : e.workTapeSymbols = c.workTapeSymbols := by
        funext; simp [Cfg.workTapeSymbols, hw, hp]
      refine .inr ?_
      rw [step_of_running tr he rfl, step_of_state hq, hi', hw']
      simpa [Tracks, Action.apply, hi, hw, hp] using fst_of_mem_nextState
  · refine .inl ?_
    rw [step_of_pending tr he]
    exact ⟨hi, hw, hp, hs _ he ▸ fst_of_mem_nextState⟩

/-- Every configuration of the run of `tm.transduceOutput tr n` from `cfg tr c` tracks a
configuration of the run of `tm` from `c`. -/
lemma exists_tracks_runFrom (c : Cfg k Symbol State input) (j : ℕ) :
    ∃ t, Tracks (tm.runFrom c t) ((tm.transduceOutput tr n).runFrom (cfg tr c) j) := by
  induction j with
  | zero => exact ⟨0, rfl, rfl, rfl, fst_of_mem_nextState⟩
  | succ j ih =>
    obtain ⟨t, h⟩ := ih
    rw [runFrom_succ]
    exact (h.step tr).elim (⟨t, ·⟩) fun h => ⟨t + 1, by rwa [runFrom_succ]⟩

end TransduceOutput

open TransduceOutput in
/-- If `tm` outputs `out` in time `t` and space `s`, and the words emitted by `tr` on its
transitions and at the end have length at most `m` and `l`, then `tm.transduceOutput tr (m + l)`
outputs `tr.eval out` in time `max 1 m * t + l` and space `s`. -/
theorem ComputesInTimeAndSpace.transduceOutput {tm : MultiTapeTM k Symbol State}
    (tr : SubsequentialTransducer StateT Symbol Symbol) {m l : ℕ}
    (hemit : ∀ q b, (tr.emit q b).length ≤ m) (hfinal : ∀ q, (tr.finalOut q).length ≤ l)
    {out : List Symbol} {t s : ℕ} (h : tm.ComputesInTimeAndSpace input out t s) :
    (tm.transduceOutput tr (m + l)).ComputesInTimeAndSpace input (tr.eval out)
      (max 1 m * t + l) s := by
  obtain ⟨p, hh, halt, rfl, ht, hs⟩ := computesInTimeAndSpace_iff_exists_runPath.mp h
  obtain ⟨j, hj, hrun⟩ := exists_runFrom_cfg tr hemit hfinal p.head p.length
  rw [← runPath_last_eq_runFrom] at hrun hj
  simp only [eq_true halt, ↓reduceIte] at hj
  have hlast : (MultiTapeNTM.RunPath.ofDeterministic _ (cfg tr p.head) j).last =
      cfg tr p.last := hrun
  refine computesInTimeAndSpace_iff_exists_runPath.mpr
    ⟨.ofDeterministic _ (cfg tr p.head) j, by rw [hh]; rfl, by rw [hlast]; simp [cfg, halt],
      by rw [hlast]; simp [cfg, halt], ?_, ?_⟩
  · exact hj.trans (by grw [ht])
  · refine (MultiTapeNTM.RunPath.space_le_sum_card _ (S := p.visitedByTapeHead) ?_).trans hs
    rintro _ ⟨i, rfl⟩ l
    obtain ⟨n, -, -, hn, -⟩ := exists_tracks_runFrom tr p.head i
    exact (p.mem_visitedByTapeHead).mpr ⟨_, runFrom_mem halt n, (congrFun hn l).symm⟩

/-- If `f` is computable in time `t` and space `s` with output encoding `encOut`, and the finite
subsequential transducer `tr` translates `encOut b` to `encOut' (g b)`, then `g ∘ f` is
computable in time `max 1 m * t + l` and space `s` with output encoding `encOut'`, where `m` and
`l` bound the lengths of the words emitted by `tr` on its transitions and at the end. -/
theorem ComputableInTimeAndSpace.transduce {α β γ : Type*} {f : α → β} {g : β → γ}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {encOut' : γ ↪ List Bool} {t s : α → ℕ}
    {StateT : Type} [Finite StateT] (tr : SubsequentialTransducer StateT Bool Bool) {m l : ℕ}
    (hemit : ∀ q b, (tr.emit q b).length ≤ m) (hfinal : ∀ q, (tr.finalOut q).length ≤ l)
    (hg : ∀ b, tr.eval (encOut b) = encOut' (g b))
    (h : ComputableInTimeAndSpace f encIn encOut t s) :
    ComputableInTimeAndSpace (g ∘ f) encIn encOut' (fun a => max 1 m * t a + l) s := by
  obtain ⟨k, State, _, tm, htm⟩ := h
  have := (List.finite_length_le Bool (m + l)).to_subtype
  exact ⟨k, _, inferInstance, tm.transduceOutput tr (m + l),
    fun a => hg (f a) ▸ (htm a).transduceOutput tr hemit hfinal⟩

end Turing.MultiTapeTM
