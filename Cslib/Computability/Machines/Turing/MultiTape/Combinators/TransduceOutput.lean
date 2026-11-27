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
def transduced (tr : SubsequentialTransducer StateT Symbol Symbol) :
    (halted : Bool) → StateT → List Symbol → List Symbol
  | true, q, w => tr.evalFrom q w
  | false, q, w => tr.toSequentialTransducer.evalFrom q w

attribute [simp] transduced.eq_1 transduced.eq_2

/-- A non-halting state of `tm.transduceOutput tr n`. -/
structure TransduceOutput.Control (State StateT Symbol : Type*) (n : ℕ) where
  /-- The state of `tm`, or `none` once `tm` has halted. -/
  tmState : Option State
  /-- The state of `tr`. -/
  trState : StateT
  /-- The word still to be emitted. -/
  pending : List Symbol
  length_pending_le : pending.length ≤ n

instance [Finite State] [Finite StateT] [Finite Symbol] {n : ℕ} :
    Finite (TransduceOutput.Control State StateT Symbol n) :=
  have := (List.finite_length_le Symbol n).to_subtype
  Finite.of_injective (fun c => (c.tmState, c.trState,
    (⟨c.pending, c.length_pending_le⟩ : {w : List Symbol // w.length ≤ n})))
    fun ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h => by simp_all

/-- The state of `tm.transduceOutput tr n` in which `w` is still to be emitted, where `s` is the
state of `tm` and `qT` the state of `tr`. If `tm` has halted and nothing is left to emit, this is
the halting state `none`. -/
def TransduceOutput.nextState {n : ℕ} (s : Option State) (qT : StateT) (w : List Symbol)
    (hw : w.length ≤ n) : Option (TransduceOutput.Control State StateT Symbol n) :=
  if s.isNone && w.isEmpty then none else some ⟨s, qT, w, hw⟩

open TransduceOutput in
/-- The machine that behaves like `tm`, but pipes its output through the subsequential
transducer `tr`. Its state `Control` consists of the state `tmState` of `tm` (`none` once `tm`
has halted), the state `trState` of `tr`, and the word `pending` still to be emitted, of length
at most `n`. If this word is nonempty, the machine emits its first symbol. Otherwise, it performs
the step of `tm`, computes the word that `tr` emits on the output of this step (including the
final output if `tm` halts), emits its first symbol and stores the rest. The machine halts as
soon as `tm` has halted and everything is emitted. -/
noncomputable def transduceOutput (tm : MultiTapeTM k Symbol State)
    (tr : SubsequentialTransducer StateT Symbol Symbol) (n : ℕ) :
    MultiTapeTM k Symbol (Control State StateT Symbol n) :=
  ofTr ⟨some tm.q₀, tr.start, [], by simp⟩ fun st inp work =>
    match st with
    | ⟨s, qT, b :: w, hw⟩ => ⟨0, fun _ => (none, 0), some b, nextState s qT w (by grind)⟩
    | ⟨none, _, [], _⟩ => ⟨0, fun _ => (none, 0), none, none⟩
    | ⟨some q, qT, [], _⟩ =>
      let a := tm.tr q inp work
      let w := (transduced tr a.state.isNone qT a.output.toList).take n
      ⟨a.inputTape, a.workTapes, w.head?,
        nextState a.state (a.output.toList.foldl tr.tr qT) w.tail (by grind)⟩

namespace TransduceOutput

variable (tr : SubsequentialTransducer StateT Symbol Symbol) {n : ℕ}
  {tm : MultiTapeTM k Symbol State}

private lemma evalFrom_append (q : StateT) (x y : List Symbol) :
    tr.evalFrom q (x ++ y) =
      tr.toSequentialTransducer.evalFrom q x ++ tr.evalFrom (x.foldl tr.tr q) y := by
  induction x generalizing q <;> simp_all

/-- The word that `tr` emits on the output of a step of `tm` is short. -/
private lemma length_transduced_le {m l : ℕ} (hemit : ∀ q b, (tr.emit q b).length ≤ m)
    (hfinal : ∀ q, (tr.finalOut q).length ≤ l) (halted : Bool) (q : StateT) (b : Option Symbol) :
    (transduced tr halted q b.toList).length ≤ m + if halted then l else 0 := by
  rcases b <;> cases halted <;> simp <;> grind

private lemma transduced_append (halted : Bool) (q : StateT) (x y : List Symbol) :
    transduced tr halted q (x ++ y) =
      tr.toSequentialTransducer.evalFrom q x ++ transduced tr halted (x.foldl tr.tr q) y := by
  cases halted
  · exact evalFrom_append tr.toSequentialTransducer.toSubsequential q x y
  · exact evalFrom_append tr q x y

@[simp]
lemma nextState_cons {s : Option State} {qT : StateT} {b : Symbol} {w : List Symbol}
    {hw : (b :: w).length ≤ n} : nextState s qT (b :: w) hw = some ⟨s, qT, b :: w, hw⟩ := by
  simp [nextState]

@[simp]
lemma nextState_some {q : State} {qT : StateT} {w : List Symbol} {hw : w.length ≤ n} :
    nextState (some q) qT w hw = some ⟨some q, qT, w, hw⟩ := by
  simp [nextState]

@[simp]
lemma nextState_none_nil {qT : StateT} {hw : [].length ≤ n} :
    nextState (State := State) (Symbol := Symbol) none qT [] hw = none := by
  simp [nextState]

/-- The configuration of `tm.transduceOutput tr n` with nothing to emit that simulates the
configuration `c` of `tm`. It is halted if `c` is. -/
def cfg (c : Cfg k Symbol State input) :
    Cfg k Symbol (Control State StateT Symbol n) input :=
  ⟨nextState c.state (c.output.foldl tr.tr tr.start) [] (by simp), c.inputPos, c.workTapes,
    c.workTapePos, transduced tr c.state.isNone tr.start c.output⟩

section Steps

variable {e : Cfg k Symbol (Control State StateT Symbol n) input}

/-- With a nonempty pending word, the machine emits its first symbol. -/
lemma step_of_pending {s : Option State} {qT : StateT} {b : Symbol} {w : List Symbol}
    {hw : (b :: w).length ≤ n} (he : e.state = some ⟨s, qT, b :: w, hw⟩) :
    (tm.transduceOutput tr n).step e =
      { e with state := nextState s qT w (by grind), output := e.output ++ [b] } := by
  rw [step_of_state he, transduceOutput, tr_ofTr]
  ext <;> simp [Action.apply]

/-- With nothing pending, the machine performs the step `a` of `tm`, emits the first symbol of
the word that `tr` emits on the output of `a`, and stores the rest. -/
lemma step_of_running {q : State} {qT : StateT} {hw : [].length ≤ n}
    (he : e.state = some ⟨some q, qT, [], hw⟩) {a : Action k Symbol State}
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

/-- While the pending word `w` is emitted, the work heads stand still. -/
lemma workTapePos_runFrom_of_pending {s : Option State} {qT : StateT} {w : List Symbol}
    {hw : w.length ≤ n} (he : e.state = nextState s qT w hw) {i : ℕ} (hi : i ≤ w.length) :
    ((tm.transduceOutput tr n).runFrom e i).workTapePos = e.workTapePos := by
  induction w generalizing e i with
  | nil => obtain rfl : i = 0 := by simpa using hi
           rfl
  | cons b w ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [runFrom, Function.iterate_succ_apply, ← runFrom,
        ih (by rw [step_of_pending tr (he.trans nextState_cons)]) (by simpa using hi),
        step_of_pending tr (he.trans nextState_cons)]

end Steps

/-- A step of `tm` is simulated by a run path of at most `max 1 m` steps, plus `l` steps if `tm`
halts. Its work heads are those of `c` or of the successor of `c`. -/
lemma exists_runPath_step {m l : ℕ} (hemit : ∀ q b, (tr.emit q b).length ≤ m)
    (hfinal : ∀ q, (tr.finalOut q).length ≤ l) {c : Cfg k Symbol State input} (hc : ¬c.Halted) :
    ∃ p : (tm.transduceOutput tr (m + l)).RunPath input, p.head = cfg tr c ∧
      p.last = cfg tr (tm.step c) ∧ p.length ≤ max 1 m + (if (tm.step c).Halted then l else 0) ∧
      ∀ e ∈ p, e.workTapePos = c.workTapePos ∨ e.workTapePos = (tm.step c).workTapePos := by
  obtain ⟨_ | q, pos, tapes, heads, out⟩ := c
  · exact absurd rfl hc
  set c : Cfg k Symbol State input := ⟨some q, pos, tapes, heads, out⟩
  set a := tm.tr q c.inputSymbol c.workTapeSymbols
  set w := transduced tr a.state.isNone (out.foldl tr.tr tr.start) a.output.toList
  have hw := length_transduced_le tr hemit hfinal a.state.isNone (out.foldl tr.tr tr.start) a.output
  have hw' : w.length ≤ m + l := hw.trans (by split <;> lia)
  have hc' : tm.step c = a.apply c := step_of_state rfl
  refine ⟨.ofDeterministic _ (cfg tr c) ((w.take (m + l)).tail.length + 1), rfl, ?_, ?_, ?_⟩
  · change (tm.transduceOutput tr (m + l)).runFrom (cfg tr c) ((w.take (m + l)).tail.length + 1) =
      _
    rw [runFrom, Function.iterate_succ_apply, ← runFrom, step_of_running tr (a := a) rfl rfl,
      runFrom_of_pending tr rfl, hc']
    ext <;> simp [cfg, Action.apply, transduced_append, List.take_of_length_le hw',
      ← List.take_one, ← List.drop_one, w, c]
  · change _ + 1 ≤ _
    rw [hc']
    simp only [List.take_of_length_le hw', List.length_tail, Cfg.Halted, Action.apply_state]
    split <;> simp_all <;> lia
  · rintro _ ⟨⟨_ | i, hi⟩, rfl⟩
    · exact .inl rfl
    · have hi' : i ≤ (w.take (m + l)).tail.length := by
        change i + 1 < _ + 1 + 1 at hi
        lia
      have hs :=
        step_of_running tr (tm := tm) (n := m + l) (e := cfg tr c) (q := q) (a := a) rfl rfl
      refine .inr ?_
      change ((tm.transduceOutput tr (m + l)).runFrom (cfg tr c) (i + 1)).workTapePos = _
      rw [runFrom, Function.iterate_succ_apply, ← runFrom,
        workTapePos_runFrom_of_pending tr (by rw [hs]; rfl) hi', hs, hc']
      rfl

/-- `t` steps of `tm` are simulated by a run path of at most `max 1 m * t` steps, plus `l` steps
if `tm` halts, whose work heads are those of the run of `tm`. -/
lemma exists_runPath {m l : ℕ} (hemit : ∀ q b, (tr.emit q b).length ≤ m)
    (hfinal : ∀ q, (tr.finalOut q).length ≤ l) (c : Cfg k Symbol State input) (t : ℕ) :
    ∃ p : (tm.transduceOutput tr (m + l)).RunPath input, p.head = cfg tr c ∧
      p.last = cfg tr (tm.runFrom c t) ∧
      p.length ≤ max 1 m * t + (if (tm.runFrom c t).Halted then l else 0) ∧
      ∀ e ∈ p, ∃ i ≤ t, e.workTapePos = (tm.runFrom c i).workTapePos := by
  induction t with
  | zero => exact ⟨.singleton _ (cfg tr c), rfl, rfl, by simp, fun _ ⟨_, h⟩ => ⟨0, le_rfl, h ▸ rfl⟩⟩
  | succ t ih =>
    obtain ⟨p, hh, hl, hlen, hmem⟩ := ih
    have hsucc : tm.runFrom c (t + 1) = tm.step (tm.runFrom c t) := by
      rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    rw [hsucc, Nat.mul_succ]
    by_cases hc : (tm.runFrom c t).Halted
    · rw [step_of_halt hc]
      exact ⟨p, hh, hl, by lia, fun e he => (hmem e he).imp fun _ ⟨hi, h⟩ => ⟨by lia, h⟩⟩
    · obtain ⟨p', hh', hl', hlen', hmem'⟩ := exists_runPath_step tr hemit hfinal hc
      simp only [hc, ↓reduceIte] at hlen
      refine ⟨p.smash p' (hl.trans hh'.symm), by simp [hh], by simp [hl'], by simp; omega,
        fun e he => ?_⟩
      rcases RelSeries.mem_or_mem_of_mem_smash he with he | he
      · exact (hmem e he).imp fun _ ⟨hi, h⟩ => ⟨by lia, h⟩
      · exact (hmem' e he).elim (⟨t, by lia, ·⟩) (⟨t + 1, le_rfl, hsucc ▸ ·⟩)

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
  obtain ⟨q, hqh, hql, hlen, hmem⟩ := exists_runPath tr hemit hfinal p.head p.length
  rw [← runPath_last_eq_runFrom] at hql hlen
  simp only [eq_true halt, ↓reduceIte] at hlen
  refine computesInTimeAndSpace_iff_exists_runPath.mpr ⟨q, by rw [hqh, hh]; rfl,
    by rw [hql]; simp [cfg, halt], by rw [hql]; simp [cfg, halt], hlen.trans (by grw [ht]), ?_⟩
  refine (MultiTapeNTM.RunPath.space_le_sum_card _ (S := p.visitedByTapeHead)
    fun e he l => ?_).trans hs
  obtain ⟨i, hi, h⟩ := hmem e he
  exact p.mem_visitedByTapeHead.mpr
    ⟨_, ⟨⟨i, by lia⟩, runPath_apply_eq_runFrom ..⟩, (congrFun h l).symm⟩

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
  exact ⟨k, _, inferInstance, tm.transduceOutput tr (m + l),
    fun a => hg (f a) ▸ (htm a).transduceOutput tr hemit hfinal⟩

end Turing.MultiTapeTM
