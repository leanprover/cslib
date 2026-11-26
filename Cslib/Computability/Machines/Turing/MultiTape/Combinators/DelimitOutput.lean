/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.DA.Transducer
public import Cslib.Computability.Encoding.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Fintype.Option

/-!
# Delimiting the output of a machine

`tm.delimitOutput` behaves like `tm`, but outputs the delimited code `Cslib.Encoding.delimit` of
the output of `tm`: each emitted bit `b` becomes `true, b`, and a final `false` is emitted before
halting. A step of `tm` that emits a bit takes two steps, so the time at most doubles, plus one
step for the final delimiter. The work tapes are used exactly as `tm` uses them.

## Main definitions

* `Turing.MultiTapeTM.delimitOutput`: the machine with delimited output.

## Main results

* `Turing.MultiTapeTM.ComputesInTimeAndSpace.delimitOutput`: if `tm` outputs `out` in time `t` and
  space `s`, then `tm.delimitOutput` outputs `delimit out` in time `2 * t + 1` and space `s`.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.delimit`: the same for computable functions, with
  the delimited output encoding `Cslib.Encoding.encDelimited`.
-/

public section

namespace Turing.MultiTapeTM

open Cslib.Encoding

variable {k : ℕ} {State : Type*} {input : List Bool}

/-- The machine that behaves like `tm`, but outputs `true, b` for each bit `b` that `tm` outputs,
and a final `false`. Its state is the (optional) state of `tm` together with an optional bit that
is still to be emitted. In state `(some q, none)` it acts like `tm` in `q`, emitting `true` in
place of a bit `b`, which it then emits from state `(_, some b)`. In state `(none, none)`, reached
when `tm` has halted, it emits `false` and halts. -/
noncomputable def delimitOutput (tm : MultiTapeTM k Bool State) :
    MultiTapeTM k Bool (Option State × Option Bool) :=
  ofTr (some tm.q₀, none) fun st inp work =>
    match st with
    | (q, some b) =>
      { inputTape := 0, workTapes := fun _ => (none, 0), output := some b, state := some (q, none) }
    | (none, none) =>
      { inputTape := 0, workTapes := fun _ => (none, 0), output := some false, state := none }
    | (some q, none) =>
      { inputTape := (tm.tr q inp work).inputTape, workTapes := (tm.tr q inp work).workTapes,
        output := (tm.tr q inp work).output.map fun _ => true,
        state := some ((tm.tr q inp work).state, (tm.tr q inp work).output) }

namespace DelimitOutput

variable {tm : MultiTapeTM k Bool State}

/-- The configuration of `tm.delimitOutput` simulating the configuration `c` of `tm`, with no bit
pending: the output of `c` appears delimited, but without the final `false`. -/
def cfg (c : Cfg k Bool State input) : Cfg k Bool (Option State × Option Bool) input :=
  ⟨some (c.state, none), c.inputPos, c.workTapes, c.workTapePos,
    c.output.flatMap fun b => [true, b]⟩

private lemma runFrom_add {tm' : MultiTapeTM k Bool State} (c : Cfg k Bool State input) (a b : ℕ) :
    tm'.runFrom c (a + b) = tm'.runFrom (tm'.runFrom c a) b := by
  simp [runFrom, ← Function.iterate_add_apply, Nat.add_comm a b]

/-- One step of `tm` is simulated by at most two steps, during which the work heads are where
they are before or after the step of `tm`. -/
lemma exists_runFrom_cfg_step (c : Cfg k Bool State input) :
    ∃ m ≤ 2, tm.delimitOutput.runFrom (cfg c) m = cfg (tm.step c) ∧
      ∀ m' ≤ m, (tm.delimitOutput.runFrom (cfg c) m').workTapePos = c.workTapePos ∨
        (tm.delimitOutput.runFrom (cfg c) m').workTapePos = (tm.step c).workTapePos := by
  rcases hq : c.state with _ | q
  · exact ⟨0, by lia, by rw [step_of_halt hq]; rfl, fun m' hm' =>
      .inl (by rw [Nat.le_zero.mp hm']; rfl)⟩
  set a := tm.tr q c.inputSymbol c.workTapeSymbols with ha
  have hc : tm.step c = a.apply c := step_of_state hq
  have h1 : tm.delimitOutput.runFrom (cfg c) 1 = Action.apply
      { inputTape := a.inputTape, workTapes := a.workTapes, output := a.output.map fun _ => true,
        state := some (a.state, a.output) } (cfg c) := by
    change tm.delimitOutput.step (cfg c) = _
    rw [step_of_state (q := (some q, none)) (by simp [cfg, hq]), delimitOutput, tr_ofTr]
    rfl
  obtain ⟨m, hm, hm', hrun⟩ :
      ∃ m, 1 ≤ m ∧ m ≤ 2 ∧ tm.delimitOutput.runFrom (cfg c) m = cfg (tm.step c) := by
    rcases ho : a.output with _ | b
    · exact ⟨1, le_rfl, by lia, by rw [h1, hc]; simp [cfg, Action.apply, ho]⟩
    · refine ⟨2, by lia, le_rfl, ?_⟩
      rw [show tm.delimitOutput.runFrom (cfg c) 2 =
        tm.delimitOutput.step (tm.delimitOutput.runFrom (cfg c) 1) from rfl, h1, ho,
        step_of_state (q := (a.state, some b)) rfl, delimitOutput, tr_ofTr, hc]
      simp [cfg, Action.apply, ho]
  refine ⟨m, hm', hrun, fun m' _ => ?_⟩
  obtain rfl | rfl | rfl : m' = 0 ∨ m' = 1 ∨ m' = m := by lia
  exacts [.inl rfl, .inr (by rw [h1, hc]; rfl), .inr (by rw [hrun]; rfl)]

/-- `n` steps of `tm` are simulated by at most `2 * n` steps, during which the work heads are
where they are at some point of the run of `tm`. -/
lemma exists_runFrom_cfg (c : Cfg k Bool State input) (n : ℕ) :
    ∃ m ≤ 2 * n, tm.delimitOutput.runFrom (cfg c) m = cfg (tm.runFrom c n) ∧
      ∀ m' ≤ m, ∃ n' ≤ n,
        (tm.delimitOutput.runFrom (cfg c) m').workTapePos = (tm.runFrom c n').workTapePos := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl, fun m' hm' => ⟨0, le_rfl, by rw [Nat.le_zero.mp hm']; rfl⟩⟩
  | succ n ih =>
    obtain ⟨m, hm, hrun, hpos⟩ := ih
    obtain ⟨j, hj, hrun', hpos'⟩ := exists_runFrom_cfg_step (tm := tm) (tm.runFrom c n)
    have hsucc : tm.runFrom c (n + 1) = tm.step (tm.runFrom c n) := by
      simp [runFrom, Function.iterate_succ_apply']
    refine ⟨m + j, by omega, by
      rw [runFrom_add, hrun, hrun', hsucc], fun m' hm' => ?_⟩
    rcases le_or_gt m' m with h | h
    · obtain ⟨n', hn', h'⟩ := hpos m' h; exact ⟨n', by omega, h'⟩
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h.le
      rw [runFrom_add, hrun]
      rcases hpos' i (by omega) with h' | h'
      · exact ⟨n, by omega, h'⟩
      · exact ⟨n + 1, le_rfl, by rw [h', hsucc]⟩

/-- Once `tm` has halted, the final delimiter is emitted and the machine halts. -/
lemma step_cfg_of_halted {c : Cfg k Bool State input} (h : c.Halted) :
    tm.delimitOutput.step (cfg c) =
      ⟨none, c.inputPos, c.workTapes, c.workTapePos, delimit c.output⟩ := by
  rw [step_of_state (q := (none, none)) (by simp [cfg, show c.state = none from h]),
    delimitOutput, tr_ofTr]
  simp [cfg, Action.apply, delimit]

end DelimitOutput

open DelimitOutput in
/-- If `tm` outputs `out`, then `tm.delimitOutput` outputs the delimited code of `out`, in at most
twice the time plus one step, and in the same space. -/
theorem ComputesInTimeAndSpace.delimitOutput {tm : MultiTapeTM k Bool State} {out : List Bool}
    {t s : ℕ} (h : tm.ComputesInTimeAndSpace input out t s) :
    tm.delimitOutput.ComputesInTimeAndSpace input (delimit out) (2 * t + 1) s := by
  obtain ⟨p, hh, halt, rfl, ht, hs⟩ := computesInTimeAndSpace_iff_exists_runPath.mp h
  obtain ⟨m, hm, hrun, hpos⟩ := exists_runFrom_cfg (tm := tm) p.head p.length
  rw [← runPath_last_eq_runFrom] at hrun
  have hlast : tm.delimitOutput.runFrom (cfg p.head) (m + 1) =
      ⟨none, p.last.inputPos, p.last.workTapes, p.last.workTapePos, delimit p.last.output⟩ := by
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, hrun, step_cfg_of_halted halt]
  refine computesInTimeAndSpace_iff_exists_runPath.mpr
    ⟨.ofDeterministic _ (cfg p.head) (m + 1), by rw [hh]; rfl, ?_, ?_, ?_, ?_⟩
  · exact congrArg Cfg.state hlast
  · exact congrArg Cfg.output hlast
  · exact (Nat.add_le_add_right hm 1).trans (by change _ ≤ 2 * t + 1; lia)
  · refine (MultiTapeNTM.RunPath.space_le_sum_card _ (S := p.visitedByTapeHead) ?_).trans hs
    rintro _ ⟨⟨m', hm'⟩, rfl⟩ i
    rw [MultiTapeNTM.RunPath.mem_visitedByTapeHead]
    change m' < m + 1 + 1 at hm'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm' with h' | rfl
    · obtain ⟨n', hn', h⟩ := hpos m' (by lia)
      exact ⟨p ⟨n', by lia⟩, ⟨_, rfl⟩, by
        rw [runPath_apply_eq_runFrom]
        exact (congrFun h i).symm⟩
    · exact ⟨p.last, p.last_mem, (congrFun (congrArg Cfg.workTapePos hlast) i).symm⟩

/-- A function computable with some output encoding is computable with the delimited output
encoding, in at most twice the time plus one step, and in the same space. -/
theorem ComputableInTimeAndSpace.delimit {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {t s : α → ℕ} (h : ComputableInTimeAndSpace f encIn encOut t s) :
    ComputableInTimeAndSpace f encIn (encDelimited encOut) (fun a => 2 * t a + 1) s := by
  obtain ⟨k, State, _, tm, htm⟩ := h
  exact ⟨k, _, inferInstance, tm.delimitOutput, fun a => (htm a).delimitOutput⟩

/-! ### Transducing the output with a subsequential transducer -/

section TransduceOutput

variable {Symbol : Type*} {StateT : Type*} {input : List Symbol}

/-- The machine that behaves like `tm`, but pipes its output through the subsequential
transducer `tr`: each output symbol `b` emitted by `tm` while `tr` is in state `qT` is replaced by
the word `tr.emit qT b`, and when `tm` halts, `tr.finalOut qT` is appended. Its state is the
state of `tm`, the state of `tr`, and an optional pending output word (the symbol being transduced
and the position within its chunk). In a pending state the input and work heads stay put. -/
noncomputable def transduceOutput (tm : MultiTapeTM k Symbol State)
    (tr : Cslib.Automata.SubsequentialTransducer StateT Symbol Symbol) (m : ℕ) :
    MultiTapeTM k Symbol ((Option State × StateT) × Option (Option Symbol × Fin (m + 1))) :=
  ofTr ((some tm.q₀, tr.start), none) fun st inp work =>
    match st with
    | ((some q, qT), none) =>
      let a := tm.tr q inp work
      match a.output with
      | none =>
        { inputTape := a.inputTape, workTapes := a.workTapes, output := none,
          state := some ((a.state, qT), none) }
      | some b =>
        { inputTape := a.inputTape, workTapes := a.workTapes, output := none,
          state := some ((a.state, qT), some (some b, 0)) }
    | ((q', qT), some (some b, i)) =>
      let out := tr.emit qT b
      if h : i.val < out.length then
        { inputTape := 0, workTapes := fun _ => (none, 0), output := some out[i.val],
          state := some ((q', qT), some (some b, i + 1)) }
      else
        { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
          state := some ((q', tr.tr qT b), none) }
    | ((q', qT), some (none, i)) =>
      let out := tr.finalOut qT
      if h : i.val < out.length then
        { inputTape := 0, workTapes := fun _ => (none, 0), output := some out[i.val],
          state := some ((q', qT), some (none, i + 1)) }
      else
        { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }
    | ((none, qT), none) =>
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
        state := some ((none, qT), some (none, 0)) }

namespace TransduceOutput

variable {tm : MultiTapeTM k Symbol State}
variable (tr : Cslib.Automata.SubsequentialTransducer StateT Symbol Symbol) {m : ℕ}

/-- The words emitted by `tr` on `w` per transition, without the final output. -/
private abbrev chunks (q : StateT) (w : List Symbol) : List Symbol :=
  tr.toSequentialTransducer.evalFrom q w

private lemma chunks_nil (q : StateT) : chunks tr q [] = [] := rfl

private lemma chunks_cons (q : StateT) (b : Symbol) (w : List Symbol) :
    chunks tr q (b :: w) = tr.emit q b ++ chunks tr (tr.tr q b) w := rfl

private lemma chunks_append (q : StateT) (w : List Symbol) (b : Symbol) :
    chunks tr q (w ++ [b]) = chunks tr q w ++ tr.emit (w.foldl tr.tr q) b := by
  induction w generalizing q with
  | nil => simp [chunks]
  | cons a w ih =>
    rw [List.cons_append, chunks_cons, ih, chunks_cons, List.foldl_cons, List.append_assoc]

private lemma evalFrom_eq_chunks_final (q : StateT) (w : List Symbol) :
    tr.evalFrom q w = chunks tr q w ++ tr.finalOut (w.foldl tr.tr q) := by
  induction w generalizing q with
  | nil => simp [chunks]
  | cons a w ih =>
    rw [Cslib.Automata.SubsequentialTransducer.evalFrom, chunks_cons, ih, List.foldl_cons]
    simp [List.append_assoc]

/-- The configuration of `tm.transduceOutput tr m` simulating the configuration `c` of `tm`,
where `qT` is the state of `tr` after consuming the output of `c`. -/
def cfg (c : Cfg k Symbol State input) (qT : StateT) :
    Cfg k Symbol ((Option State × StateT) × Option (Option Symbol × Fin (m + 1))) input :=
  ⟨some ((c.state, qT), none), c.inputPos, c.workTapes, c.workTapePos,
    chunks tr tr.start c.output⟩

lemma runFrom_add {tm' : MultiTapeTM k Symbol State} (c : Cfg k Symbol State input) (a b : ℕ) :
    tm'.runFrom c (a + b) = tm'.runFrom (tm'.runFrom c a) b := by
  simp [runFrom, ← Function.iterate_add_apply, Nat.add_comm a b]

/-- While a chunk `out` is pending, the machine emits one symbol of the chunk per
step, keeping the input and work heads in place, and then enters `next`. -/
private lemma runFrom_pending
    (c : Cfg k Symbol ((Option State × StateT) × Option (Option Symbol × Fin (m + 1))) input)
    (q' : Option State) (qT : StateT) (pb : Option Symbol) (out : List Symbol)
    (hL : out.length ≤ m) (hout : out = pb.elim (tr.finalOut qT) (fun b => tr.emit qT b))
    (next : Option ((Option State × StateT) × Option (Option Symbol × Fin (m + 1))))
    (hnext : next = pb.elim none (fun b => some ((q', tr.tr qT b), none)))
    (hstate : c.state = some ((q', qT), some (pb, 0))) :
    (∀ j (hj : j ≤ out.length),
      (tm.transduceOutput tr m).runFrom c j =
        ⟨some ((q', qT), some (pb, ⟨j, by lia⟩)), c.inputPos, c.workTapes,
          c.workTapePos, c.output ++ out.take j⟩) ∧
    (tm.transduceOutput tr m).runFrom c (out.length + 1) =
      ⟨next, c.inputPos, c.workTapes, c.workTapePos, c.output ++ out⟩ := by
  have hfin : ∀ j (hj : j < out.length), (⟨j, by lia⟩ : Fin (m + 1)) + 1 = ⟨j + 1, by lia⟩ := by
    intro j hj
    have h1 : (1 : Fin (m + 1)).val = 1 := Nat.mod_eq_of_lt (by lia)
    simp only [Fin.ext_iff, Fin.val_add, h1]
    exact Nat.mod_eq_of_lt (by lia)
  have hstep : ∀ j (hj : j < out.length),
      (tm.transduceOutput tr m).step
          ⟨some ((q', qT), some (pb, ⟨j, by lia⟩)), c.inputPos, c.workTapes,
            c.workTapePos, c.output ++ out.take j⟩ =
        ⟨some ((q', qT), some (pb, ⟨j + 1, by lia⟩)), c.inputPos, c.workTapes,
          c.workTapePos, c.output ++ out.take (j + 1)⟩ := by
    intro j hj
    cases pb with
    | none =>
      have hout' : out = tr.finalOut qT := hout
      subst hout'
      rw [step_of_state rfl, transduceOutput, tr_ofTr]
      simp [hj, Action.apply, hfin j hj]
    | some b =>
      have hout' : out = tr.emit qT b := hout
      subst hout'
      rw [step_of_state rfl, transduceOutput, tr_ofTr]
      simp [hj, Action.apply, hfin j hj]
  have key : ∀ j (hj : j ≤ out.length),
      (tm.transduceOutput tr m).runFrom c j =
        ⟨some ((q', qT), some (pb, ⟨j, by lia⟩)), c.inputPos, c.workTapes,
          c.workTapePos, c.output ++ out.take j⟩ := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [runFrom, Function.iterate_zero_apply, List.take_zero, List.append_nil]
      exact Cfg.ext hstate rfl rfl rfl rfl
    | succ j ih =>
      intro hj
      rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by lia), hstep j (by lia)]
  refine ⟨key, ?_⟩
  rw [runFrom, Function.iterate_succ_apply', ← runFrom, key _ le_rfl,
    List.take_of_length_le (Nat.le_refl _)]
  cases pb with
  | none => simp [step_of_state _, transduceOutput, tr_ofTr, hout, hnext, Action.apply]
  | some b => simp [step_of_state _, transduceOutput, tr_ofTr, hout, hnext, Action.apply]

/-- One step of `tm` is simulated by at most `m + 2` steps: the step of `tm` itself, then the
chunk `tr.emit qT b` for its output symbol `b`, one symbol per step. The work heads are where they
are before or after the step of `tm`. -/
lemma exists_runFrom_cfg_step (hbound : tr.OutputBoundedBy m) (c : Cfg k Symbol State input)
    (qT : StateT) (hqT : qT = c.output.foldl tr.tr tr.start) :
    ∃ j ≤ m + 2, (tm.transduceOutput tr m).runFrom (cfg tr c qT) j =
        cfg tr (tm.step c) ((tm.step c).output.foldl tr.tr tr.start) ∧
      ∀ j' ≤ j, ((tm.transduceOutput tr m).runFrom (cfg tr c qT) j').workTapePos =
        c.workTapePos ∨ ((tm.transduceOutput tr m).runFrom (cfg tr c qT) j').workTapePos =
          (tm.step c).workTapePos := by
  rcases hq : c.state with _ | q
  · refine ⟨0, by lia, ?_, fun j' hj' => .inl ?_⟩
    · rw [step_of_halt hq, ← hqT]
      simp [runFrom, Function.iterate_zero_apply]
    · rw [Nat.le_zero.mp hj']
      simp [runFrom, Function.iterate_zero_apply, cfg]
  have hc : tm.step c = (tm.tr q c.inputSymbol c.workTapeSymbols).apply c := step_of_state hq
  have hstep1 : (tm.transduceOutput tr m).step (cfg tr c qT) =
      ((tm.transduceOutput tr m).tr ((some q, qT), none) (cfg tr c qT).inputSymbol
        (cfg tr c qT).workTapeSymbols).apply (cfg tr c qT) :=
    step_of_state (q := ((some q, qT), none))
      (show (cfg (m := m) tr c qT).state = some ((some q, qT), none) by simp [cfg, hq])
  rcases ho : (tm.tr q c.inputSymbol c.workTapeSymbols).output with _ | b
  · have h1 : (tm.transduceOutput tr m).step (cfg tr c qT) = Action.apply
        { inputTape := (tm.tr q c.inputSymbol c.workTapeSymbols).inputTape,
          workTapes := (tm.tr q c.inputSymbol c.workTapeSymbols).workTapes, output := none,
          state := some (((tm.tr q c.inputSymbol c.workTapeSymbols).state, qT), none) }
        (cfg tr c qT) := by
      rw [hstep1, transduceOutput, tr_ofTr]
      have hinp : (cfg (m := m) tr c qT).inputSymbol = c.inputSymbol := rfl
      have hwork : (cfg (m := m) tr c qT).workTapeSymbols = c.workTapeSymbols := rfl
      simp only [hinp, hwork]
      rw [ho]
    have hq' : (tm.step c).output.foldl tr.tr tr.start = qT := by
      rw [hc]
      simp [Action.apply, ho, hqT]
    refine ⟨1, by lia, ?_, ?_⟩
    · rw [runFrom, Function.iterate_one, h1, hc]
      simp [cfg, Action.apply, chunks, ho, hqT]
    · intro j' hj'
      obtain rfl | rfl : j' = 0 ∨ j' = 1 := by lia
      · exact .inl (by simp [runFrom, Function.iterate_zero_apply, cfg])
      · exact .inr (by rw [runFrom, Function.iterate_one, h1, hc]; simp [cfg, Action.apply])
  · have hL : (tr.emit qT b).length ≤ m := hbound qT (some b)
    have hfold : (tm.step c).output.foldl tr.tr tr.start = tr.tr qT b := by
      rw [hc]
      simp [Action.apply, ho, hqT]
    have hout : chunks tr tr.start (tm.step c).output =
        chunks tr tr.start c.output ++ tr.emit qT b := by
      rw [hc]
      simp [Action.apply, ho, chunks_append, hqT]
    have h1 : (tm.transduceOutput tr m).step (cfg tr c qT) =
        ⟨some (((tm.tr q c.inputSymbol c.workTapeSymbols).state, qT), some (some b, 0)),
          (tm.step c).inputPos, (tm.step c).workTapes,
          (tm.step c).workTapePos, chunks tr tr.start c.output⟩ := by
      rw [hstep1, transduceOutput, tr_ofTr]
      have hinp : (cfg (m := m) tr c qT).inputSymbol = c.inputSymbol := rfl
      have hwork : (cfg (m := m) tr c qT).workTapeSymbols = c.workTapeSymbols := rfl
      simp only [hinp, hwork]
      rw [ho]
      simp [hc, cfg, Action.apply]
    obtain ⟨hpend, hnext⟩ := runFrom_pending tr
      ⟨some (((tm.tr q c.inputSymbol c.workTapeSymbols).state, qT), some (some b, 0)),
        (tm.step c).inputPos, (tm.step c).workTapes,
        (tm.step c).workTapePos, chunks tr tr.start c.output⟩
      (tm.tr q c.inputSymbol c.workTapeSymbols).state qT (some b) (tr.emit qT b)
      hL rfl (some (((tm.tr q c.inputSymbol c.workTapeSymbols).state, tr.tr qT b), none)) rfl rfl
    refine ⟨(tr.emit qT b).length + 2, by lia, ?_, ?_⟩
    · have h12 : (tr.emit qT b).length + 2 = ((tr.emit qT b).length + 1) + 1 := by lia
      rw [h12, runFrom, Function.iterate_add_apply, Function.iterate_one, h1, ← runFrom, hnext, hc]
      simp [cfg, Action.apply, ho, hqT, chunks_append]
    · intro j' hj'
      rcases le_or_gt j' 1 with h | h
      · obtain rfl | rfl : j' = 0 ∨ j' = 1 := by lia
        · exact .inl (by simp [runFrom, Function.iterate_zero_apply, cfg])
        · exact .inr (by rw [runFrom, Function.iterate_one, h1])
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h.le
        have hi : i ≤ (tr.emit qT b).length + 1 := by lia
        rw [show (1 : ℕ) + i = i + 1 from by lia, runFrom, Function.iterate_add_apply,
          Function.iterate_one, h1, ← runFrom]
        rcases le_or_gt i (tr.emit qT b).length with hi' | hi'
        · exact .inr (by rw [hpend i hi'])
        · have hi'' : i = (tr.emit qT b).length + 1 := by lia
          subst hi''
          exact .inr (by rw [hnext])

/-- `n` steps of `tm` are simulated by at most `(m + 2) * n` steps, during which the work heads
are where they are at some point of the run of `tm`. -/
lemma exists_runFrom_cfg (hbound : tr.OutputBoundedBy m) (c : Cfg k Symbol State input)
    (qT : StateT) (hqT : qT = c.output.foldl tr.tr tr.start) (n : ℕ) :
    ∃ j ≤ (m + 2) * n, (tm.transduceOutput tr m).runFrom (cfg tr c qT) j =
        cfg tr (tm.runFrom c n) ((tm.runFrom c n).output.foldl tr.tr tr.start) ∧
      ∀ j' ≤ j, ∃ n' ≤ n,
        ((tm.transduceOutput tr m).runFrom (cfg tr c qT) j').workTapePos =
          (tm.runFrom c n').workTapePos := by
  induction n with
  | zero =>
    exact ⟨0, le_rfl, by simp [runFrom, ← hqT], fun j' hj' =>
      ⟨0, le_rfl, by simp [runFrom, cfg, Nat.le_zero.mp hj']⟩⟩
  | succ n ih =>
    obtain ⟨j, hj, hrun, hpos⟩ := ih
    obtain ⟨j', hj', hrun', hpos'⟩ := exists_runFrom_cfg_step tr hbound (tm.runFrom c n) _ rfl
    have hsucc : tm.runFrom c (n + 1) = tm.step (tm.runFrom c n) := by
      rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    refine ⟨j + j', by rw [Nat.mul_succ]; exact Nat.add_le_add hj hj', by
      rw [runFrom_add, hrun, hrun', hsucc], fun j'' hj'' => ?_⟩
    rcases le_or_gt j'' j with h | h
    · obtain ⟨n', hn', h'⟩ := hpos j'' h; exact ⟨n', by omega, h'⟩
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h.le; rw [runFrom_add, hrun]
      rcases hpos' i (by omega) with h' | h'
      · exact ⟨n, by omega, h'⟩
      · exact ⟨n + 1, le_rfl, by rw [h', hsucc]⟩

/-- Once `tm` has halted, the final output of `tr` is emitted and the machine halts, without
moving the work heads. -/
lemma exists_runFrom_cfg_of_halted (hbound : tr.OutputBoundedBy m) {c : Cfg k Symbol State input}
    (h : c.Halted) (qT : StateT) (hqT : qT = c.output.foldl tr.tr tr.start) :
    ∃ j ≤ m + 2, (tm.transduceOutput tr m).runFrom (cfg tr c qT) j =
        ⟨none, c.inputPos, c.workTapes, c.workTapePos, tr.evalFrom tr.start c.output⟩ ∧
      ∀ j' ≤ j,
        ((tm.transduceOutput tr m).runFrom (cfg tr c qT) j').workTapePos = c.workTapePos := by
  have hL : (tr.finalOut qT).length ≤ m := hbound qT none
  have h1 : (tm.transduceOutput tr m).step (cfg tr c qT) =
      ⟨some ((none, qT), some (none, 0)), c.inputPos, c.workTapes, c.workTapePos,
        chunks tr tr.start c.output⟩ := by
    rw [step_of_state (q := ((none, qT), none)) (by simp [cfg, h]), transduceOutput, tr_ofTr]
    simp [cfg, Action.apply]
  obtain ⟨hpend, hnext⟩ := runFrom_pending tr
    ⟨some ((none, qT), some (none, 0)), c.inputPos, c.workTapes, c.workTapePos,
      chunks tr tr.start c.output⟩ none qT none (tr.finalOut qT) hL rfl none rfl rfl
  set L := (tr.finalOut qT).length with hLdef
  refine ⟨L + 2, by omega, ?_, ?_⟩
  · rw [show L + 2 = (L + 1) + 1 by omega, runFrom, Function.iterate_add_apply,
      Function.iterate_one, h1, ← runFrom, hnext,
      evalFrom_eq_chunks_final tr tr.start c.output, hqT]
  · intro j' hj'
    rcases le_or_gt j' 1 with h' | h'
    · obtain rfl | rfl : j' = 0 ∨ j' = 1 := by omega
      · rfl
      · rw [runFrom, Function.iterate_one, h1]
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h'.le
      rw [show (1 : ℕ) + i = i + 1 by omega, runFrom, Function.iterate_add_apply,
        Function.iterate_one, h1, ← runFrom]
      rcases le_or_gt i L with hi' | hi'
      · rw [hpend i hi']
      · obtain rfl : i = L + 1 := by omega
        exact congrArg Cfg.workTapePos hnext

end TransduceOutput

open TransduceOutput in
/-- If `tm` outputs `out` in time `t` and space `s`, then `tm.transduceOutput tr m` outputs
`tr.eval out` in time at most `(m + 2) * (t + 1)` and space `s`, provided that `m` bounds every
chunk that `tr` emits. -/
theorem ComputesInTimeAndSpace.transduceOutput {tm : MultiTapeTM k Symbol State}
    (tr : Cslib.Automata.SubsequentialTransducer StateT Symbol Symbol) {m : ℕ}
    (hbound : tr.OutputBoundedBy m)
    {out : List Symbol} {t s : ℕ} (h : tm.ComputesInTimeAndSpace input out t s) :
    (tm.transduceOutput tr m).ComputesInTimeAndSpace input (tr.eval out) ((m + 2) * (t + 1)) s := by
  obtain ⟨p, hh, halt, rfl, ht, hs⟩ := computesInTimeAndSpace_iff_exists_runPath.mp h
  obtain ⟨j, hj, hrun, hpos⟩ :=
    exists_runFrom_cfg tr hbound p.head tr.start (by rw [hh]; rfl) p.length
  rw [← runPath_last_eq_runFrom] at hrun
  obtain ⟨j', hj', hlast, hpos'⟩ := exists_runFrom_cfg_of_halted tr hbound halt _ rfl
  have hrun' : (tm.transduceOutput tr m).runFrom (cfg tr p.head tr.start) (j + j') =
      ⟨none, p.last.inputPos, p.last.workTapes, p.last.workTapePos, tr.eval p.last.output⟩ := by
    rw [runFrom_add, hrun, hlast]
  refine computesInTimeAndSpace_iff_exists_runPath.mpr
    ⟨.ofDeterministic _ (cfg tr p.head tr.start) (j + j'), by rw [hh]; rfl, ?_, ?_, ?_, ?_⟩
  · exact congrArg Cfg.state hrun'
  · exact congrArg Cfg.output hrun'
  · exact (Nat.add_le_add hj hj').trans_eq (by rw [← Nat.mul_succ]) |>.trans
      (Nat.mul_le_mul_left _ (by omega))
  · refine (MultiTapeNTM.RunPath.space_le_sum_card _ (S := p.visitedByTapeHead) ?_).trans hs
    rintro _ ⟨⟨m', hm'⟩, rfl⟩ i
    rw [MultiTapeNTM.RunPath.mem_visitedByTapeHead]
    rcases Nat.lt_succ_iff_lt_or_eq.mp (show m' < j + j' + 1 from hm') with h' | rfl
    · rcases le_or_gt m' j with hle | hgt
      · obtain ⟨n', hn', h⟩ := hpos m' hle
        exact ⟨p ⟨n', by omega⟩, ⟨_, rfl⟩, by
          rw [runPath_apply_eq_runFrom]; exact (congrFun h i).symm⟩
      · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le hgt.le
        have hgoal : ∃ c ∈ p, c.workTapePos i =
            ((tm.transduceOutput tr m).runFrom (cfg tr p.head tr.start)
              (j + i')).workTapePos i := by
          rw [runFrom_add, hrun]
          exact ⟨p.last, p.last_mem, by rw [hpos' i' (by omega)]⟩
        exact hgoal
    · exact ⟨p.last, p.last_mem, (congrFun (congrArg Cfg.workTapePos hrun') i).symm⟩

end TransduceOutput

/-- Composing a function on Boolean words that is computable in time `t` and space `s` with a
subsequential transducer `tr` on the output: the composite `tr.eval ∘ f` is computable in time
`(m + 2) * (t + 1)` and space `s`, where `m` bounds the output chunks of `tr`. -/
theorem ComputableInTimeAndSpace.transduce {StateT : Type} [Finite StateT]
    (tr : Cslib.Automata.SubsequentialTransducer StateT Bool Bool)
    {f : List Bool → List Bool} {t s : List Bool → ℕ}
    (h : ComputableInTimeAndSpace f encBits encBits t s) :
    ∃ m, ComputableInTimeAndSpace (tr.eval ∘ f) encBits encBits
      (fun w => (m + 2) * (t w + 1)) s := by
  obtain ⟨m, hbound⟩ := tr.exists_outputBoundedBy_of_finite
  obtain ⟨k, State, _, tm, htm⟩ := h
  refine ⟨m, k, _, inferInstance, tm.transduceOutput tr m, fun w => ?_⟩
  exact (htm w).transduceOutput tr hbound

end Turing.MultiTapeTM
