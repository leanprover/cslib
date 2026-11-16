/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

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
    have hadd (i : ℕ) : tm.delimitOutput.runFrom (cfg c) (m + i) =
        tm.delimitOutput.runFrom (cfg (tm.runFrom c n)) i := by
      rw [← hrun, runFrom, runFrom, runFrom, Nat.add_comm, Function.iterate_add_apply]
    have hsucc : tm.runFrom c (n + 1) = tm.step (tm.runFrom c n) := by
      rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    refine ⟨m + j, by lia, by rw [hadd, hrun', hsucc], fun m' hm' => ?_⟩
    rcases le_or_gt m' m with h | h
    · obtain ⟨n', hn', h'⟩ := hpos m' h
      exact ⟨n', by lia, h'⟩
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h.le
      rw [hadd]
      rcases hpos' i (by lia) with h' | h'
      · exact ⟨n, by lia, h'⟩
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

end Turing.MultiTapeTM
