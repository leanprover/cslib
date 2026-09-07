/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Nat.Order.Lemmas
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Acceptors: Turing machines that output only in their last step

An execution of a multi-tape Turing machine computes a (partial) function from strings to strings.
Deciding a language is defined on top of this as computing the indicator function of the language,
i.e. the machine either outputs nothing or a single default symbol.

This output can be performed at any step during the execution. Often it is much more convenient
to put this accept/reject verdict at the end of the computation. Many textbooks even use
specialized accept/reject states.

This file bridges the gap by introducing a normal form: A machine that performs an output only
on its last step. Any machine that outputs at most one symbol during its execution can be
transformed into this normal form, without changing the final output or the time and space bounds
of the computation.

The normalisation `delayOutput` buffers the symbol to be emitted in the state and flushes it in the
halting step. A machine that would emit a second symbol cannot be simulated with a one-symbol
buffer; such a machine cannot compute an indicator function anyway, so all symbols after the first
one are simply discarded.

## Main definitions

* `OutputsOnlyAtHalt`: the normal form — every transition that emits a symbol also halts,
* `delayOutput`: the normalisation construction.

## Main results

* `outputsOnlyAtHalt_delayOutput`: the constructed machine is in normal form,
* `computesInTimeAndSpace_delayOutput`: for outputs of length at most one,it computes the same
  output in exactly the same time and space; conversely,
* `exists_computesInTimeAndSpace_of_delayOutput` shows that it always computes the one-symbol
  truncation of the output of the simulated machine, in the same time and space,
* `exists_acceptor_computesFun_indicator`: a machine computing the indicator function of a language
  within given time and space bounds can be replaced by an acceptor with the same bounds.
-/

@[expose] public section

namespace Turing.MultiTapeTM

universe u v

variable {k : ℕ} {State : Type u} {Symbol : Type v} {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

section OutputNormalForm

/-- A Turing machine satisfying this condition has the property that whenever a transition emits a
symbol, that same transition halts the machine. Such a machine emits at most one symbol in its whole
run, namely in its very last step. -/
def OutputsOnlyAtHalt (tm : MultiTapeTM k Symbol State) : Prop :=
  ∀ q i w, (tm.tr q i w).outS ≠ none → (tm.tr q i w).q' = none

/-- A Turing machine that outputs only at the last step halts whenever it emits a symbol. -/
lemma OutputsOnlyAtHalt.state_step_eq_none_of_outputSymbol_ne_none
    (h : OutputsOnlyAtHalt tm) {cfg : Cfg k Symbol State input}
    (hne : tm.outputSymbol cfg ≠ none) :
    (tm.step cfg).state = none := by
  cases hstate : cfg.state with
  -- a halted machine stays halted, so `step_of_halt` closes this case
  | none => simp [hstate]
  | some q => simpa [step, hstate] using h q _ _ (by simpa [outputSymbol, hstate] using hne)

/-- A Turing machine that outputs only at the last step is halted whenever its output string is
non-empty. -/
lemma OutputsOnlyAtHalt.state_eq_none_of_outputString_ne_nil
    (h : OutputsOnlyAtHalt tm) (cfg : Cfg k Symbol State input) (t : ℕ)
    (hne : tm.outputString cfg t ≠ []) :
    (tm.configs cfg t).state = none := by
  -- A non-empty output means that some step `t' < t` emitted a symbol.
  have : ∃ t' < t, tm.outputSymbol (tm.configs cfg t') ≠ none := by simpa [outputString] using hne
  obtain ⟨t', hlt, hout⟩ := this
  -- That step halted the machine, and a halted machine stays halted.
  have hhalt : (tm.configs cfg (t' + 1)).state = none := by
    simpa [configs_succ_eq_step'] using h.state_step_eq_none_of_outputSymbol_ne_none hout
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlt
  rw [configs_add, configs_of_halts _ hhalt]
  exact hhalt

/-- The output string of a Turing machine that outputs only at the last step is always at most
one symbol long. -/
theorem OutputsOnlyAtHalt.outputString_length_le_one
    (h : OutputsOnlyAtHalt tm) (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.outputString cfg t).length ≤ 1 := by
  induction t with
  | zero => simp [outputString]
  | succ t ih =>
    rw [outputString_succ]
    by_cases hne : tm.outputString cfg t = []
    · grind
    · grind [outputSymbol_of_halt, state_eq_none_of_outputString_ne_nil]

/--
The state space of `delayOutput`: a state of the simulated machine together with the symbol emitted
so far, which serves as the one-symbol output buffer.
-/
abbrev DelayState (State Symbol : Type*) := State × Option Symbol

/-- Construct a TM with `OutputsOnlyAtHalt` from a TM `tm` that outputs at most one symbol:
We simulate `tm` step by step but instead of emitting a symbol, we store the symbol in the state.
The buffered symbol is flushed in the step in which the simulated machine halts.

The buffer keeps the *first* symbol emitted by `tm`; if `tm` emits further symbols (and thus
violates the assumption), they are discarded. `tm.delayOutput` therefore performs exactly the same
steps as `tm`, and in particular has the same time and space bounds. -/
def delayOutput (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM k Symbol (DelayState State Symbol) where
  q₀ := (tm.q₀, none)
  tr := fun (q, buf) i w =>
    let out := tm.tr q i w
    -- the first symbol emitted so far, including the one emitted by the simulated step
    let buf := buf.or out.outS
    { inputMove := out.inputMove
      workActions := out.workActions
      -- flush the buffer if and only if the simulated machine halts now
      outS := if out.q'.isNone then buf else none
      q' := out.q'.map (⟨·, buf⟩) }

/-- The `delayOutput` machine outputs only on the last step. -/
theorem outputsOnlyAtHalt_delayOutput (tm : MultiTapeTM k Symbol State) :
    OutputsOnlyAtHalt tm.delayOutput := by
  rintro ⟨q, buf⟩ i w h
  simp only [delayOutput] at h ⊢
  cases hq : (tm.tr q i w).q' with
  | none => simp
  | some q' => simp [hq] at h

end OutputNormalForm

section Simulation

/-!
## Correctness of `delayOutput`

The correctness proof is organised around the *encoding* `encodeCfg buf c`, which lifts a
configuration `c` of `tm` to the corresponding configuration of `tm.delayOutput` holding `buf` in
its output buffer. All the content of the simulation is in the two step-level lemmas
`step_encodeCfg` and `outputSymbol_encodeCfg`, which are pure case analyses on a single transition;
the statements about whole runs (`delayOutput_configs`, `delayOutput_outputString`) then follow by a
short induction on the number of steps.
-/

/-- The configuration of `tm.delayOutput` corresponding to a configuration `c` of `tm` with the
symbol `buf` in the output buffer. Everything except the state is copied verbatim. -/
@[simps -fullyApplied]
def encodeCfg (buf : Option Symbol) (c : Cfg k Symbol State input) :
    Cfg k Symbol (DelayState State Symbol) input where
  state := c.state.map (fun q => (q, buf))
  inputPos := c.inputPos
  workTapes := c.workTapes
  workTapePos := c.workTapePos

/-- `inputSymbol` and `workTapeSymbols` are not fields of `Cfg` but are computed from the fields
that `encodeCfg` copies verbatim, so they need their own simp lemmas. -/
@[simp]
lemma encodeCfg_inputSymbol {buf : Option Symbol} {c : Cfg k Symbol State input} :
    (encodeCfg buf c).inputSymbol = c.inputSymbol := rfl

@[simp]
lemma encodeCfg_workTapeSymbols {buf : Option Symbol} {c : Cfg k Symbol State input} :
    (encodeCfg buf c).workTapeSymbols = c.workTapeSymbols := rfl

lemma encodeCfg_state_eq_none {buf : Option Symbol} {c : Cfg k Symbol State input} :
    (encodeCfg buf c).state = none ↔ c.state = none := by
  simp [encodeCfg]

/-- One step of `tm.delayOutput` on an encoded configuration corresponds to one step of `tm`,
with the emitted symbol added to the buffer. -/
lemma step_encodeCfg {c : Cfg k Symbol State input} {buf : Option Symbol} :
    tm.delayOutput.step (encodeCfg buf c) =
      encodeCfg (buf.or (tm.outputSymbol c)) (tm.step c) := by
  cases hstate : c.state with
  | none => simp [step, outputSymbol, hstate]
  | some q => apply Cfg.ext <;> simp [step, delayOutput, outputSymbol, hstate]

/-- A running `tm.delayOutput` emits nothing, except in the step in which the simulated machine
halts, where it flushes its buffer. -/
lemma outputSymbol_encodeCfg {c : Cfg k Symbol State input}
    {buf : Option Symbol} (hstate : c.state ≠ none) :
    tm.delayOutput.outputSymbol (encodeCfg buf c) =
      if (tm.step c).state = none then buf.or (tm.outputSymbol c) else none := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hstate
  cases hq' : (tm.tr q c.inputSymbol c.workTapeSymbols).q' <;>
    simp [outputSymbol, step, delayOutput, hq, hq']

/-- After `t` steps, `tm.delayOutput` is in the encoding of the configuration of `tm`, with the
first symbol emitted by `tm` so far in its buffer. -/
theorem delayOutput_configs (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    tm.delayOutput.configs (tm.delayOutput.initCfg input) t =
      encodeCfg (tm.outputString (tm.initCfg input) t).head? (tm.configs (tm.initCfg input) t) := by
  induction t with
  | zero => simp [encodeCfg, delayOutput, outputString]
  | succ t ih =>
    rw [configs_succ_eq_step', ih, step_encodeCfg, configs_succ_eq_step', outputString_succ]
    grind

/-- The output of `tm.delayOutput`: nothing while `tm` is still running, and the first symbol
emitted by `tm` once `tm` has halted. -/
theorem delayOutput_outputString (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    tm.delayOutput.outputString (tm.delayOutput.initCfg input) t =
      if (tm.configs (tm.initCfg input) t).state = none then
        (tm.outputString (tm.initCfg input) t).take 1
      else
        [] := by
  induction t with
  | zero => simp [outputString, delayOutput]
  | succ t ih =>
    rw [outputString_succ, ih, delayOutput_configs tm input t, configs_succ_eq_step']
    by_cases hstate : (tm.configs (tm.initCfg input) t).state = none
    · -- `tm` has already halted: neither machine emits anything any more
      rw [outputSymbol_of_halt (encodeCfg_state_eq_none.mpr hstate), step_of_halt hstate,
        outputString_succ, outputSymbol_of_halt hstate]
      simp [hstate, -initCfg]
    · rw [outputSymbol_encodeCfg hstate]
      simp only [hstate, reduceIte, List.nil_append, outputString_succ]
      -- `tm` flushes the buffer exactly if it halts in this step; the buffer holds the head of
      -- the output emitted so far, which is what truncating to one symbol keeps
      split <;> cases tm.outputString (tm.initCfg input) t <;> simp

/-- `tm.delayOutput` halts exactly when `tm` halts. -/
theorem delayOutput_state_eq_none_iff (tm : MultiTapeTM k Symbol State) (input : List Symbol)
    (t : ℕ) :
    (tm.delayOutput.configs (tm.delayOutput.initCfg input) t).state = none ↔
      (tm.configs (tm.initCfg input) t).state = none := by
  rw [delayOutput_configs tm input t, encodeCfg_state_eq_none]

/-- Both machines use the same space: `delayOutput` copies the work tape actions verbatim, so the
work tape heads visit the same cells. -/
theorem delayOutput_spaceUsed (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    tm.delayOutput.spaceUsed (tm.delayOutput.initCfg input) t =
      tm.spaceUsed (tm.initCfg input) t := by
  refine spaceUsed_congr fun t' ht' => ?_
  rw [delayOutput_configs tm input t']
  rfl

/-- For outputs of length at most one, `tm.delayOutput` computes the same output in the same time
and space as the original Turing machine `tm`. -/
theorem computesInTimeAndSpace_delayOutput (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t s : ℕ) (h_short : output.length ≤ 1)
    (h : tm.ComputesInTimeAndSpace input output t s) :
    tm.delayOutput.ComputesInTimeAndSpace input output t s := by
  obtain ⟨h_halt, h_out, h_space⟩ := h
  have h_le : (tm.outputString (tm.initCfg input) t).length ≤ 1 := by rw [h_out]; exact h_short
  refine ⟨?_, ?_, ?_⟩
  · rw [delayOutput_state_eq_none_iff tm input t]; exact h_halt
  · -- the output of `tm` is short enough that truncating it to one symbol changes nothing
    rw [delayOutput_outputString, List.take_of_length_le h_le]
    simp only [h_halt, reduceIte]
    exact h_out
  · rw [delayOutput_spaceUsed tm input t]; exact h_space

/-- The converse direction of `computesInTimeAndSpace_delayOutput`: whatever `tm.delayOutput`
computes, `tm` computes in the same time and space, except that `tm.delayOutput` discards
everything after the first output symbol. -/
theorem exists_computesInTimeAndSpace_of_delayOutput (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t s : ℕ)
    (h : tm.delayOutput.ComputesInTimeAndSpace input output t s) :
    ∃ output', tm.ComputesInTimeAndSpace input output' t s ∧ output'.take 1 = output := by
  obtain ⟨h_halt, h_out, h_space⟩ := h
  rw [delayOutput_state_eq_none_iff tm input t] at h_halt
  rw [delayOutput_outputString tm input t] at h_out
  rw [delayOutput_spaceUsed tm input t] at h_space
  simp only [h_halt, reduceIte] at h_out
  exact ⟨_, ⟨h_halt, rfl, h_space⟩, h_out⟩

/-- If the output of `tm.delayOutput` determines that of `tm` — which is the case for the outputs
of length at most one that a decider produces — the simulation is exact. -/
theorem computesInTimeAndSpace_of_delayOutput (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t s : ℕ)
    (h_short : (tm.outputString (tm.initCfg input) t).length ≤ 1)
    (h : tm.delayOutput.ComputesInTimeAndSpace input output t s) :
    tm.ComputesInTimeAndSpace input output t s := by
  obtain ⟨output', ⟨h_halt, h_out, h_space⟩, hout'⟩ :=
    exists_computesInTimeAndSpace_of_delayOutput tm input output t s h
  subst h_out
  exact ⟨h_halt, by rw [← hout', List.take_of_length_le h_short], h_space⟩

/-- If `tm` outputs at most one symbol, `delayOutput` is equivalent to `tm`. -/
theorem computesInTimeAndSpace_delayOutput_iff (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t s : ℕ) (h_short : output.length ≤ 1)
    (h_short' : (tm.outputString (tm.initCfg input) t).length ≤ 1) :
    tm.delayOutput.ComputesInTimeAndSpace input output t s ↔
      tm.ComputesInTimeAndSpace input output t s :=
  ⟨computesInTimeAndSpace_of_delayOutput tm input output t s h_short',
    computesInTimeAndSpace_delayOutput tm input output t s h_short⟩

/--
Every Turing machine `tm` can be simulated (for the outputs of length at most one) by a Turing
machine `tm'` that outputs only at the last step.
Conversely, `tm'` runs for exactly as long and computes the one-symbol truncation of the
output of `tm`.
-/
theorem exists_outputsOnlyAtHalt (tm : MultiTapeTM k Symbol State) :
    ∃ (State' : Type (max u v)) (tm' : MultiTapeTM k Symbol State'),
      OutputsOnlyAtHalt tm' ∧
      (∀ input output t s, output.length ≤ 1 →
        tm.ComputesInTimeAndSpace input output t s →
          tm'.ComputesInTimeAndSpace input output t s) ∧
      (∀ input output t s, tm'.ComputesInTimeAndSpace input output t s →
        ∃ output', tm.ComputesInTimeAndSpace input output' t s ∧ output'.take 1 = output) :=
  ⟨_, tm.delayOutput, outputsOnlyAtHalt_delayOutput tm,
    fun input output t s h => computesInTimeAndSpace_delayOutput tm input output t s h,
    fun input output t s => exists_computesInTimeAndSpace_of_delayOutput tm input output t s⟩

end Simulation

/--
If a Turing machine computes the indicator function of a language `L` within time `t` and space `s`,
then it is computable in the same time and space by a machine that outputs only at the last step.
-/
theorem exists_acceptor_computesFun_indicator {IOSymbol : Type*} [Inhabited IOSymbol]
    {L : Language IOSymbol} {toMachineSymbol : IOSymbol ↪ Symbol}
    {t s : ℕ → ℕ} (h : tm.ComputesFunInTimeAndSpace (indicator L) toMachineSymbol t s) :
    ∃ tm' : MultiTapeTM k Symbol (DelayState State Symbol),
      OutputsOnlyAtHalt tm' ∧
        tm'.ComputesFunInTimeAndSpace (indicator L) toMachineSymbol t s := by
  refine ⟨tm.delayOutput, outputsOnlyAtHalt_delayOutput tm, fun input => ?_⟩
  obtain ⟨t', ht', s', hs', h⟩ := h input
  refine ⟨t', ht', s', hs', ?_⟩
  refine computesInTimeAndSpace_delayOutput tm _ _ t' s' ?_ h
  -- the indicator function returns `[]` or `[default]`
  by_cases hL : input ∈ L <;> simp [indicator, hL]

end Turing.MultiTapeTM
