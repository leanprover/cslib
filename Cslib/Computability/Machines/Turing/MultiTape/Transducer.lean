/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.DA.Transducer
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Order

/-!
# Turing machine simulation of finite sequential and subsequential transducers

A function on Boolean words computed by a finite sequential or
subsequential transducer is computable by a multitape Turing machine in zero work space
and at most one step per input and output symbol, plus one step to halt.

The machine spends one step per emitted symbol with its input head stationary. A separate step
advances the head after each input symbol or halts after the final output. An empty chunk thus
takes one step.

## Main definitions

* `Turing.MultiTapeTM.ofSequential` compiles a sequential transducer to a machine with zero
  work tapes. Its finite control stores the position within the output word.
* `Turing.MultiTapeTM.ofSubsequential` uses the same compiler with the transducer's final output.
* `Turing.MultiTapeTM.transducerCfg` describes the machine between chunks using the transducer
  state, input head position, and output written so far.

## Main results

* `Turing.MultiTapeTM.runFrom_ofSequential_tr` simulates one transition.
  `Turing.MultiTapeTM.runFrom_ofSequential_mtr` simulates reading an input word in one step per
  input and output symbol.
* `Turing.MultiTapeTM.computesInTimeAndSpace_ofSubsequential` gives a time bound
  of input length plus output length plus one, including the final output and halting step.
* `Turing.MultiTapeTM.computableInTimeAndSpace_of_sequential` and
  `Turing.MultiTapeTM.computableInTimeAndSpace_of_subsequential` give this time bound and zero
  work space for functions on Boolean words realized by finite transducers.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib.Automata

variable {State Symbol : Type*}

/-- A TM `Action` to output the words emitted by a transducer symbol by symbol:
If `i` is in range, emit symbol `i` of `out` while holding the input head still. Otherwise,
move the input head by `move` and enter `next`. -/
def emitChunk {m : ℕ} (out : List Symbol) (i : Fin (m + 1)) (q : State) (move : SignType)
    (next : Option State) : Action 0 Symbol (State × Fin (m + 1)) :=
  if h : i.val < out.length then
    ⟨0, Fin.elim0, some out[i.val], some (q, i + 1)⟩
  else ⟨move, Fin.elim0, none, next.map (·, 0)⟩

variable {input : List Symbol} {m : ℕ}

/-- From the beginning of a chunk, emitting its symbols and taking its completion step
appends the whole word, moves the input head and resets the counter in the state. -/
private lemma runFrom_emitChunk {tm : MultiTapeTM 0 Symbol (State × Fin (m + 1))}
    {out : List Symbol} {q : State} {move : SignType} {next : Option State}
    (c : Cfg 0 Symbol (State × Fin (m + 1)) input) (hq : c.state = some (q, 0))
    (htr : ∀ j, tm.tr (q, j) c.inputSymbol c.workTapeSymbols = emitChunk out j q move next)
    (hlen : out.length ≤ m) :
    tm.runFrom c (out.length + 1) =
      { c with
        state := next.map (·, 0), inputPos := moveInputPos c.inputPos move,
        output := c.output ++ out } := by
  have emitPrefix (i : ℕ) (hi : i ≤ out.length) :
      tm.step^[i] c =
        { c with state := some (q, ⟨i, by lia⟩), output := c.output ++ out.take i } := by
    induction i with
    | zero => simp [← hq]
    | succ i ih =>
      change i < out.length at hi
      erw [Function.iterate_succ_apply', ih hi.le, step_of_state rfl, htr]
      apply Cfg.ext_zero_tapes <;>
        simp [emitChunk, hi, Fin.ext_iff, Fin.val_add_one, List.append_assoc]
      lia
  erw [runFrom, Function.iterate_succ_apply', emitPrefix _ le_rfl, step_of_state rfl, htr]
  apply Cfg.ext_zero_tapes <;> simp [emitChunk]

variable (transducer : SequentialTransducer State Symbol Symbol)

/-- Compile a sequential transducer with zero work tapes. The machine emits `finalOut q` at
end of input in state `q`. For correct simulation, `m` must bound the length of every
transition output and every `finalOut q`. -/
def ofSequential (transducer : SequentialTransducer State Symbol Symbol) (m : ℕ)
    (finalOut : State → List Symbol := fun _ => []) :
    MultiTapeTM 0 Symbol (State × Fin (m + 1)) :=
  ofTr (transducer.start, 0) fun ⟨q, i⟩ inp _ =>
    inp.elim (emitChunk (finalOut q) i q 0 none) fun a =>
      emitChunk (transducer.emit q a) i q 1 (some (transducer.tr q a))

variable (finalOut : State → List Symbol)

/-- A configuration between output chunks, with the counter reset to zero. -/
@[simps state inputPos output]
def transducerCfg (q : State) (pos : Fin (input.length + 2)) (written : List Symbol) :
    Cfg 0 Symbol (State × Fin (m + 1)) input :=
  ⟨some (q, 0), pos, fun _ _ => none, fun _ => 0, written⟩

/-- A transition consumes one input symbol and appends its output chunk. -/
theorem runFrom_ofSequential_tr (q : State) (a : Symbol) (hlen : (transducer.emit q a).length ≤ m)
    (pre post written : List Symbol) (hin : input = pre ++ a :: post) :
    (ofSequential transducer m finalOut).runFrom
        (transducerCfg (input := input) q ⟨pre.length + 1, by simp +arith [hin]⟩ written)
        ((transducer.emit q a).length + 1) =
      transducerCfg (transducer.tr q a) ⟨(pre ++ [a]).length + 1, by simp +arith [hin]⟩
        (written ++ transducer.emit q a) := by
  subst input
  let c := transducerCfg (input := pre ++ a :: post) (m := m) q
    ⟨pre.length + 1, by simp +arith⟩ written
  have ha : c.inputSymbol = some a := by
    simpa using inputSymbolInner (cfg := c) pre.length (by simp +arith [c]) (by simp)
  rw [runFrom_emitChunk (move := .pos) (next := some (transducer.tr q a)) c rfl
    (fun j => by simp [ofSequential, ha]) hlen]
  refine Cfg.ext_zero_tapes rfl ?_ rfl
  simpa +arith [c] using moveInputPos_pos_of_ne_right c.inputPos (by simp +arith [c])

/-- Reading an input word appends its transition outputs in one step per input and output
symbol. The machine is then ready for the next chunk in the state reached. -/
theorem runFrom_ofSequential_mtr (hstep : ∀ q a, (transducer.emit q a).length ≤ m)
    (q : State) (w pre post written : List Symbol) (hin : input = pre ++ w ++ post) :
    (ofSequential transducer m finalOut).runFrom
        (transducerCfg (input := input) q ⟨pre.length + 1, by simp +arith [hin]⟩ written)
        (w.length + (transducer.outputFrom q w).length) =
      transducerCfg (transducer.mtr q w) ⟨pre.length + w.length + 1, by simp +arith [hin]⟩
        (written ++ transducer.outputFrom q w) := by
  induction w generalizing q pre written with
  | nil => simp [runFrom]
  | cons a w ih =>
    have first := runFrom_ofSequential_tr transducer finalOut q a (hstep q a) pre (w ++ post)
      written (by simpa [List.append_assoc] using hin)
    specialize ih (transducer.tr q a) (pre ++ [a]) (written ++ transducer.emit q a)
      (by simpa [List.append_assoc] using hin)
    rw [← first] at ih
    have hmtr : transducer.mtr q (a :: w) = transducer.mtr (transducer.tr q a) w := rfl
    simpa +arith [runFrom, ← Function.iterate_add_apply, List.append_assoc, hmtr] using ih

variable (transducer : SubsequentialTransducer State Symbol Symbol)

/-- Compile a subsequential transducer using its final output at end of input.
For correct simulation, `m` must bound the length of every transition output and final output. -/
abbrev ofSubsequential (transducer : SubsequentialTransducer State Symbol Symbol) (m : ℕ) :
    MultiTapeTM 0 Symbol (State × Fin (m + 1)) :=
  ofSequential transducer.toSequentialTransducer m transducer.finalOut

private theorem exists_chunk_bound [Finite State] [Finite Symbol] :
    ∃ m, transducer.OutputBoundedBy m := by
  obtain ⟨m, hm⟩ := Finite.exists_le fun p : State × Option Symbol =>
    (p.2.elim (transducer.finalOut p.1) (transducer.emit p.1)).length
  exact ⟨m, fun q a => hm (q, a)⟩

/-- The compiled machine computes the transducer output in at most one step per input and
output symbol plus one, using zero work space. -/
theorem computesInTimeAndSpace_ofSubsequential
    (hbound : transducer.OutputBoundedBy m)
    (w : List Symbol) :
    (ofSubsequential transducer m).ComputesInTimeAndSpace w (transducer.output w)
      (w.length + (transducer.output w).length + 1) 0 := by
  let c := (ofSubsequential transducer m).initCfg w
  let q := transducer.mtr transducer.start w
  let d := transducerCfg (input := w) (m := m) q ⟨w.length + 1, by simp +arith⟩
    (transducer.toSequentialTransducer.output w)
  have wordRun : (ofSubsequential transducer m).runFrom c
      (w.length + (transducer.toSequentialTransducer.output w).length) = d := by
    simpa using!
      runFrom_ofSequential_mtr transducer.toSequentialTransducer transducer.finalOut
        (fun q a => hbound q (some a)) (input := w) transducer.start w [] [] [] (by simp)
  have blank : d.inputSymbol = none := inputSymbol_eq_none_of_boundary (.inr (by simp [d]))
  have finish := runFrom_emitChunk (tm := ofSubsequential transducer m)
    (out := transducer.finalOut q) (move := 0) (next := none) d rfl
    (fun j => by simp [ofSubsequential, ofSequential, blank]) (hbound q none)
  conv_lhs at finish => rw [← wordRun]
  simp only [runFrom, ← Function.iterate_add_apply] at finish
  have halt := congrArg Cfg.state finish
  have hout : transducer.output w =
      transducer.toSequentialTransducer.output w ++ transducer.finalOut q :=
    transducer.outputFrom_eq_append _ w
  refine ⟨⟨_, halt, ?_⟩, ?_, by simp⟩
  · simpa [runFrom, c, d, hout] using congrArg Cfg.output finish
  · simpa +arith [hout] using runsInTime_of_halted halt

/-- A function on binary words realized by a finite subsequential transducer is computable
in time linear in the input and output lengths and in zero work space. -/
theorem computableInTimeAndSpace_of_subsequential {State : Type} [Finite State]
    (transducer : SubsequentialTransducer State Bool Bool) (f : List Bool → List Bool)
    (h : ∀ w, Transducer.Translates transducer w (f w)) :
    ComputableInTimeAndSpace f (Function.Embedding.refl _) (Function.Embedding.refl _)
      (fun w => w.length + (f w).length + 1) (fun _ => 0) := by
  obtain ⟨m, hbound⟩ := exists_chunk_bound transducer
  refine ⟨0, _, inferInstance, ofSubsequential transducer m, fun w => ?_⟩
  have hw : transducer.output w = f w := h w
  simpa [hw] using computesInTimeAndSpace_ofSubsequential transducer hbound w

/-- A function realized by a finite sequential transducer has the same time and space bounds
as its subsequential extension with empty final output. -/
theorem computableInTimeAndSpace_of_sequential {State : Type} [Finite State]
    (transducer : SequentialTransducer State Bool Bool) (f : List Bool → List Bool)
    (h : ∀ w, Transducer.Translates transducer w (f w)) :
    ComputableInTimeAndSpace f (Function.Embedding.refl _) (Function.Embedding.refl _)
      (fun w => w.length + (f w).length + 1) (fun _ => 0) :=
  computableInTimeAndSpace_of_subsequential transducer.toSubsequential f h

end Turing.MultiTapeTM
