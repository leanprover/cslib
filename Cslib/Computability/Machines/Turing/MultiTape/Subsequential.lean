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
# Turing machine simulation of sequential and subsequential transducers

The machine spends one step per emitted symbol with its input head stationary. A separate step
advances the head after each input symbol or halts after the final output. An empty chunk thus
takes one step.

## Main definitions

* `Turing.MultiTapeTM.ofSequential` compiles a sequential transducer to a machine with zero
  work tapes. Its finite control stores the position within the output word.
* `Turing.MultiTapeTM.ofSubsequential` uses the same compiler with the transducer's final output.

## Main results

* `Turing.MultiTapeTM.runFrom_ofSequential_tr` simulates one labelled transition.
  `Turing.MultiTapeTM.runFrom_ofSequential_mTr` simulates a path in one step per input and
  output symbol.
* `Turing.MultiTapeTM.computesInTimeAndSpace_ofSubsequential_of_translates` gives a time bound
  of input length plus output length plus one, including the final output and halting step.
* `Turing.MultiTapeTM.computableInTimeAndSpace_of_sequential` and
  `Turing.MultiTapeTM.computableInTimeAndSpace_of_subsequential` give this time bound and zero
  work space for functions on Boolean words realized by finite transducers.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib.Automata

variable {State Symbol : Type*}

/-- Emit the next symbol while holding the input head still. At the end of the chunk,
move the input head by `move` and enter `next`. -/
def emitChunk {m : ℕ} (out : List Symbol) (i : Fin (m + 1)) (q : State) (move : SignType)
    (next : Option State) : Action 0 Symbol (State × Fin (m + 1)) :=
  if h : i.val < out.length then
    ⟨0, Fin.elim0, some out[i.val], some (q, i + 1)⟩
  else ⟨move, Fin.elim0, none, next.map (·, 0)⟩

variable {input : List Symbol} {m : ℕ}

/-- From the beginning of a chunk, emitting its symbols and taking its completion step
appends the whole word, moves the input head and resets the counter. -/
private lemma runFrom_emitChunk {tm : MultiTapeTM 0 Symbol (State × Fin (m + 1))}
    {out : List Symbol} {q : State} {move : SignType} {next : Option State}
    (c : Cfg 0 Symbol (State × Fin (m + 1)) input) (hq : c.state = some (q, 0))
    (htr : ∀ j ws, tm.tr (q, j) c.inputSymbol ws = emitChunk out j q move next)
    (hlen : out.length ≤ m) :
    tm.runFrom c (out.length + 1) =
      { c with
        state := next.map (·, 0), inputPos := moveInputPos c.inputPos move,
        output := c.output ++ out } := by
  have emitPrefix (i : ℕ) (hi : i ≤ out.length) :
      tm.runFrom c i =
        { c with state := some (q, ⟨i, by lia⟩), output := c.output ++ out.take i } := by
    induction i with
    | zero => simp [runFrom, ← hq]
    | succ i ih =>
      have h : i < out.length := hi
      rw [runFrom_add, runFrom_one, ih h.le, step_of_state rfl]
      erw [htr]
      apply Cfg.ext_zero_tapes <;>
        simp [emitChunk, h, Fin.ext_iff, Fin.val_add_one, List.append_assoc]
      lia
  rw [runFrom_add, runFrom_one, emitPrefix _ le_rfl, step_of_state rfl]
  erw [htr]
  apply Cfg.ext_zero_tapes <;> simp [emitChunk]

variable (transducer : SequentialTransducer State Symbol Symbol)

/-- Compile a sequential transducer with zero work tapes. The machine emits `finalOut q` at
end of input in state `q`. For correct simulation, `m` must bound the length of every
transition output and every `finalOut q`. -/
def ofSequential (transducer : SequentialTransducer State Symbol Symbol) (m : ℕ)
    (finalOut : State → List Symbol := fun _ => []) :
    MultiTapeTM 0 Symbol (State × Fin (m + 1)) :=
  ofTr (transducer.start, 0) fun s inp _ =>
    inp.elim (emitChunk (finalOut s.1) s.2 s.1 0 none) fun a =>
      emitChunk (transducer.emit s.1 a) s.2 s.1 1 (some (transducer.tr s.1 a))

variable (finalOut : State → List Symbol)

/-- The compiled machine simulates an edge by emitting the label's output and moving right. -/
theorem runFrom_ofSequential_tr {q q' : State} {a : Symbol} {out : List Symbol}
    (edge : transducer.toIOLTS.Tr q (a, out) q') (hlen : out.length ≤ m)
    (c : Cfg 0 Symbol (State × Fin (m + 1)) input)
    (hq : c.state = some (q, 0)) (ha : c.inputSymbol = some a) :
    (ofSequential transducer m finalOut).runFrom c (out.length + 1) =
      { c with
        state := some (q', 0), inputPos := moveInputPos c.inputPos .pos,
        output := c.output ++ out } := by
  obtain ⟨hout, hnext⟩ := edge
  exact runFrom_emitChunk (next := some q') c hq
    (fun j ws => by simp [ofSequential, ha, hout, hnext]) hlen

/-- A labelled path consumes its input and appends its output in one step per input
and output symbol. The machine is ready for the next chunk at the end of the path. -/
theorem runFrom_ofSequential_mTr (hstep : ∀ q a, (transducer.emit q a).length ≤ m)
    {q q' : State} {labels : List (Symbol × List Symbol)}
    (path : transducer.toIOLTS.MTr q labels q')
    (pre post : List Symbol) (hin : input = pre ++ labels.map Prod.fst ++ post)
    (c : Cfg 0 Symbol (State × Fin (m + 1)) input)
    (hq : c.state = some (q, 0)) (hp : c.inputPos.val = pre.length + 1) :
    (ofSequential transducer m finalOut).runFrom c
        (labels.length + (labels.flatMap Prod.snd).length) =
      { c with
        state := some (q', 0),
        inputPos := ⟨pre.length + labels.length + 1, by simp +arith [hin]⟩,
        output := c.output ++ labels.flatMap Prod.snd } := by
  induction path generalizing pre c with
  | refl =>
    apply Cfg.ext_zero_tapes <;> simp [runFrom, hq, Fin.ext_iff, hp]
  | @stepL q label r labels s edge _ ih =>
    obtain ⟨a, out⟩ := label
    have ha : c.inputSymbol = some a := by
      subst input
      simpa using inputSymbolInner (cfg := c) pre.length (by lia) (by simp)
    have hlen : out.length ≤ m := by
      grind only [SequentialTransducer.toIOLTS_tr]
    have hpos : (moveInputPos c.inputPos .pos).val = (pre ++ [a]).length + 1 := by
      grind [moveInputPos_pos_of_ne_right]
    have edgeRun := runFrom_ofSequential_tr transducer finalOut edge hlen c hq ha
    have tailRun := ih (pre ++ [a]) (by simpa [List.append_assoc] using hin) _
      (congrArg Cfg.state edgeRun) (by simpa only [edgeRun] using hpos)
    rw [← runFrom_add, edgeRun] at tailRun
    simpa +arith [List.append_assoc] using tailRun

variable (transducer : SubsequentialTransducer State Symbol Symbol)

/-- Compile a subsequential transducer using its final output at end of input.
For correct simulation, `m` must bound the length of every transition output and final output. -/
abbrev ofSubsequential (transducer : SubsequentialTransducer State Symbol Symbol) (m : ℕ) :
    MultiTapeTM 0 Symbol (State × Fin (m + 1)) :=
  ofSequential transducer.toSequentialTransducer m transducer.finalOut

private theorem exists_chunk_bound [Finite State] [Finite Symbol] :
    ∃ m, (∀ q a, (transducer.emit q a).length ≤ m) ∧ ∀ q, (transducer.finalOut q).length ≤ m := by
  obtain ⟨b, hb⟩ := Finite.exists_le fun p : State × Symbol => (transducer.emit p.1 p.2).length
  obtain ⟨c, hc⟩ := Finite.exists_le fun q => (transducer.finalOut q).length
  exact ⟨max b c, fun q a => le_max_of_le_left (hb (q, a)), fun q => le_max_of_le_right (hc q)⟩

/-- The compiled machine simulates an edge by emitting the label's output and moving right. -/
theorem runFrom_ofSubsequential_tr {q q' : State} {a : Symbol} {out : List Symbol}
    (edge : transducer.toIOLTS.Tr q (a, out) q') (hlen : out.length ≤ m)
    (c : Cfg 0 Symbol (State × Fin (m + 1)) input)
    (hq : c.state = some (q, 0)) (ha : c.inputSymbol = some a) :
    (ofSubsequential transducer m).runFrom c (out.length + 1) =
      { c with
        state := some (q', 0), inputPos := moveInputPos c.inputPos .pos,
        output := c.output ++ out } :=
  runFrom_ofSequential_tr transducer.toSequentialTransducer transducer.finalOut edge hlen c hq ha

/-- A labelled path consumes its input and appends its output in one step per input
and output symbol. The machine is ready for the next chunk at the end of the path. -/
theorem runFrom_ofSubsequential_mTr (hstep : ∀ q a, (transducer.emit q a).length ≤ m)
    {q q' : State} {labels : List (Symbol × List Symbol)}
    (path : transducer.toIOLTS.MTr q labels q')
    (pre post : List Symbol) (hin : input = pre ++ labels.map Prod.fst ++ post)
    (c : Cfg 0 Symbol (State × Fin (m + 1)) input)
    (hq : c.state = some (q, 0)) (hp : c.inputPos.val = pre.length + 1) :
    (ofSubsequential transducer m).runFrom c
        (labels.length + (labels.flatMap Prod.snd).length) =
      { c with
        state := some (q', 0),
        inputPos := ⟨pre.length + labels.length + 1, by simp +arith [hin]⟩,
        output := c.output ++ labels.flatMap Prod.snd } :=
  runFrom_ofSequential_mTr transducer.toSequentialTransducer transducer.finalOut
    hstep path pre post hin c hq hp

/-- A translation witness gives a zero-work-tape computation in one step per input
and output symbol plus one for halting. -/
theorem computesInTimeAndSpace_ofSubsequential_of_translates
    (hstep : ∀ q a, (transducer.emit q a).length ≤ m)
    (hfinal : ∀ q, (transducer.finalOut q).length ≤ m)
    {w out : List Symbol} (h : Transducer.Translates transducer w out) :
    (ofSubsequential transducer m).ComputesInTimeAndSpace w out (w.length + out.length + 1) 0 := by
  obtain ⟨labels, q, path, rfl, rfl⟩ := h
  let c := (ofSubsequential transducer m).initCfg (labels.map Prod.fst)
  have hp := runFrom_ofSubsequential_mTr transducer hstep path [] [] (by simp) c rfl rfl
  let d := (ofSubsequential transducer m).runFrom c
    (labels.length + (labels.flatMap Prod.snd).length)
  have blank : d.inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (.inr (by simp [d, hp]))
  have finish := runFrom_emitChunk (tm := ofSubsequential transducer m) (q := q)
    (move := 0) (next := none) d (by simp [d, hp])
    (fun j ws => by simp [ofSubsequential, ofSequential, blank]) (hfinal q)
  dsimp only [d] at finish
  rw [← runFrom_add, hp] at finish
  have halt := congrArg Cfg.state finish
  refine ⟨⟨_, halt, ?_⟩, ?_, by simp⟩
  · simpa [c] using congrArg Cfg.output finish
  · simpa +arith using runsInTime_of_halted halt

/-- The compiled machine computes the transducer output in at most one step per input and
output symbol plus one, using zero work space. -/
theorem computesInTimeAndSpace_ofSubsequential
    (hstep : ∀ q a, (transducer.emit q a).length ≤ m)
    (hfinal : ∀ q, (transducer.finalOut q).length ≤ m)
    (w : List Symbol) :
    (ofSubsequential transducer m).ComputesInTimeAndSpace w (transducer.output w)
      (w.length + (transducer.output w).length + 1) 0 :=
  computesInTimeAndSpace_ofSubsequential_of_translates transducer hstep hfinal (by simp)

/-- A function on binary words realized by a finite subsequential transducer is computable
in time linear in the input and output lengths and in zero work space. -/
theorem computableInTimeAndSpace_of_subsequential {State : Type} [Finite State]
    (transducer : SubsequentialTransducer State Bool Bool) (f : List Bool → List Bool)
    (h : ∀ w, Transducer.Translates transducer w (f w)) :
    ComputableInTimeAndSpace f (Function.Embedding.refl _) (Function.Embedding.refl _)
      (fun w => w.length + (f w).length + 1) (fun _ => 0) := by
  obtain ⟨m, hstep, hfinal⟩ := exists_chunk_bound transducer
  exact ⟨0, _, inferInstance, ofSubsequential transducer m, fun w =>
    computesInTimeAndSpace_ofSubsequential_of_translates transducer hstep hfinal (h w)⟩

/-- A function realized by a finite sequential transducer has the same time and space bounds
as its subsequential extension with empty final output. -/
theorem computableInTimeAndSpace_of_sequential {State : Type} [Finite State]
    (transducer : SequentialTransducer State Bool Bool) (f : List Bool → List Bool)
    (h : ∀ w, Transducer.Translates transducer w (f w)) :
    ComputableInTimeAndSpace f (Function.Embedding.refl _) (Function.Embedding.refl _)
      (fun w => w.length + (f w).length + 1) (fun _ => 0) :=
  computableInTimeAndSpace_of_subsequential transducer.toSubsequential f fun w =>
    (transducer.toSubsequential_translates_iff ..).2 (h w)

end Turing.MultiTapeTM
