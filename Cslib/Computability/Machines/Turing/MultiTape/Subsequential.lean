/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Automata.Transducers.Subsequential
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Order

/-!
# Turing machine simulation of subsequential transducers

The machine spends one step per emitted symbol with its input head stationary. A separate step
advances the head after each input symbol or halts after the final output. An empty chunk thus
takes one step. The finite control stores the transducer state and an index in the current chunk.

## Main results

* `Turing.MultiTapeTM.runFrom_ofSubsequential_mTr` simulates a labelled path in one Turing step
  per input and output symbol, leaving the machine ready for the next transition.
* `Turing.MultiTapeTM.computesInTimeAndSpace_ofSubsequential_of_translates` runs the path of a
  translation witness and emits the final output. Its time bound is the sum of the input and
  output lengths plus one.
* `Turing.MultiTapeTM.computableInTimeAndSpace_of_subsequential` applies this bound to any
  function on Boolean words realized by the labelled paths of a finite subsequential transducer.
  The compiled machine uses zero work tapes.
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

variable (t : SubsequentialTransducer State Symbol Symbol)

/-- Implement a subsequential transducer with zero work tapes. The bound `m` provides enough
finite control states to count the symbols of each emitted word. -/
def ofSubsequential (m : ℕ) : MultiTapeTM 0 Symbol (State × Fin (m + 1)) :=
  ofTr (t.start, 0) fun s inp _ =>
    inp.elim (emitChunk (t.final s.1) s.2 s.1 0 none) fun a =>
      emitChunk (t.step s.1 a).1 s.2 s.1 1 (some (t.step s.1 a).2)

private theorem exists_chunk_bound [Finite State] [Finite Symbol] :
    ∃ m, (∀ q a, (t.step q a).1.length ≤ m) ∧ ∀ q, (t.final q).length ≤ m := by
  obtain ⟨b, hb⟩ := Finite.exists_le fun p : State × Symbol => (t.step p.1 p.2).1.length
  obtain ⟨c, hc⟩ := Finite.exists_le fun q => (t.final q).length
  exact ⟨max b c, fun q a => le_max_of_le_left (hb (q, a)), fun q => le_max_of_le_right (hc q)⟩

/-- The compiled machine simulates an edge by emitting the label's output and moving right. -/
theorem runFrom_ofSubsequential_tr {q q' : State} {a : Symbol} {out : List Symbol}
    (edge : t.toLTS.Tr q (a, out) q') (hlen : out.length ≤ m)
    (c : Cfg 0 Symbol (State × Fin (m + 1)) input)
    (hq : c.state = some (q, 0)) (ha : c.inputSymbol = some a) :
    (ofSubsequential t m).runFrom c (out.length + 1) =
      { c with
        state := some (q', 0), inputPos := moveInputPos c.inputPos .pos,
        output := c.output ++ out } := by
  change t.step q a = (out, q') at edge
  exact runFrom_emitChunk (next := some q') c hq
    (fun j ws => by simp [ofSubsequential, ha, edge]) hlen

/-- A labelled path consumes its input and appends its output in one step per input
and output symbol. The machine is ready for the next chunk at the end of the path. -/
theorem runFrom_ofSubsequential_mTr (hstep : ∀ q a, (t.step q a).1.length ≤ m)
    {q q' : State} {labels : List (Symbol × List Symbol)} (path : t.toLTS.MTr q labels q')
    (pre post : List Symbol) (hin : input = pre ++ labels.map Prod.fst ++ post)
    (c : Cfg 0 Symbol (State × Fin (m + 1)) input)
    (hq : c.state = some (q, 0)) (hp : c.inputPos.val = pre.length + 1) :
    (ofSubsequential t m).runFrom c (labels.length + (labels.flatMap Prod.snd).length) =
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
      grind only [SubsequentialTransducer.toLTS_tr]
    have hpos : (moveInputPos c.inputPos .pos).val = (pre ++ [a]).length + 1 := by
      grind [moveInputPos_pos_of_ne_right]
    have edgeRun := runFrom_ofSubsequential_tr t edge hlen c hq ha
    have tailRun := ih (pre ++ [a]) (by simpa [List.append_assoc] using hin) _
      (congrArg Cfg.state edgeRun) (by simpa only [edgeRun] using hpos)
    rw [← runFrom_add, edgeRun] at tailRun
    simpa +arith [List.append_assoc] using tailRun

/-- A translation witness gives a zero-work-tape computation in one step per input
and output symbol plus one for halting. -/
theorem computesInTimeAndSpace_ofSubsequential_of_translates
    (hstep : ∀ q a, (t.step q a).1.length ≤ m) (hfinal : ∀ q, (t.final q).length ≤ m)
    {w out : List Symbol} (h : Transducer.Translates t w out) :
    (ofSubsequential t m).ComputesInTimeAndSpace w out (w.length + out.length + 1) 0 := by
  obtain ⟨labels, q, path, rfl, rfl⟩ := h
  let c := (ofSubsequential t m).initCfg (labels.map Prod.fst)
  have hp := runFrom_ofSubsequential_mTr t hstep path [] [] (by simp) c rfl rfl
  let d := (ofSubsequential t m).runFrom c (labels.length + (labels.flatMap Prod.snd).length)
  have blank : d.inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (.inr (by simp [d, hp]))
  have finish := runFrom_emitChunk (tm := ofSubsequential t m) (q := q) (move := 0) (next := none)
    d (by simp [d, hp]) (fun j ws => by simp [ofSubsequential, blank]) (hfinal q)
  dsimp only [d] at finish
  rw [← runFrom_add, hp] at finish
  have halt := congrArg Cfg.state finish
  refine ⟨⟨_, halt, ?_⟩, ?_, by simp⟩
  · simpa [c] using congrArg Cfg.output finish
  · simpa +arith using runsInTime_of_halted halt

/-- The compiled machine computes the transducer output in at most one step per input and
output symbol plus one, using zero work space. -/
theorem computesInTimeAndSpace_ofSubsequential
    (hstep : ∀ q a, (t.step q a).1.length ≤ m) (hfinal : ∀ q, (t.final q).length ≤ m)
    (w : List Symbol) :
    (ofSubsequential t m).ComputesInTimeAndSpace w (t.output w)
      (w.length + (t.output w).length + 1) 0 :=
  computesInTimeAndSpace_ofSubsequential_of_translates t hstep hfinal (by simp)

/-- A function on binary words realized by a finite subsequential transducer is computable
in time linear in the input and output lengths and in zero work space. -/
theorem computableInTimeAndSpace_of_subsequential {State : Type} [Finite State]
    (t : SubsequentialTransducer State Bool Bool) (f : List Bool → List Bool)
    (h : ∀ w, Transducer.Translates t w (f w)) :
    ComputableInTimeAndSpace f (Function.Embedding.refl _) (Function.Embedding.refl _)
      (fun w => w.length + (f w).length + 1) (fun _ => 0) := by
  obtain ⟨m, hstep, hfinal⟩ := exists_chunk_bound t
  exact ⟨0, _, inferInstance, ofSubsequential t m, fun w =>
    computesInTimeAndSpace_ofSubsequential_of_translates t hstep hfinal (h w)⟩

end Turing.MultiTapeTM
