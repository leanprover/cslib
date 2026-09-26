/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# A machine that rewinds a work-tape head

A two-state machine that returns the head of one designated work tape `i` to position `0` — the
start of the word — from the frontier just past the word, and halts there. It never writes to any
tape, never moves the input head, never moves any other work head and never outputs, so a
combinator can run it between two phases of a computation to re-normalise a work-tape head without
disturbing anything else.

Tape `i` holds a word `w` in cells `0, …, w.length - 1` and is blank everywhere else, and the head
starts at the frontier cell `w.length`. In its initial state `start` the machine takes one
unconditional step left, into state `scan`. In state `scan` it walks left over the symbols of `w`;
the first blank it reads is the cell at position `-1`, and the halting transition moves the head
right, back onto position `0`.

On a word of length `L` the run halts after `L + 2` steps. The designated head visits exactly the
cells `-1, …, L`; every tape's contents and every other head remain unchanged.

## Main results

* `Turing.MultiTapeTM.exists_rewindTape`: the machine that rewinds a work-tape head to the start of
  its word.
-/

namespace Turing.MultiTapeTM

variable {K : ℕ} {Symbol : Type*} {input : List Symbol}

/-- The control states of the work-tape-rewinding machine: `start` takes one unconditional step
left, `scan` walks left towards the start of the word. -/
inductive RewindTapeState : Type
  | start
  | scan

instance : Finite RewindTapeState :=
  Finite.of_injective
    (fun q => match q with
      | .start => (0 : Fin 2)
      | .scan => 1)
    (fun a b h => by cases a <;> cases b <;> first | rfl | exact absurd h (by decide))

/-- The work-tape-rewinding machine for tape `i`. In state `start` it moves the head of tape `i`
left, unconditionally, and enters state `scan`. In state `scan` it moves left over a symbol,
staying in `scan`; on the first blank it moves right and halts. No tape is ever written, the input
head never moves, no other work head moves and nothing is output. -/
def rewindTape (i : Fin K) : MultiTapeTM K Symbol RewindTapeState where
  q₀ := .start
  tr q _ work :=
    match q, work i with
    | .start, _ =>
        { inputTape := 0, workTapes := fun l => (none, if l = i then -1 else 0),
          output := none, state := some .scan }
    | .scan, some _ =>
        { inputTape := 0, workTapes := fun l => (none, if l = i then -1 else 0),
          output := none, state := some .scan }
    | .scan, none =>
        { inputTape := 0, workTapes := fun l => (none, if l = i then 1 else 0),
          output := none, state := none }

namespace RewindTape

variable {i : Fin K} {ip : Fin (input.length + 2)} {W : Fin K → ℤ → Option Symbol}
  {WP : Fin K → ℤ} {out : List Symbol} {p : ℤ}

/-- A configuration of the rewinding machine: state `q`, the head of tape `i` at `p`, every other
field frozen — tape contents `W`, the other heads `WP`, the input head `ip` and output `out`. -/
def cfg (input : List Symbol) (i : Fin K) (q : Option RewindTapeState)
    (ip : Fin (input.length + 2)) (W : Fin K → ℤ → Option Symbol) (WP : Fin K → ℤ)
    (out : List Symbol) (p : ℤ) : Cfg K Symbol RewindTapeState input :=
  ⟨q, ip, W, Function.update WP i p, out⟩

/-- Configurations of the shape `cfg` are equal as soon as the tape-`i` head positions agree. -/
lemma cfg_congr {q : Option RewindTapeState} {p p' : ℤ} (hp : p = p') :
    cfg input i q ip W WP out p = cfg input i q ip W WP out p' := by
  rw [hp]

/-- Moving the head of tape `i` left in state `start`, unconditionally, entering `scan`. -/
lemma step_start :
    (rewindTape i).step (cfg input i (some .start) ip W WP out p) =
      cfg input i (some .scan) ip W WP out (p - 1) := by
  simp only [step, cfg, rewindTape]
  refine Cfg.ext rfl (by simp) (by simp) (funext fun l => ?_) (by simp)
  by_cases h : l = i <;> simp [h, sub_eq_add_neg]

/-- Walking left in state `scan`: over a symbol the head moves left and stays in `scan`. -/
lemma step_scan_some {s : Symbol} (hs : W i p = some s) :
    (rewindTape i).step (cfg input i (some .scan) ip W WP out p) =
      cfg input i (some .scan) ip W WP out (p - 1) := by
  simp only [step, cfg, rewindTape, Cfg.workTapeSymbols, Function.update_self, hs]
  refine Cfg.ext rfl (by simp) (by simp) (funext fun l => ?_) (by simp)
  by_cases h : l = i <;> simp [h, sub_eq_add_neg]

/-- Halting in state `scan`: on the first blank — the cell at position `-1` — the head moves right
and the machine halts. -/
lemma step_scan_none (hs : W i p = none) :
    (rewindTape i).step (cfg input i (some .scan) ip W WP out p) =
      cfg input i none ip W WP out (p + 1) := by
  simp only [step, cfg, rewindTape, Cfg.workTapeSymbols, Function.update_self, hs]
  refine Cfg.ext rfl (by simp) (by simp) (funext fun l => ?_) (by simp)
  by_cases h : l = i <;> simp [h]

/-- The scanning phase: from `scan` at the last cell of the word, after `n ≤ w.length` steps the
head has walked left `n` cells, over untouched symbols. -/
lemma runFrom_scan {w : List Symbol} (hw : W i = tapeOfList w) (n : ℕ) (hn : n ≤ w.length) :
    (rewindTape i).runFrom (cfg input i (some .scan) ip W WP out ((w.length : ℤ) - 1)) n =
      cfg input i (some .scan) ip W WP out ((w.length : ℤ) - 1 - n) := by
  induction n with
  | zero => simp [runFrom]
  | succ n ih =>
    have hpos : (w.length : ℤ) - 1 - n = ((w.length - 1 - n : ℕ) : ℤ) := by omega
    have hsym : W i ((w.length : ℤ) - 1 - n) = some (w[w.length - 1 - n]'(by omega)) := by
      rw [hw, hpos, tapeOfList_ofNat]
      exact List.getElem?_eq_getElem (by omega)
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega), step_scan_some hsym]
    exact cfg_congr (by omega)

/-- The complete run: from `start` at the frontier `w.length`, after `w.length + 2` steps the
machine has halted with the head of tape `i` back at position `0`. -/
lemma runFrom_full {w : List Symbol} (hw : W i = tapeOfList w) :
    (rewindTape i).runFrom (cfg input i (some .start) ip W WP out (w.length : ℤ)) (w.length + 2) =
      cfg input i none ip W WP out 0 := by
  rw [runFrom, Function.iterate_succ_apply, step_start, Function.iterate_succ_apply',
    ← runFrom, runFrom_scan hw w.length le_rfl]
  rw [show (w.length : ℤ) - 1 - w.length = -1 by omega]
  rw [step_scan_none (by rw [hw]; exact tapeOfList_negSucc w 0)]
  simp

/-- Throughout the run, the head of tape `i` stays within `[-1, w.length]`: it walks from the
frontier down to `-1` and back to `0`, never leaving that interval. -/
lemma runFrom_pos_range {w : List Symbol} (hw : W i = tapeOfList w) (m : ℕ)
    (hm : m ≤ w.length + 2) :
    -1 ≤ ((rewindTape i).runFrom
        (cfg input i (some .start) ip W WP out (w.length : ℤ)) m).workTapePos i ∧
      ((rewindTape i).runFrom
        (cfg input i (some .start) ip W WP out (w.length : ℤ)) m).workTapePos i ≤
        (w.length : ℤ) := by
  rcases m with _ | m
  · simp [runFrom, cfg]
  rcases Nat.lt_or_ge m (w.length + 1) with hlt | hge
  · -- After the initial left move, take `m` scanning steps.
    rw [runFrom, Function.iterate_succ_apply, step_start, ← runFrom,
      runFrom_scan hw m (by omega)]
    simp only [cfg, Function.update_self]
    constructor <;> omega
  · obtain rfl : m = w.length + 1 := by omega
    rw [runFrom_full hw]
    simp [cfg]

/-- No action of the machine writes to a work tape. -/
lemma tr_write_none (q : RewindTapeState) (inp : Option Symbol) (work : Fin K → Option Symbol)
    (l : Fin K) : (((rewindTape i).tr q inp work).workTapes l).1 = none := by
  simp only [rewindTape]
  cases q <;> cases work i <;> rfl

/-- No action of the machine moves the input head. -/
lemma tr_inputTape (q : RewindTapeState) (inp : Option Symbol) (work : Fin K → Option Symbol) :
    ((rewindTape i).tr q inp work).inputTape = 0 := by
  simp only [rewindTape]
  cases q <;> cases work i <;> rfl

/-- No action of the machine outputs. -/
lemma tr_output (q : RewindTapeState) (inp : Option Symbol) (work : Fin K → Option Symbol) :
    ((rewindTape i).tr q inp work).output = none := by
  simp only [rewindTape]
  cases q <;> cases work i <;> rfl

/-- No action of the machine moves a work head other than the head of tape `i`. -/
lemma tr_move_ne (q : RewindTapeState) (inp : Option Symbol) (work : Fin K → Option Symbol)
    {l : Fin K} (h : l ≠ i) : (((rewindTape i).tr q inp work).workTapes l).2 = 0 := by
  simp only [rewindTape]
  cases q <;> cases work i <;> simp [h]

/-- One step preserves the input head, the output, every tape's contents and every work head other
than the head of tape `i`. -/
lemma step_frame (c : Cfg K Symbol RewindTapeState input) :
    ((rewindTape i).step c).inputPos = c.inputPos ∧
      ((rewindTape i).step c).output = c.output ∧
      (∀ j, ((rewindTape i).step c).workTapes j = c.workTapes j) ∧
      (∀ j, j ≠ i → ((rewindTape i).step c).workTapePos j = c.workTapePos j) := by
  cases hc : c.state with
  | none => rw [step_of_halt hc]; exact ⟨rfl, rfl, fun _ => rfl, fun _ _ => rfl⟩
  | some q =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [step_inputPos_of_state hc, tr_inputTape, moveInputPos_zero]
    · rw [step_apply_of_state hc, Action.apply_output, tr_output]; simp
    · intro j
      rw [step_workTapes_of_state hc, tr_write_none q c.inputSymbol c.workTapeSymbols j]
    · intro j hj
      rw [step_workTapePos_of_state hc, tr_move_ne q c.inputSymbol c.workTapeSymbols hj]
      simp

/-- The whole run preserves the input head, the output, every tape's contents and every work head
other than the head of tape `i`. -/
lemma runFrom_frame (c : Cfg K Symbol RewindTapeState input) (m : ℕ) :
    ((rewindTape i).runFrom c m).inputPos = c.inputPos ∧
      ((rewindTape i).runFrom c m).output = c.output ∧
      (∀ j, ((rewindTape i).runFrom c m).workTapes j = c.workTapes j) ∧
      (∀ j, j ≠ i → ((rewindTape i).runFrom c m).workTapePos j = c.workTapePos j) := by
  induction m with
  | zero => exact ⟨rfl, rfl, fun _ => rfl, fun _ _ => rfl⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3, h4⟩ := step_frame ((rewindTape i).runFrom c m)
    rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    exact ⟨h1.trans ih.1, h2.trans ih.2.1, fun j => (h3 j).trans (ih.2.2.1 j),
      fun j hj => (h4 j hj).trans (ih.2.2.2 j hj)⟩

end RewindTape

open RewindTape in
/-- **The machine that rewinds a work-tape head.** One machine per tape index `i`: started with
tape `i` holding a word `w` in cells `0, …, w.length - 1` and the head at the frontier `w.length`,
it halts within `w.length + 3` steps with the head back at position `0` and every other field —
input head, output, all tape contents and all other work heads — unchanged at every step of the
run. Before the halting step the machine is live, so runs chain sequentially. -/
public theorem exists_rewindTape {Symbol : Type*} {K : ℕ} (i : Fin K) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM K Symbol State),
      ∀ (input : List Symbol) (c : Cfg K Symbol State input) (w : List Symbol),
        c.state = some tm.q₀ →
        c.workTapes i = tapeOfList w →
        c.workTapePos i = (w.length : ℤ) →
        ∃ u ≤ w.length + 3,
          (∀ m < u, (tm.runFrom c m).state ≠ none) ∧
          tm.runFrom c u = ⟨none, c.inputPos, c.workTapes,
            Function.update c.workTapePos i 0, c.output⟩ ∧
          ∀ m ≤ u, (tm.runFrom c m).inputPos = c.inputPos ∧ (tm.runFrom c m).output = c.output ∧
            (∀ j, j ≠ i → (tm.runFrom c m).workTapes j = c.workTapes j ∧
              (tm.runFrom c m).workTapePos j = c.workTapePos j) ∧
            (tm.runFrom c m).workTapes i = c.workTapes i ∧
            -1 ≤ (tm.runFrom c m).workTapePos i ∧
            (tm.runFrom c m).workTapePos i ≤ (w.length : ℤ) := by
  refine ⟨RewindTapeState, inferInstance, rewindTape i, fun input c w hstate hwi hwp => ?_⟩
  have hc0 : c = cfg input i (some .start) c.inputPos c.workTapes c.workTapePos c.output
      (w.length : ℤ) := by
    refine Cfg.ext hstate rfl rfl ?_ rfl
    simp [cfg, ← hwp]
  have hrun := runFrom_full (ip := c.inputPos) (WP := c.workTapePos) (out := c.output) hwi
  rw [← hc0] at hrun
  obtain ⟨u, hu, hhalt, hactive⟩ :=
    exists_minimal_halting_time (rewindTape i) c (w.length + 2) (by rw [hrun]; rfl)
  refine ⟨u, by omega, hactive, ?_, fun m hm => ?_⟩
  · exact (runFrom_eq_of_halt (rewindTape i) c hu hhalt).symm.trans hrun
  · obtain ⟨f1, f2, f3, f4⟩ := runFrom_frame c m
    have hrange := runFrom_pos_range (ip := c.inputPos) (WP := c.workTapePos)
      (out := c.output) hwi m (hm.trans hu)
    rw [← hc0] at hrange
    exact ⟨f1, f2, fun j hj => ⟨f3 j, f4 j hj⟩, f3 i, hrange⟩

end Turing.MultiTapeTM
