/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# A machine that rewinds the input head

A three-state machine that returns the input head to position `1` — the first input symbol — from
an arbitrary starting configuration and halts there. It never writes to a work tape, never moves a
work-tape head and never outputs, so a combinator can run it between two phases of a computation
to re-normalise the input head without disturbing anything else.

In its initial state `probe` the machine reads the cell under the input head. A symbol means the
head is inside the input (positions `1, …, input.length`) and the machine starts walking left. A
blank means the head is at one of the two boundary positions `0` and `input.length + 1`, and one
more probe a cell to the left disambiguates: in state `probe2`, a symbol identifies the right
boundary of a nonempty input and the machine walks left, while a blank means the head started at
the left boundary or the input is empty, so moving right lands on position `1` and the machine
halts. In state `walk` the machine moves left over symbols; the first blank is the cell at
position `0`, and the halting transition moves right, onto position `1`.

From any starting position the run halts within `input.length + 2` steps.

## Main results

* `Turing.MultiTapeTM.exists_rewindInput`: the machine that rewinds the input head.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*} {input : List Symbol}

/-- The control states of the rewinding machine: `probe` reads the starting cell, `probe2` reads
the cell to its left when the first read was blank, and `walk` moves left towards the input
boundary. -/
inductive RewindState : Type
  | probe
  | probe2
  | walk

instance : Finite RewindState :=
  Finite.of_injective
    (fun q => match q with
      | .probe => (0 : Fin 3)
      | .probe2 => 1
      | .walk => 2)
    (fun a b h => by cases a <;> cases b <;> first | rfl | exact absurd h (by decide))

/-- The rewinding machine. Reading a symbol, every state turns to `walk` and moves the input head
left; reading a blank, `probe` moves left into `probe2` while `probe2` and `walk` move right and
halt. No work tape is ever written or moved and nothing is output. -/
def rewindInput (k : ℕ) (Symbol : Type*) : MultiTapeTM k Symbol RewindState where
  q₀ := .probe
  tr q inp _ :=
    match q, inp with
    | .probe, some _ =>
        { inputTape := .neg, workTapes := fun _ => (none, 0), output := none,
          state := some .walk }
    | .probe, none =>
        { inputTape := .neg, workTapes := fun _ => (none, 0), output := none,
          state := some .probe2 }
    | .probe2, some _ =>
        { inputTape := .neg, workTapes := fun _ => (none, 0), output := none,
          state := some .walk }
    | .probe2, none =>
        { inputTape := .pos, workTapes := fun _ => (none, 0), output := none,
          state := none }
    | .walk, some _ =>
        { inputTape := .neg, workTapes := fun _ => (none, 0), output := none,
          state := some .walk }
    | .walk, none =>
        { inputTape := .pos, workTapes := fun _ => (none, 0), output := none,
          state := none }

namespace Rewind

variable {w : Fin k → ℤ → Option Symbol} {wp : Fin k → ℤ} {out : List Symbol}
  {p : Fin (input.length + 2)}

/-- The value of the input position after a left move: truncated subtraction in `ℕ` captures the
clamping at the left boundary. -/
lemma val_moveInputPos_neg {n : ℕ} (p : Fin (n + 2)) :
    (moveInputPos p .neg).val = p.val - 1 := by
  rcases eq_or_ne p 0 with rfl | h
  · simp
  · rw [moveInputPos_neg_of_ne_left p h]

/-- The value of the input position after a right move away from the right boundary. -/
lemma val_moveInputPos_pos {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ n + 1) :
    (moveInputPos p .pos).val = p.val + 1 := by
  rw [moveInputPos_pos_of_ne_right p h]

/-- Configurations that differ only in provably equal input positions are equal. -/
lemma cfg_congr {q : Option RewindState} {p p' : Fin (input.length + 2)} (h : p.val = p'.val) :
    (⟨q, p, w, wp, out⟩ : Cfg k Symbol RewindState input) = ⟨q, p', w, wp, out⟩ := by
  rw [Fin.ext h]

/-- The symbol read with the input head inside the input. -/
lemma inputSymbol_mk_eq_some {q : Option RewindState} (h1 : p.val ≠ 0)
    (h2 : p.val ≠ input.length + 1) :
    (⟨q, p, w, wp, out⟩ : Cfg k Symbol RewindState input).inputSymbol =
      some (input[p.val - 1]'(by have := p.isLt; omega)) :=
  inputSymbolInner (p.val - 1) (show p.val = 1 + (p.val - 1) by omega)
    (by have := p.isLt; omega)

/-- The blank read at the left boundary. -/
lemma inputSymbol_mk_eq_none_left {q : Option RewindState} (h : p = 0) :
    (⟨q, p, w, wp, out⟩ : Cfg k Symbol RewindState input).inputSymbol = none := by
  subst h
  simp [Cfg.inputSymbol]

/-- The blank read at the right boundary. -/
lemma inputSymbol_mk_eq_none_right {q : Option RewindState} (h : p.val = input.length + 1) :
    (⟨q, p, w, wp, out⟩ : Cfg k Symbol RewindState input).inputSymbol = none := by
  grind [Cfg.inputSymbol]

/-- No action of the rewinding machine writes to a work tape or moves a work head. -/
lemma tr_workTapes (q : RewindState) (inp : Option Symbol) (work : Fin k → Option Symbol)
    (i : Fin k) : ((rewindInput k Symbol).tr q inp work).workTapes i = (none, 0) := by
  cases q <;> cases inp <;> rfl

/-- The rewinding machine never outputs. -/
lemma tr_output (q : RewindState) (inp : Option Symbol) (work : Fin k → Option Symbol) :
    ((rewindInput k Symbol).tr q inp work).output = none := by
  cases q <;> cases inp <;> rfl

/-- Applying an action that writes nothing, moves no work head and outputs nothing changes only
the state and the input position. -/
lemma apply_action (a : Action k Symbol RewindState)
    (ha1 : ∀ i, a.workTapes i = (none, 0)) (ha2 : a.output = none)
    (c : Cfg k Symbol RewindState input) :
    a.apply c =
      ⟨a.state, moveInputPos c.inputPos a.inputTape, c.workTapes, c.workTapePos, c.output⟩ := by
  refine Cfg.ext rfl rfl (funext fun i => ?_) (funext fun i => ?_) ?_ <;>
    simp [ha1, ha2, SignType.cast]

/-- One step from a live state applies the transition to the symbols read. -/
lemma step_mk (q : RewindState) :
    (rewindInput k Symbol).step ⟨some q, p, w, wp, out⟩ =
      ((rewindInput k Symbol).tr q
          (Cfg.inputSymbol ⟨some q, p, w, wp, out⟩)
          (Cfg.workTapeSymbols ⟨some q, p, w, wp, out⟩)).apply
        ⟨some q, p, w, wp, out⟩ := rfl

/-- Reading a symbol, every state turns to `walk` and moves the input head left. -/
lemma step_read (q : RewindState) {s : Symbol}
    (hs : (⟨some q, p, w, wp, out⟩ : Cfg k Symbol RewindState input).inputSymbol = some s) :
    (rewindInput k Symbol).step ⟨some q, p, w, wp, out⟩ =
      ⟨some .walk, moveInputPos p .neg, w, wp, out⟩ := by
  rw [step_mk, hs]
  cases q <;> exact apply_action _ (fun _ => rfl) rfl _

/-- Reading a blank in `probe`, the machine moves left and probes again. -/
lemma step_probe_none
    (hs : (⟨some .probe, p, w, wp, out⟩ : Cfg k Symbol RewindState input).inputSymbol = none) :
    (rewindInput k Symbol).step ⟨some .probe, p, w, wp, out⟩ =
      ⟨some .probe2, moveInputPos p .neg, w, wp, out⟩ := by
  rw [step_mk, hs]
  exact apply_action _ (fun _ => rfl) rfl _

/-- Reading a blank in `probe2`, the head started at the left boundary or the input is empty:
the machine moves right, onto position `1`, and halts. -/
lemma step_probe2_none
    (hs : (⟨some .probe2, p, w, wp, out⟩ : Cfg k Symbol RewindState input).inputSymbol = none) :
    (rewindInput k Symbol).step ⟨some .probe2, p, w, wp, out⟩ =
      ⟨none, moveInputPos p .pos, w, wp, out⟩ := by
  rw [step_mk, hs]
  exact apply_action _ (fun _ => rfl) rfl _

/-- Reading a blank in `walk`, the head is at position `0`: the machine moves right, onto
position `1`, and halts. -/
lemma step_walk_none
    (hs : (⟨some .walk, p, w, wp, out⟩ : Cfg k Symbol RewindState input).inputSymbol = none) :
    (rewindInput k Symbol).step ⟨some .walk, p, w, wp, out⟩ =
      ⟨none, moveInputPos p .pos, w, wp, out⟩ := by
  rw [step_mk, hs]
  exact apply_action _ (fun _ => rfl) rfl _

/-- One step never changes the work tapes, the work heads or the output. -/
lemma step_frame (c : Cfg k Symbol RewindState input) :
    ((rewindInput k Symbol).step c).workTapes = c.workTapes ∧
      ((rewindInput k Symbol).step c).workTapePos = c.workTapePos ∧
      ((rewindInput k Symbol).step c).output = c.output := by
  obtain ⟨q, p, w, wp, out⟩ := c
  cases q with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some q =>
    rw [step_mk, apply_action _ (fun i => tr_workTapes q _ _ i) (tr_output q _ _)]
    exact ⟨rfl, rfl, rfl⟩

/-- The run never changes the work tapes, the work heads or the output. -/
lemma runFrom_frame (c : Cfg k Symbol RewindState input) (m : ℕ) :
    ((rewindInput k Symbol).runFrom c m).workTapes = c.workTapes ∧
      ((rewindInput k Symbol).runFrom c m).workTapePos = c.workTapePos ∧
      ((rewindInput k Symbol).runFrom c m).output = c.output := by
  induction m with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := step_frame ((rewindInput k Symbol).runFrom c m)
    rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    exact ⟨h1.trans ih.1, h2.trans ih.2.1, h3.trans ih.2.2⟩

/-- One step of the run, as an equation on `runFrom`. -/
lemma runFrom_one (c : Cfg k Symbol RewindState input) :
    (rewindInput k Symbol).runFrom c 1 = (rewindInput k Symbol).step c := rfl

/-- Two steps of the run, as an equation on `runFrom`. -/
lemma runFrom_two (c : Cfg k Symbol RewindState input) :
    (rewindInput k Symbol).runFrom c 2 =
      (rewindInput k Symbol).step ((rewindInput k Symbol).step c) := rfl

/-- From `walk` at position `j ≤ input.length` the machine reaches the halting configuration with
the input head at position `1` in `j + 1` steps. -/
lemma runFrom_walk (j : ℕ) :
    ∀ p : Fin (input.length + 2), p.val = j → j ≤ input.length →
      (rewindInput k Symbol).runFrom ⟨some .walk, p, w, wp, out⟩ (j + 1) =
        ⟨none, 1, w, wp, out⟩ := by
  induction j with
  | zero =>
    intro p hp _
    obtain rfl : p = 0 := Fin.ext (by simpa using hp)
    rw [runFrom, Function.iterate_succ_apply', Function.iterate_zero, id_eq,
      step_walk_none (inputSymbol_mk_eq_none_left rfl)]
    refine cfg_congr ?_
    rw [val_moveInputPos_pos 0 (by simp)]
    simp
  | succ j ih =>
    intro p hp hj
    rw [runFrom, Function.iterate_succ_apply, ← runFrom,
      step_read _ (inputSymbol_mk_eq_some (by omega) (by omega))]
    exact ih (moveInputPos p .neg) (by rw [val_moveInputPos_neg]; omega) (by omega)

end Rewind

/-- **The machine that rewinds the input head.** From any configuration in its initial state it
halts, within `input.length + 3` steps, with the input head at position `1` — the first input
symbol — and with the work tapes, the work-tape head positions and the output unchanged at every
step of the run. Before the halting step the machine is live, so runs chain sequentially. -/
public theorem exists_rewindInput (k : ℕ) (Symbol : Type*) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM k Symbol State),
      ∀ (input : List Symbol) (c : Cfg k Symbol State input), c.state = some tm.q₀ →
        ∃ u ≤ c.inputPos.val + 2,
          (∀ m < u, (tm.runFrom c m).state ≠ none) ∧
          tm.runFrom c u = ⟨none, 1, c.workTapes, c.workTapePos, c.output⟩ ∧
          ∀ m ≤ u, (tm.runFrom c m).workTapes = c.workTapes ∧
            (tm.runFrom c m).workTapePos = c.workTapePos ∧
            (tm.runFrom c m).output = c.output := by
  refine ⟨RewindState, inferInstance, rewindInput k Symbol, fun input c hc => ?_⟩
  obtain ⟨q, p, w, wp, out⟩ := c
  obtain rfl : q = some RewindState.probe := hc
  -- the run halts at position `1` after at most `input.length + 3` steps
  obtain ⟨u₀, hu₀, hrun⟩ : ∃ u₀ ≤ p.val + 2,
      (rewindInput k Symbol).runFrom ⟨some .probe, p, w, wp, out⟩ u₀ =
        ⟨none, 1, w, wp, out⟩ := by
    rcases Nat.eq_zero_or_pos p.val with hp0 | hp1
    · -- started at the left boundary: probe, probe again, halt
      refine ⟨2, by omega, ?_⟩
      obtain rfl : p = 0 := Fin.ext (by simpa using hp0)
      rw [Rewind.runFrom_two, Rewind.step_probe_none (Rewind.inputSymbol_mk_eq_none_left rfl),
        show moveInputPos (0 : Fin (input.length + 2)) .neg = 0 from
          Fin.ext (by rw [Rewind.val_moveInputPos_neg]; simp),
        Rewind.step_probe2_none (Rewind.inputSymbol_mk_eq_none_left rfl)]
      refine Rewind.cfg_congr ?_
      rw [Rewind.val_moveInputPos_pos 0 (by simp)]
      simp
    rcases Nat.lt_or_ge p.val (input.length + 1) with hplt | hpge
    · -- started inside the input: one probe, then walk to the boundary
      refine ⟨p.val + 1, by omega, ?_⟩
      have hw := Rewind.runFrom_walk (k := k) (w := w) (wp := wp) (out := out) (p.val - 1)
        (moveInputPos p .neg) (by rw [Rewind.val_moveInputPos_neg]) (by omega)
      rw [show p.val - 1 + 1 = p.val from by omega] at hw
      rw [runFrom, Function.iterate_succ_apply, ← runFrom,
        Rewind.step_read _ (Rewind.inputSymbol_mk_eq_some (by omega) (by omega))]
      exact hw
    · -- started at the right boundary
      have hpv : p.val = input.length + 1 := by have := p.isLt; omega
      have hs1 := Rewind.inputSymbol_mk_eq_none_right (q := some .probe) (w := w) (wp := wp)
        (out := out) hpv
      rcases Nat.eq_zero_or_pos input.length with hlen | hlen
      · -- empty input: two probes and halt
        refine ⟨2, by omega, ?_⟩
        rw [Rewind.runFrom_two, Rewind.step_probe_none hs1,
          show moveInputPos p .neg = 0 from
            Fin.ext (by rw [Rewind.val_moveInputPos_neg, Fin.val_zero]; omega),
          Rewind.step_probe2_none (Rewind.inputSymbol_mk_eq_none_left rfl)]
        refine Rewind.cfg_congr ?_
        rw [Rewind.val_moveInputPos_pos 0 (by simp)]
        simp
      · -- nonempty input: one probe, the second probe finds a symbol, then walk
        refine ⟨1 + (1 + (input.length - 1 + 1)), by omega, ?_⟩
        have hmv : (moveInputPos p .neg).val = input.length := by
          rw [Rewind.val_moveInputPos_neg]; omega
        rw [runFrom, Nat.add_comm 1 (1 + (input.length - 1 + 1)),
          Function.iterate_add_apply]
        rw [← runFrom, ← runFrom, Rewind.runFrom_one, Rewind.step_probe_none hs1]
        rw [runFrom, Nat.add_comm 1 (input.length - 1 + 1),
          Function.iterate_add_apply]
        rw [← runFrom, ← runFrom, Rewind.runFrom_one,
          Rewind.step_read _ (Rewind.inputSymbol_mk_eq_some (by omega) (by omega))]
        exact Rewind.runFrom_walk (input.length - 1) _
          (by rw [Rewind.val_moveInputPos_neg, hmv]) (by omega)
  -- take the first halting time; the frame holds at every step
  obtain ⟨u, hu, hhalt, hactive⟩ :=
    exists_minimal_halting_time (rewindInput k Symbol) _ u₀ (by rw [hrun])
  have hfin : (rewindInput k Symbol).runFrom ⟨some RewindState.probe, p, w, wp, out⟩ u =
      ⟨none, 1, w, wp, out⟩ := by
    have h := runFrom_eq_of_halt (rewindInput k Symbol) _ hu hhalt
    rw [hrun] at h
    exact h.symm
  exact ⟨u, le_trans hu hu₀, hactive, hfin, fun m _ => Rewind.runFrom_frame _ m⟩

end Turing.MultiTapeTM
