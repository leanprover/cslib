/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Machines that emit a work tape to the output and set a single cell

Two small machines used by combinators to assemble the write-only output tape and to place or
remove markers on a work tape.

`emitTape i` reads the word held on work tape `i` from its start and appends it, symbol by symbol,
to the real output tape, moving the tape-`i` head right over the word and halting on the first
blank. It never writes to any work tape, never moves the input head and never moves any other work
head: the only lasting effect is the appended output and the tape-`i` head resting at the frontier
`w.length`.

`setCell i v` writes a designated symbol value `v` into cell `-1` of work tape `i` — the cell just
left of the word — and returns the head to `0`, touching nothing else. It is the primitive used to
place or clear a flag mark. The machine is specialised to the cell `-1`, the only cell the callers
need; a general version for an arbitrary cell `z` would require a head able to reach `z`, i.e. a
state count depending on `z`.

## Main results

* `Turing.MultiTapeTM.exists_emitTape`: the machine appending a work tape's word to the output.
* `Turing.MultiTapeTM.exists_setCell`: the machine setting cell `-1` of a work tape to a value.
-/

namespace Turing.MultiTapeTM

variable {K : ℕ} {Symbol : Type*} {input : List Symbol}

/-! ## Emitting a work tape to the output -/

/-- The tape-emitting machine for tape `i`. It has a single live state. Reading a symbol `s` on
tape `i` it appends `s` to the output, moves the tape-`i` head right and stays live; reading the
first blank it halts, writing nothing and moving nothing. No work tape is ever written, the input
head never moves and no other work head moves. -/
def emitTape (i : Fin K) : MultiTapeTM K Symbol Unit where
  q₀ := ()
  tr _ _ work :=
    match work i with
    | some s =>
        { inputTape := 0, workTapes := fun l => (none, if l = i then 1 else 0),
          output := some s, state := some () }
    | none =>
        { inputTape := 0, workTapes := fun _ => (none, 0),
          output := none, state := none }

namespace EmitTape

variable {i : Fin K} {ip : Fin (input.length + 2)} {W : Fin K → ℤ → Option Symbol}
  {WP : Fin K → ℤ} {out : List Symbol} {p : ℤ}

/-- A configuration of the emitting machine: state `q`, the head of tape `i` at `p`, tape contents
`W`, the other heads `WP`, the input head `ip` and output `out`. -/
def cfg (input : List Symbol) (i : Fin K) (q : Option Unit)
    (ip : Fin (input.length + 2)) (W : Fin K → ℤ → Option Symbol) (WP : Fin K → ℤ)
    (out : List Symbol) (p : ℤ) : Cfg K Symbol Unit input :=
  ⟨q, ip, W, Function.update WP i p, out⟩

/-- Configurations of the shape `cfg` are equal as soon as their outputs and tape-`i` head
positions agree. -/
lemma cfg_congr {q : Option Unit} {out out' : List Symbol} {p p' : ℤ}
    (hout : out = out') (hp : p = p') :
    cfg input i q ip W WP out p = cfg input i q ip W WP out' p' := by
  rw [hout, hp]

/-- Emitting one symbol: reading `s` on tape `i` appends `s` to the output and moves the head
right, staying live. -/
lemma step_emit_some {s : Symbol} (hs : W i p = some s) :
    (emitTape i).step (cfg input i (some ()) ip W WP out p) =
      cfg input i (some ()) ip W WP (out ++ [s]) (p + 1) := by
  have hsym : (cfg input i (some ()) ip W WP out p).workTapeSymbols i = some s := by
    simp [cfg, Cfg.workTapeSymbols, hs]
  unfold step
  simp only [cfg] at hsym ⊢
  simp only [emitTape]
  rw [hsym]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp
  · funext l
    rcases eq_or_ne l i with rfl | h
    · simp
    · simp
  · funext l
    rcases eq_or_ne l i with rfl | h
    · simp
    · simp [h]
  · simp

/-- Halting: reading the first blank on tape `i` the machine halts, writing and moving nothing. -/
lemma step_emit_none (hs : W i p = none) :
    (emitTape i).step (cfg input i (some ()) ip W WP out p) =
      cfg input i none ip W WP out p := by
  have hsym : (cfg input i (some ()) ip W WP out p).workTapeSymbols i = none := by
    simp [cfg, Cfg.workTapeSymbols, hs]
  unfold step
  simp only [cfg] at hsym ⊢
  simp only [emitTape]
  rw [hsym]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp
  · funext l
    rcases eq_or_ne l i with rfl | h
    · simp
    · simp
  · funext l
    rcases eq_or_ne l i with rfl | h
    · simp
    · simp [h]
  · simp

/-- The scanning phase: from the start of the word, after `n ≤ w.length` steps the head is at
position `n` and the first `n` symbols of `w` have been appended to the output. -/
lemma runFrom_scan {w : List Symbol} (hw : W i = tapeOfList w) (n : ℕ) (hn : n ≤ w.length) :
    (emitTape i).runFrom (cfg input i (some ()) ip W WP out 0) n =
      cfg input i (some ()) ip W WP (out ++ w.take n) (n : ℤ) := by
  induction n with
  | zero =>
    simp only [runFrom, Function.iterate_zero, id_eq]
    exact cfg_congr (by simp) (by simp)
  | succ n ih =>
    have hsym : W i (n : ℤ) = some (w[n]'(by omega)) := by
      rw [hw, tapeOfList_ofNat]
      exact List.getElem?_eq_getElem (by omega)
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega), step_emit_some hsym]
    refine cfg_congr ?_ (by push_cast; omega)
    rw [List.append_assoc, List.take_concat_get' w n (by omega)]

/-- The complete run: from the start of the word, after `w.length + 1` steps the machine has
halted with the full word `w` appended to the output and the head at the frontier `w.length`. -/
lemma runFrom_full {w : List Symbol} (hw : W i = tapeOfList w) :
    (emitTape i).runFrom (cfg input i (some ()) ip W WP out 0) (w.length + 1) =
      cfg input i none ip W WP (out ++ w) (w.length : ℤ) := by
  have hnone : W i (w.length : ℤ) = none := by
    rw [hw, tapeOfList_ofNat]
    exact List.getElem?_eq_none (by omega)
  rw [runFrom, Function.iterate_succ_apply', ← runFrom,
    runFrom_scan hw w.length le_rfl, step_emit_none hnone]
  exact cfg_congr (by rw [List.take_length]) rfl

/-- Throughout the run the head of tape `i` stays within `[0, w.length]`: it walks right from the
start of the word to the frontier and stops. -/
lemma runFrom_pos_range {w : List Symbol} (hw : W i = tapeOfList w) (m : ℕ)
    (hm : m ≤ w.length + 1) :
    (0 : ℤ) ≤ ((emitTape i).runFrom (cfg input i (some ()) ip W WP out 0) m).workTapePos i ∧
      ((emitTape i).runFrom (cfg input i (some ()) ip W WP out 0) m).workTapePos i ≤
        (w.length : ℤ) := by
  rcases Nat.lt_or_ge m (w.length + 1) with hlt | hge
  · have hml : m ≤ w.length := by omega
    rw [runFrom_scan hw m hml]
    constructor <;> simp only [cfg, Function.update_self] <;> omega
  · obtain rfl : m = w.length + 1 := by omega
    rw [runFrom_full hw]
    constructor <;> simp only [cfg, Function.update_self] <;> omega

/-- No action of the machine writes to a work tape. -/
lemma tr_write_none (q : Unit) (inp : Option Symbol) (work : Fin K → Option Symbol) (l : Fin K) :
    (((emitTape i).tr q inp work).workTapes l).1 = none := by
  simp only [emitTape]
  cases work i <;> rfl

/-- No action of the machine moves the input head. -/
lemma tr_inputTape (q : Unit) (inp : Option Symbol) (work : Fin K → Option Symbol) :
    ((emitTape i).tr q inp work).inputTape = 0 := by
  simp only [emitTape]
  cases work i <;> rfl

/-- No action of the machine moves a work head other than the head of tape `i`. -/
lemma tr_move_ne (q : Unit) (inp : Option Symbol) (work : Fin K → Option Symbol)
    {l : Fin K} (h : l ≠ i) : (((emitTape i).tr q inp work).workTapes l).2 = 0 := by
  simp only [emitTape]
  cases work i <;> simp [h]

/-- One step preserves the input head, every tape's contents and every work head other than the
head of tape `i`. (The output does change.) -/
lemma step_frame (c : Cfg K Symbol Unit input) :
    ((emitTape i).step c).inputPos = c.inputPos ∧
      (∀ j, ((emitTape i).step c).workTapes j = c.workTapes j) ∧
      (∀ j, j ≠ i → ((emitTape i).step c).workTapePos j = c.workTapePos j) := by
  cases hc : c.state with
  | none => rw [step_of_halt hc]; exact ⟨rfl, fun _ => rfl, fun _ _ => rfl⟩
  | some q =>
    refine ⟨?_, ?_, ?_⟩
    · rw [step_inputPos_of_state hc, tr_inputTape, moveInputPos_zero]
    · intro j
      rw [step_workTapes_of_state hc, tr_write_none q c.inputSymbol c.workTapeSymbols j]
    · intro j hj
      rw [step_workTapePos_of_state hc, tr_move_ne q c.inputSymbol c.workTapeSymbols hj]
      simp

/-- The whole run preserves the input head, every tape's contents and every work head other than
the head of tape `i`. -/
lemma runFrom_frame (c : Cfg K Symbol Unit input) (m : ℕ) :
    ((emitTape i).runFrom c m).inputPos = c.inputPos ∧
      (∀ j, ((emitTape i).runFrom c m).workTapes j = c.workTapes j) ∧
      (∀ j, j ≠ i → ((emitTape i).runFrom c m).workTapePos j = c.workTapePos j) := by
  induction m with
  | zero => exact ⟨rfl, fun _ => rfl, fun _ _ => rfl⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := step_frame ((emitTape i).runFrom c m)
    rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    exact ⟨h1.trans ih.1, fun j => (h2 j).trans (ih.2.1 j),
      fun j hj => (h3 j hj).trans (ih.2.2 j hj)⟩

end EmitTape

open EmitTape in
/-- **The machine that appends a work tape's word to the output.** One machine per tape index `i`:
started with tape `i` holding a word `w` in cells `0, …, w.length - 1` and the head at position
`0`, it halts within `w.length + 2` steps having appended `w` to the output, with the tape-`i`
head resting at the frontier `w.length` and every other field — input head, all tape contents and
all other work heads — unchanged at every step of the run. Before the halting step the machine is
live, so runs chain sequentially. -/
public theorem exists_emitTape {Symbol : Type*} {K : ℕ} (i : Fin K) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM K Symbol State),
      ∀ (input : List Symbol) (c : Cfg K Symbol State input) (w : List Symbol),
        c.state = some tm.q₀ →
        c.workTapes i = tapeOfList w →
        c.workTapePos i = 0 →
        ∃ u ≤ w.length + 2,
          (∀ m < u, (tm.runFrom c m).state ≠ none) ∧
          tm.runFrom c u = ⟨none, c.inputPos, c.workTapes,
            Function.update c.workTapePos i (w.length : ℤ), c.output ++ w⟩ ∧
          ∀ m ≤ u, (tm.runFrom c m).inputPos = c.inputPos ∧
            (∀ j, (tm.runFrom c m).workTapes j = c.workTapes j) ∧
            (∀ j, j ≠ i → (tm.runFrom c m).workTapePos j = c.workTapePos j) ∧
            (0 : ℤ) ≤ (tm.runFrom c m).workTapePos i ∧
            (tm.runFrom c m).workTapePos i ≤ (w.length : ℤ) := by
  refine ⟨Unit, inferInstance, emitTape i, fun input c w hstate hwi hwp => ?_⟩
  obtain ⟨q, ip, W, WP, out⟩ := c
  obtain rfl : q = some () := hstate
  have hwi' : W i = tapeOfList w := hwi
  have hwp' : WP i = 0 := hwp
  have hc0 : (⟨some (), ip, W, WP, out⟩ : Cfg K Symbol Unit input) =
      cfg input i (some ()) ip W WP out 0 := by
    refine Cfg.ext rfl rfl rfl ?_ rfl
    change WP = Function.update WP i 0
    rw [← hwp', Function.update_eq_self]
  obtain ⟨u, hu, hactive, hhalt⟩ : ∃ u ≤ w.length + 1,
      (∀ m < u, ((emitTape i).runFrom
        (⟨some (), ip, W, WP, out⟩ : Cfg K Symbol Unit input) m).state ≠ none) ∧
      (emitTape i).runFrom (⟨some (), ip, W, WP, out⟩ : Cfg K Symbol Unit input) u =
        ⟨none, ip, W, Function.update WP i (w.length : ℤ), out ++ w⟩ := by
    have hrun : (emitTape i).runFrom
        (⟨some (), ip, W, WP, out⟩ : Cfg K Symbol Unit input) (w.length + 1) =
        ⟨none, ip, W, Function.update WP i (w.length : ℤ), out ++ w⟩ := by
      rw [hc0, runFrom_full hwi']
      simp only [cfg]
    obtain ⟨u, hu, hhaltu, hact⟩ :=
      exists_minimal_halting_time (emitTape i) _ (w.length + 1) (by rw [hrun])
    have heq := runFrom_eq_of_halt (emitTape i) _ hu hhaltu
    rw [hrun] at heq
    exact ⟨u, hu, hact, heq.symm⟩
  refine ⟨u, by omega, hactive, hhalt, fun m hm => ?_⟩
  obtain ⟨f1, f2, f3⟩ := runFrom_frame (⟨some (), ip, W, WP, out⟩) m
  obtain ⟨g1, g2⟩ := runFrom_pos_range (input := input) (i := i) (ip := ip) (W := W) (WP := WP)
    (out := out) hwi' m (by omega)
  rw [← hc0] at g1 g2
  exact ⟨f1, f2, f3, g1, g2⟩

/-! ## Setting a single work-tape cell -/

/-- The control states of the cell-setting machine: `go` walks the head one cell left to cell
`-1`, `write` writes the value there and returns the head to `0`. -/
inductive SetCellState : Type
  | go
  | write

instance : Finite SetCellState :=
  Finite.of_injective
    (fun q => match q with
      | .go => (0 : Fin 2)
      | .write => 1)
    (fun a b h => by cases a <;> cases b <;> first | rfl | exact absurd h (by decide))

/-- The cell-setting machine for tape `i` and value `v`. In state `go` it moves the head of tape
`i` one cell left, into state `write`. In state `write` it writes `v` at the current cell, moves
the head right and halts. No other tape is ever written, the input head never moves, no other work
head moves and nothing is output. -/
def setCell (i : Fin K) (v : Option Symbol) : MultiTapeTM K Symbol SetCellState where
  q₀ := .go
  tr q _ _ :=
    match q with
    | .go =>
        { inputTape := 0, workTapes := fun l => (none, if l = i then -1 else 0),
          output := none, state := some .write }
    | .write =>
        { inputTape := 0,
          workTapes := fun l => (if l = i then some v else none, if l = i then 1 else 0),
          output := none, state := none }

namespace SetCell

variable {i : Fin K} {v : Option Symbol} {ip : Fin (input.length + 2)}
  {W : Fin K → ℤ → Option Symbol} {WP : Fin K → ℤ} {out : List Symbol} {p : ℤ}

/-- A configuration of the cell-setting machine: state `q`, tape contents `W`, the head of tape
`i` at `p`, the other heads `WP`, the input head `ip` and output `out`. -/
def cfg (input : List Symbol) (i : Fin K) (q : Option SetCellState)
    (ip : Fin (input.length + 2)) (W : Fin K → ℤ → Option Symbol) (WP : Fin K → ℤ)
    (out : List Symbol) (p : ℤ) : Cfg K Symbol SetCellState input :=
  ⟨q, ip, W, Function.update WP i p, out⟩

/-- Configurations of the shape `cfg` are equal as soon as their tape contents and tape-`i` head
positions agree. -/
lemma cfg_congr {q : Option SetCellState} {W W' : Fin K → ℤ → Option Symbol} {p p' : ℤ}
    (hW : W = W') (hp : p = p') :
    cfg input i q ip W WP out p = cfg input i q ip W' WP out p' := by
  rw [hW, hp]

/-- Moving the head of tape `i` left in state `go`, unconditionally, entering `write`. -/
lemma step_go :
    (setCell i v).step (cfg input i (some .go) ip W WP out p) =
      cfg input i (some .write) ip W WP out (p - 1) := by
  unfold step
  simp only [cfg]
  simp only [setCell]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp
  · funext l
    rcases eq_or_ne l i with rfl | h
    · simp
    · simp
  · funext l
    rcases eq_or_ne l i with rfl | h
    · simp [sub_eq_add_neg]
    · simp [h]
  · simp

/-- Writing `v` at the current cell in state `write`, moving the head right and halting. -/
lemma step_write :
    (setCell i v).step (cfg input i (some .write) ip W WP out p) =
      cfg input i none ip (Function.update W i (Function.update (W i) p v)) WP out (p + 1) := by
  unfold step
  simp only [cfg]
  simp only [setCell]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp
  · funext l
    rcases eq_or_ne l i with rfl | h
    · simp
    · simp [h]
  · funext l
    rcases eq_or_ne l i with rfl | h
    · simp
    · simp [h]
  · simp

/-- After one step the machine is in state `write` with the head at cell `-1`. -/
lemma runFrom_one :
    (setCell i v).runFrom (cfg input i (some .go) ip W WP out 0) 1 =
      cfg input i (some .write) ip W WP out (-1) := by
  rw [runFrom, Function.iterate_succ_apply', Function.iterate_zero, id_eq, step_go]
  exact cfg_congr rfl (by omega)

/-- The complete run: after two steps the machine has written `v` at cell `-1` of tape `i` and
returned the head to `0`. -/
lemma runFrom_two :
    (setCell i v).runFrom (cfg input i (some .go) ip W WP out 0) 2 =
      cfg input i none ip (Function.update W i (Function.update (W i) (-1) v)) WP out 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, runFrom, Function.iterate_succ_apply',
    ← runFrom, runFrom_one, step_write]
  exact cfg_congr rfl (by omega)

/-- Throughout the run the head of tape `i` stays within `[-1, 0]`. -/
lemma runFrom_pos_range (m : ℕ) (hm : m ≤ 2) :
    (-1 : ℤ) ≤ ((setCell i v).runFrom (cfg input i (some .go) ip W WP out 0) m).workTapePos i ∧
      ((setCell i v).runFrom (cfg input i (some .go) ip W WP out 0) m).workTapePos i ≤ 0 := by
  rcases m with _ | _ | _ | m
  · simp only [runFrom, Function.iterate_zero, id_eq]
    constructor <;> simp only [cfg, Function.update_self] <;> omega
  · rw [runFrom_one]
    constructor <;> simp only [cfg, Function.update_self] <;> omega
  · rw [runFrom_two]
    constructor <;> simp only [cfg, Function.update_self] <;> omega
  · exact absurd hm (by omega)

/-- No action of the machine moves the input head. -/
lemma tr_inputTape (q : SetCellState) (inp : Option Symbol) (work : Fin K → Option Symbol) :
    ((setCell i v).tr q inp work).inputTape = 0 := by
  simp only [setCell]
  cases q <;> rfl

/-- No action of the machine outputs. -/
lemma tr_output (q : SetCellState) (inp : Option Symbol) (work : Fin K → Option Symbol) :
    ((setCell i v).tr q inp work).output = none := by
  simp only [setCell]
  cases q <;> rfl

/-- No action of the machine writes to a work tape other than tape `i`. -/
lemma tr_write_ne (q : SetCellState) (inp : Option Symbol) (work : Fin K → Option Symbol)
    {l : Fin K} (h : l ≠ i) : (((setCell i v).tr q inp work).workTapes l).1 = none := by
  simp only [setCell]
  cases q <;> simp [h]

/-- No action of the machine moves a work head other than the head of tape `i`. -/
lemma tr_move_ne (q : SetCellState) (inp : Option Symbol) (work : Fin K → Option Symbol)
    {l : Fin K} (h : l ≠ i) : (((setCell i v).tr q inp work).workTapes l).2 = 0 := by
  simp only [setCell]
  cases q <;> simp [h]

/-- One step preserves the input head, the output, and every tape's contents and work head other
than those of tape `i`. -/
lemma step_frame (c : Cfg K Symbol SetCellState input) :
    ((setCell i v).step c).inputPos = c.inputPos ∧
      ((setCell i v).step c).output = c.output ∧
      (∀ j, j ≠ i → ((setCell i v).step c).workTapes j = c.workTapes j ∧
        ((setCell i v).step c).workTapePos j = c.workTapePos j) := by
  cases hc : c.state with
  | none => rw [step_of_halt hc]; exact ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  | some q =>
    refine ⟨?_, ?_, ?_⟩
    · rw [step_inputPos_of_state hc, tr_inputTape, moveInputPos_zero]
    · rw [step_apply_of_state hc, Action.apply_output, tr_output]; simp
    · intro j hj
      refine ⟨?_, ?_⟩
      · rw [step_workTapes_of_state hc, tr_write_ne q c.inputSymbol c.workTapeSymbols hj]
      · rw [step_workTapePos_of_state hc, tr_move_ne q c.inputSymbol c.workTapeSymbols hj]; simp

/-- The whole run preserves the input head, the output, and every tape's contents and work head
other than those of tape `i`. -/
lemma runFrom_frame (c : Cfg K Symbol SetCellState input) (m : ℕ) :
    ((setCell i v).runFrom c m).inputPos = c.inputPos ∧
      ((setCell i v).runFrom c m).output = c.output ∧
      (∀ j, j ≠ i → ((setCell i v).runFrom c m).workTapes j = c.workTapes j ∧
        ((setCell i v).runFrom c m).workTapePos j = c.workTapePos j) := by
  induction m with
  | zero => exact ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := step_frame ((setCell i v).runFrom c m)
    rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    exact ⟨h1.trans ih.1, h2.trans ih.2.1,
      fun j hj => ⟨(h3 j hj).1.trans (ih.2.2 j hj).1, (h3 j hj).2.trans (ih.2.2 j hj).2⟩⟩

end SetCell

open SetCell in
/-- **The machine that sets cell `-1` of a work tape.** One machine per tape index `i` and value
`v`: started with the head of tape `i` at position `0`, it halts within `4` steps having written
`v` into cell `-1` of tape `i` and returned the head to `0`, with every other field — input head,
output, all other tape contents and all other work heads — unchanged at every step of the run.
Before the halting step the machine is live, so runs chain sequentially.

This is the specialisation to the cell `z = -1` of a general "set cell `z`" primitive: it is the
only cell the callers (which mark and clear the flag cell just left of a word) need, and the
excursion is confined to `[-1, 0]`. -/
public theorem exists_setCell {Symbol : Type*} {K : ℕ} (i : Fin K) (v : Option Symbol) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM K Symbol State),
      ∀ (input : List Symbol) (c : Cfg K Symbol State input),
        c.state = some tm.q₀ → c.workTapePos i = 0 →
        ∃ u ≤ 4,
          (∀ m < u, (tm.runFrom c m).state ≠ none) ∧
          tm.runFrom c u = ⟨none, c.inputPos,
            Function.update c.workTapes i (Function.update (c.workTapes i) (-1) v),
            c.workTapePos, c.output⟩ ∧
          ∀ m ≤ u, (tm.runFrom c m).inputPos = c.inputPos ∧ (tm.runFrom c m).output = c.output ∧
            (∀ j, j ≠ i → (tm.runFrom c m).workTapes j = c.workTapes j ∧
              (tm.runFrom c m).workTapePos j = c.workTapePos j) ∧
            (-1 : ℤ) ≤ (tm.runFrom c m).workTapePos i ∧ (tm.runFrom c m).workTapePos i ≤ 0 := by
  refine ⟨SetCellState, inferInstance, setCell i v, fun input c hstate hwp => ?_⟩
  obtain ⟨q, ip, W, WP, out⟩ := c
  obtain rfl : q = some SetCellState.go := hstate
  have hwp' : WP i = 0 := hwp
  have hupdWP : Function.update WP i 0 = WP := by rw [← hwp', Function.update_eq_self]
  have hc0 : (⟨some SetCellState.go, ip, W, WP, out⟩ : Cfg K Symbol SetCellState input) =
      cfg input i (some .go) ip W WP out 0 := by
    refine Cfg.ext rfl rfl rfl ?_ rfl
    exact hupdWP.symm
  obtain ⟨u, hu, hactive, hhalt⟩ : ∃ u ≤ 2,
      (∀ m < u, ((setCell i v).runFrom
        (⟨some SetCellState.go, ip, W, WP, out⟩ : Cfg K Symbol SetCellState input)
        m).state ≠ none) ∧
      (setCell i v).runFrom
          (⟨some SetCellState.go, ip, W, WP, out⟩ : Cfg K Symbol SetCellState input) u =
        ⟨none, ip, Function.update W i (Function.update (W i) (-1) v), WP, out⟩ := by
    have hrun : (setCell i v).runFrom
        (⟨some SetCellState.go, ip, W, WP, out⟩ : Cfg K Symbol SetCellState input) 2 =
        ⟨none, ip, Function.update W i (Function.update (W i) (-1) v), WP, out⟩ := by
      rw [hc0, runFrom_two]
      unfold cfg
      rw [hupdWP]
    obtain ⟨u, hu, hhaltu, hact⟩ :=
      exists_minimal_halting_time (setCell i v) _ 2 (by rw [hrun])
    have heq := runFrom_eq_of_halt (setCell i v) _ hu hhaltu
    rw [hrun] at heq
    exact ⟨u, hu, hact, heq.symm⟩
  refine ⟨u, by omega, hactive, hhalt, fun m hm => ?_⟩
  obtain ⟨f1, f2, f3⟩ := runFrom_frame (⟨some SetCellState.go, ip, W, WP, out⟩) m
  obtain ⟨g1, g2⟩ := runFrom_pos_range (input := input) (i := i) (v := v) (ip := ip) (W := W)
    (WP := WP) (out := out) m (by omega)
  rw [← hc0] at g1 g2
  exact ⟨f1, f2, f3, g1, g2⟩

end Turing.MultiTapeTM
