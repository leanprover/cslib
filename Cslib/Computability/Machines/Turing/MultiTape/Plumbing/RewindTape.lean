/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.SingleTapeAction
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# A machine that rewinds a work-tape head

A two-state machine that returns the head of one designated work tape `i` to the start of the word
it is in, and halts there. It never moves the input head, never moves any other work head, never
writes to any other tape and never outputs, so it can be run between two phases of a computation
to re-normalise a work-tape head without disturbing anything else.

In its initial state `start` the machine takes one unconditional step left, into state `scan`. In
state `scan` it walks left over symbols, writing `write` to every cell it leaves; on the first
blank it moves the head right and halts. By default `write` is `none` and the machine writes
nothing; with `write := some none` it erases the part of the word it walks over.

Suppose tape `i` holds a word `w` in cells `0, …, w.length - 1` and is blank everywhere else. If the
head starts at any cell `p ≤ w.length`, i.e. anywhere inside the word or at the frontier just past
it, the run halts after `p + 2` steps with the head on `0`. The unconditional first step makes this
work for `p = 0` too. The designated head visits exactly the cells `-1, …, p`, and `write` has been
applied to the cells `0, …, p - 1`; every other tape and every other head remain unchanged.

## Main results

* `Turing.MultiTapeTM.rewindTape`: the machine that rewinds a work-tape head to the start of its
  word.
* `Turing.MultiTapeTM.runFrom_rewindTape`: its run from the initial state, with the special cases
  `Turing.MultiTapeTM.runFrom_rewindTape_none` (nothing is written) and
  `Turing.MultiTapeTM.runFrom_rewindTape_erase` (the whole word is erased).
* `Turing.MultiTapeTM.workTapePos_runFrom_rewindTape`: the rewound head stays within `[-1, p]`.
* `Turing.MultiTapeTM.runFrom_rewindTape_frame`: no run changes the input head, the output, any
  other tape or any other work head.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*} {input : List Symbol}

/-- The control states of the work-tape-rewinding machine: `start` takes one unconditional step
left, `scan` walks left towards the start of the word. -/
public inductive RewindTapeState : Type
  | start
  | scan
  deriving DecidableEq

public instance : Fintype RewindTapeState := ⟨{.start, .scan}, fun q => by cases q <;> simp⟩

/-- The work-tape-rewinding machine for tape `i`. In state `start` it moves the head of tape `i`
left, unconditionally, and enters state `scan`. In state `scan` it writes `write` over a symbol
and moves left, staying in `scan`; on the first blank it moves right and halts. No other tape is
ever written, the input head never moves, no other work head moves and nothing is output. -/
public def rewindTape (Symbol : Type*) (i : Fin k) (write : Option (Option Symbol) := none) :
    MultiTapeTM k Symbol RewindTapeState where
  q₀ := .start
  tr q _ work :=
    match q, work i with
    | .start, _ => .onTape i none (-1) (some .scan)
    | .scan, some _ => .onTape i write (-1) (some .scan)
    | .scan, none => .onTape i none 1 none

namespace RewindTape

variable {i : Fin k} {write : Option (Option Symbol)} {ip : Fin (input.length + 2)}
  {tapes : Fin k → ℤ → Option Symbol} {heads : Fin k → ℤ} {out : List Symbol} {p : ℤ}

/-- Every action of the machine only touches tape `i`. -/
lemma tr_eq (q : RewindTapeState) (inp : Option Symbol) (work : Fin k → Option Symbol) :
    ∃ write' m state, (rewindTape Symbol i write).tr q inp work = .onTape i write' m state := by
  dsimp only [rewindTape]
  split
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩

/-- Moving the head of tape `i` left in state `start`, unconditionally, entering `scan`. -/
lemma step_start :
    (rewindTape Symbol i write).step ⟨some .start, ip, tapes, Function.update heads i p, out⟩ =
      ⟨some .scan, ip, tapes, Function.update heads i (p - 1), out⟩ := by
  rw [step_apply_of_state rfl]
  simp [rewindTape, sub_eq_add_neg]

/-- Walking left in state `scan`: over a symbol the machine writes `write` and the head moves left,
staying in `scan`. -/
lemma step_scan_some {s : Symbol} (hs : tapes i p = some s) :
    (rewindTape Symbol i write).step ⟨some .scan, ip, tapes, Function.update heads i p, out⟩ =
      ⟨some .scan, ip, Function.update tapes i (write.elim (tapes i) (Function.update (tapes i) p)),
        Function.update heads i (p - 1), out⟩ := by
  rw [step_apply_of_state rfl]
  simp [rewindTape, Cfg.workTapeSymbols, hs, Action.apply_onTape, sub_eq_add_neg]

/-- Halting in state `scan`: on the first blank — the cell at position `-1` — the head moves right
and the machine halts. -/
lemma step_scan_none (hs : tapes i p = none) :
    (rewindTape Symbol i write).step ⟨some .scan, ip, tapes, Function.update heads i p, out⟩ =
      ⟨none, ip, tapes, Function.update heads i (p + 1), out⟩ := by
  rw [step_apply_of_state rfl]
  simp [rewindTape, Cfg.workTapeSymbols, hs]

/-- The scanning phase: from `scan` at cell `l - 1` of the word, after `n ≤ l` steps the head has
walked left `n` cells, writing `write` to the cells it left. -/
lemma runFrom_scan {w : List Symbol} (hw : tapes i = tapeOfList w) {l : ℕ} (hl : l ≤ w.length)
    (n : ℕ) (hn : n ≤ l) :
    (rewindTape Symbol i write).runFrom
        ⟨some .scan, ip, tapes, Function.update heads i ((l : ℤ) - 1), out⟩ n =
      ⟨some .scan, ip,
        Function.update tapes i
          (fun z => if (l : ℤ) - n ≤ z ∧ z < l then write.getD (tapes i z) else tapes i z),
        Function.update heads i ((l : ℤ) - 1 - n), out⟩ := by
  induction n with
  | zero => simp [runFrom, show ∀ z : ℤ, ¬((l : ℤ) ≤ z ∧ z < l) by omega]
  | succ n ih =>
    have hpos : (l : ℤ) - 1 - n = ((l - 1 - n : ℕ) : ℤ) := by omega
    have hsym : Function.update tapes i
        (fun z => if (l : ℤ) - n ≤ z ∧ z < l then write.getD (tapes i z) else tapes i z) i
        ((l : ℤ) - 1 - n) = some (w[l - 1 - n]'(by omega)) := by
      rw [Function.update_self]
      split_ifs
      · omega
      rw [hw, hpos, tapeOfList_ofNat]
      exact List.getElem?_eq_getElem (by omega)
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega), step_scan_some hsym,
      Function.update_idem, Function.update_self]
    congr 2
    · cases write with
      | none => simp
      | some c =>
        funext z
        simp only [Option.elim_some, Function.update_apply, Option.getD_some]
        split_ifs <;> first | rfl | omega
    · omega

end RewindTape

open RewindTape in
/-- **The run of the machine that rewinds a work-tape head.** Started with tape `i` holding a word
`w` and the head at a position `p ≤ w.length` — inside the word or at the frontier just past it —
after `p + 2` steps the machine has halted with the head back at position `0`, `write` applied to
the cells `0, …, p - 1` and nothing else changed. -/
public theorem runFrom_rewindTape {i : Fin k} (write : Option (Option Symbol))
    (ip : Fin (input.length + 2)) (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (out : List Symbol) {w : List Symbol} (hw : tapes i = tapeOfList w) {p : ℕ}
    (hp : p ≤ w.length) :
    (rewindTape Symbol i write).runFrom
        ⟨some (rewindTape Symbol i write).q₀, ip, tapes, Function.update heads i p, out⟩ (p + 2) =
      ⟨none, ip,
        Function.update tapes i
          (fun z => if 0 ≤ z ∧ z < p then write.getD (tapes i z) else tapes i z),
        Function.update heads i 0, out⟩ := by
  rw [show (rewindTape Symbol i write).q₀ = .start from rfl, runFrom, Function.iterate_succ_apply,
    step_start, Function.iterate_succ_apply', ← runFrom, runFrom_scan hw hp p le_rfl,
    show (p : ℤ) - 1 - p = -1 by omega,
    step_scan_none (by simp [hw]; rfl)]
  simp

/-- **Rewinding without writing** changes nothing but the position of the head. -/
public theorem runFrom_rewindTape_none {i : Fin k} (ip : Fin (input.length + 2))
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ) (out : List Symbol) {w : List Symbol}
    (hw : tapes i = tapeOfList w) {p : ℕ} (hp : p ≤ w.length) :
    (rewindTape Symbol i).runFrom
        ⟨some (rewindTape Symbol i).q₀, ip, tapes, Function.update heads i p, out⟩ (p + 2) =
      ⟨none, ip, tapes, Function.update heads i 0, out⟩ := by
  simpa using runFrom_rewindTape none ip tapes heads out hw hp

/-- **Rewinding while erasing** from the frontier of the word leaves tape `i` blank. -/
public theorem runFrom_rewindTape_erase {i : Fin k} (ip : Fin (input.length + 2))
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ) (out : List Symbol) {w : List Symbol}
    (hw : tapes i = tapeOfList w) :
    (rewindTape Symbol i (some none)).runFrom
        ⟨some (rewindTape Symbol i (some none)).q₀, ip, tapes, Function.update heads i w.length,
          out⟩ (w.length + 2) =
      ⟨none, ip, Function.update tapes i fun _ => none, Function.update heads i 0, out⟩ := by
  rw [runFrom_rewindTape _ ip tapes heads out hw le_rfl]
  congr 2
  funext z
  split_ifs with h
  · rfl
  · rw [hw]
    rcases z with z | z
    · simp only [Int.ofNat_eq_natCast] at h
      exact List.getElem?_eq_none (by omega)
    · rfl

open RewindTape in
/-- At every step, the head of tape `i` is within `[-1, p]`: it walks from its start `p ≤ w.length`
down to `-1` and back to `0`, where it stays. -/
public theorem workTapePos_runFrom_rewindTape {i : Fin k} (write : Option (Option Symbol))
    (ip : Fin (input.length + 2)) (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (out : List Symbol) {w : List Symbol} (hw : tapes i = tapeOfList w) {p : ℕ}
    (hp : p ≤ w.length) (m : ℕ) :
    ((rewindTape Symbol i write).runFrom
        ⟨some (rewindTape Symbol i write).q₀, ip, tapes, Function.update heads i p, out⟩
        m).workTapePos i ∈ Set.Icc (-1) (p : ℤ) := by
  rcases m with _ | m
  · simp [runFrom]
  rcases Nat.lt_or_ge m (p + 1) with hlt | hge
  · -- After the initial left move, take `m` scanning steps.
    rw [show (rewindTape Symbol i write).q₀ = .start from rfl, runFrom,
      Function.iterate_succ_apply, step_start, ← runFrom, runFrom_scan hw hp m (by omega)]
    simp only [Function.update_self, Set.mem_Icc]
    constructor <;> omega
  · have hrun := runFrom_rewindTape write ip tapes heads out hw hp
    rw [runFrom_eq_of_halt _ _ (by omega : p + 2 ≤ m + 1) (by rw [hrun]), hrun]
    simp

/-- No run of the machine changes the input head, the output, any tape other than `i` or any work
head other than the head of tape `i`. -/
public theorem runFrom_rewindTape_frame {i : Fin k} (write : Option (Option Symbol))
    (c : Cfg k Symbol RewindTapeState input) (m : ℕ) :
    ((rewindTape Symbol i write).runFrom c m).inputPos = c.inputPos ∧
      (∀ j ≠ i, ((rewindTape Symbol i write).runFrom c m).workTapes j = c.workTapes j ∧
        ((rewindTape Symbol i write).runFrom c m).workTapePos j = c.workTapePos j) ∧
      ((rewindTape Symbol i write).runFrom c m).output = c.output :=
  runFrom_frame_of_onTape RewindTape.tr_eq c m

end Turing.MultiTapeTM
