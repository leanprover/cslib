/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.SingleTapeAction
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# A machine that rewinds a work-tape head

A machine that moves the head of one designated work tape `i` to the left end of its contents and
halts. It optionally writes a certain symbol to or clears the cells it moves over while traveling to
the left. The input tape or other work tapes are not modified.
This machine can be run between two phases of a computation to re-normalise a work-tape head without
disturbing anything else.

In its initial state `start` the machine takes one unconditional step left, into state `scan`. In
state `scan` it walks left over symbols, writing `write` to every cell it leaves; on the first
blank it moves the head right and halts. By default `write` is `none` and the machine writes
nothing; with `write := some none` it erases the part of the word it walks over.

## Main results

* `Turing.MultiTapeTM.rewindWork`: the machine that rewinds a work-tape head to the start of its
  word.
* `Turing.MultiTapeTM.runFrom_rewindWork`: its run from the initial state, with the special cases
  `Turing.MultiTapeTM.runFrom_rewindWork_none` (nothing is written) and
  `Turing.MultiTapeTM.runFrom_rewindWork_erase` (the whole word is erased).
* `Turing.MultiTapeTM.workTapePos_runFrom_rewindWork`: the rewound head stays within `[-1, p]`.
* `Turing.MultiTapeTM.spaceUsed_rewindWork_le`: the machine visits at most `p + k + 1` work-tape
  cells, including the initially occupied cell on each tape.
* `Turing.MultiTapeTM.runFrom_rewindWork_frame`: no run changes the input head, the output, any
  other tape or any other work head.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*} {input : List Symbol}

/-- The control states of the work-tape-rewinding machine: `start` takes one unconditional step
left, `scan` walks left towards the start of the word. -/
public inductive RewindWorkState : Type
  | start
  | scan
  deriving DecidableEq

public instance : Fintype RewindWorkState := ⟨{.start, .scan}, fun q => by cases q <;> simp⟩

/-- The work-tape-rewinding machine for tape `i`. In state `start` it moves the head of tape `i`
left, unconditionally, and enters state `scan`. In state `scan` it writes `write` over a symbol
and moves left, staying in `scan`; on the first blank it moves right and halts. No other tape is
ever written, the input head never moves, no other work head moves and nothing is output. -/
public def rewindWork (Symbol : Type*) (i : Fin k) (write : Option (Option Symbol) := none) :
    MultiTapeTM k Symbol RewindWorkState where
  q₀ := .start
  tr q _ work :=
    match q, work i with
    | .start, _ => .onTape i none (-1) (some .scan)
    | .scan, some _ => .onTape i write (-1) (some .scan)
    | .scan, none => .onTape i none 1 none

namespace RewindWork

variable {i : Fin k} {write : Option (Option Symbol)} {ip : Fin (input.length + 2)}
  {tapes : Fin k → ℤ → Option Symbol} {heads : Fin k → ℤ} {out : List Symbol} {p : ℤ}

/-- Every action of the machine only touches tape `i`. -/
lemma tr_eq (q : RewindWorkState) (inp : Option Symbol) (work : Fin k → Option Symbol) :
    ∃ write' m state, (rewindWork Symbol i write).tr q inp work = .onTape i write' m state := by
  dsimp only [rewindWork]
  split <;> exact ⟨_, _, _, rfl⟩

/-- Moving the head of tape `i` left in state `start`, unconditionally, entering `scan`. -/
lemma step_start :
    (rewindWork Symbol i write).step ⟨some .start, ip, tapes, Function.update heads i p, out⟩ =
      ⟨some .scan, ip, tapes, Function.update heads i (p - 1), out⟩ := by
  rw [step_apply_of_state rfl]
  simp [rewindWork, sub_eq_add_neg]

/-- Walking left in state `scan`: over a symbol the machine writes `write` and the head moves left,
staying in `scan`. -/
lemma step_scan_some {s : Symbol} (hs : tapes i p = some s) :
    (rewindWork Symbol i write).step ⟨some .scan, ip, tapes, Function.update heads i p, out⟩ =
      ⟨some .scan, ip, Function.update tapes i (write.elim (tapes i) (Function.update (tapes i) p)),
        Function.update heads i (p - 1), out⟩ := by
  rw [step_apply_of_state rfl]
  simp [rewindWork, Cfg.workTapeSymbols, hs, Action.apply_onTape, sub_eq_add_neg]

/-- Halting in state `scan`: on a blank cell, the head moves right and the machine halts. -/
lemma step_scan_none (hs : tapes i p = none) :
    (rewindWork Symbol i write).step ⟨some .scan, ip, tapes, Function.update heads i p, out⟩ =
      ⟨none, ip, tapes, Function.update heads i (p + 1), out⟩ := by
  rw [step_apply_of_state rfl]
  simp [rewindWork, Cfg.workTapeSymbols, hs]

/-- The scanning phase: from `scan` at cell `l - 1` of the word, after `n ≤ l` steps the head has
walked left `n` cells, writing `write` to the cells it left. -/
lemma runFrom_scan {w : List Symbol} (hw : tapes i = tapeOfList w) {l : ℕ} (hl : l ≤ w.length)
    (n : ℕ) (hn : n ≤ l) :
    (rewindWork Symbol i write).runFrom
        ⟨some .scan, ip, tapes, Function.update heads i ((l : ℤ) - 1), out⟩ n =
      ⟨some .scan, ip,
        Function.update tapes i
          (fun z => if (l : ℤ) - n ≤ z ∧ z < l then write.getD (tapes i z) else tapes i z),
        Function.update heads i ((l : ℤ) - 1 - n), out⟩ := by
  induction n with
  | zero => simp [runFrom, show ∀ z : ℤ, ¬((l : ℤ) ≤ z ∧ z < l) by lia]
  | succ n ih =>
    have hsym : Function.update tapes i
        (fun z => if (l : ℤ) - n ≤ z ∧ z < l then write.getD (tapes i z) else tapes i z) i
        ((l : ℤ) - 1 - n) = some (w[l - 1 - n]'(by lia)) := by
      rw [Function.update_self, ite_eq_right (by lia), hw,
        show (l : ℤ) - 1 - n = ((l - 1 - n : ℕ) : ℤ) by lia, tapeOfList_ofNat]
      exact List.getElem?_eq_getElem (by lia)
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by lia), step_scan_some hsym,
      Function.update_idem, Function.update_self]
    congr 2
    · cases write with
      | none => simp
      | some c =>
        dsimp
        grind [Function.update_apply]
    · lia

end RewindWork

open RewindWork in
/-- **The run of the machine that rewinds a work-tape head.** Started with tape `i` holding a word
`w` and the head at a position `p ≤ w.length` (inside the word or on the cell just past it),
the machine halts after `p + 2` steps with the head back at position `0`, `write` applied to
the cells `0, …, p - 1` and nothing else changed. -/
public theorem runFrom_rewindWork {i : Fin k} (write : Option (Option Symbol))
    (ip : Fin (input.length + 2)) (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (out : List Symbol) {w : List Symbol} (hw : tapes i = tapeOfList w) {p : ℕ}
    (hp : p ≤ w.length) :
    (rewindWork Symbol i write).runFrom
        ⟨some (rewindWork Symbol i write).q₀, ip, tapes, Function.update heads i p, out⟩ (p + 2) =
      ⟨none, ip,
        Function.update tapes i
          (fun z => if 0 ≤ z ∧ z < p then write.getD (tapes i z) else tapes i z),
        Function.update heads i 0, out⟩ := by
  rw [show (rewindWork Symbol i write).q₀ = .start from rfl, runFrom, Function.iterate_succ_apply,
    step_start, Function.iterate_succ_apply', ← runFrom, runFrom_scan hw hp p le_rfl,
    step_scan_none (by simp [hw]; rfl)]
  simp

/-- **Rewinding without writing** changes nothing but the position of the head. -/
public theorem runFrom_rewindWork_none {i : Fin k} (ip : Fin (input.length + 2))
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ) (out : List Symbol) {w : List Symbol}
    (hw : tapes i = tapeOfList w) {p : ℕ} (hp : p ≤ w.length) :
    (rewindWork Symbol i).runFrom
        ⟨some (rewindWork Symbol i).q₀, ip, tapes, Function.update heads i p, out⟩ (p + 2) =
      ⟨none, ip, tapes, Function.update heads i 0, out⟩ := by
  simpa using runFrom_rewindWork none ip tapes heads out hw hp

/-- **Rewinding while erasing** starting from the cell right after the word leaves tape `i` blank.
-/
public theorem runFrom_rewindWork_erase {i : Fin k} (ip : Fin (input.length + 2))
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ) (out : List Symbol) {w : List Symbol}
    (hw : tapes i = tapeOfList w) :
    (rewindWork Symbol i (some none)).runFrom
        ⟨some (rewindWork Symbol i (some none)).q₀, ip, tapes, Function.update heads i w.length,
          out⟩ (w.length + 2) =
      ⟨none, ip, Function.update tapes i fun _ => none, Function.update heads i 0, out⟩ := by
  rw [runFrom_rewindWork _ ip tapes heads out hw le_rfl]
  congr 2
  funext z
  simp only [hw, Option.getD_some, ite_eq_left_iff, tapeOfList_eq_none_iff]
  lia

open RewindWork in
/-- At every step, the head of tape `i` is within `[-1, p]`: it walks from its start `p ≤ w.length`
down to `-1` and back to `0`, where it stays. -/
public theorem workTapePos_runFrom_rewindWork {i : Fin k} (write : Option (Option Symbol))
    (ip : Fin (input.length + 2)) (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (out : List Symbol) {w : List Symbol} (hw : tapes i = tapeOfList w) {p : ℕ}
    (hp : p ≤ w.length) (m : ℕ) :
    ((rewindWork Symbol i write).runFrom
        ⟨some (rewindWork Symbol i write).q₀, ip, tapes, Function.update heads i p, out⟩
        m).workTapePos i ∈ Set.Icc (-1) (p : ℤ) := by
  rcases m with _ | m
  · simp [runFrom]
  rcases Nat.lt_or_ge m (p + 1) with hlt | hge
  · -- After the initial left move, take `m` scanning steps.
    rw [show (rewindWork Symbol i write).q₀ = .start from rfl, runFrom,
      Function.iterate_succ_apply, step_start, ← runFrom, runFrom_scan hw hp m (by lia)]
    simp only [Function.update_self, Set.mem_Icc]
    constructor <;> lia
  · have hrun := runFrom_rewindWork write ip tapes heads out hw hp
    rw [runFrom_eq_of_halt _ _ (by lia : p + 2 ≤ m + 1) (by rw [hrun]), hrun]
    simp

/-- No run of the machine changes the input head, the output, any tape other than `i` or any work
head other than the head of tape `i`. -/
public theorem runFrom_rewindWork_frame {i : Fin k} (write : Option (Option Symbol))
    (c : Cfg k Symbol RewindWorkState input) (m : ℕ) :
    ((rewindWork Symbol i write).runFrom c m).inputPos = c.inputPos ∧
      (∀ j ≠ i, ((rewindWork Symbol i write).runFrom c m).workTapes j = c.workTapes j ∧
        ((rewindWork Symbol i write).runFrom c m).workTapePos j = c.workTapePos j) ∧
      ((rewindWork Symbol i write).runFrom c m).output = c.output :=
  runFrom_frame_of_onTape RewindWork.tr_eq c m

/-- Rewinding from position `p` visits at most `p + 2` cells on tape `i` and one cell on each
other tape. This bound holds at every step, including after the machine halts. -/
public theorem spaceUsed_rewindWork_le {i : Fin k} {write : Option (Option Symbol)}
    (c : Cfg k Symbol RewindWorkState input) {w : List Symbol} {p m : ℕ}
    (hq : c.state = some .start) (hw : c.workTapes i = tapeOfList w)
    (hp : c.workTapePos i = p) (hlen : p ≤ w.length) :
    (rewindWork Symbol i write).spaceUsed c m ≤ p + k + 1 := by
  calc
    _ ≤ ∑ j : Fin k, (1 + if j = i then p + 1 else 0) := by
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with h
      · subst j
        refine (spaceUsedByTape_le_card c (S := .Icc (-1) p) fun n _ => ?_).trans
          (by rw [Int.card_Icc]; lia)
        simpa only [rewindWork, ← hq, ← hp, Function.update_eq_self,
          Finset.mem_Icc, Set.mem_Icc] using
          workTapePos_runFrom_rewindWork write c.inputPos c.workTapes c.workTapePos c.output
            hw hlen n
      · simpa using spaceUsedByTape_le_one c fun n _ =>
          ((runFrom_rewindWork_frame write c n).2.1 j h).2
    _ = _ := by simp [Finset.sum_add_distrib, Nat.add_comm, Nat.add_assoc]

end Turing.MultiTapeTM
