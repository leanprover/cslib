/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# A machine that rewinds a work-tape head

A machine that moves the head of its work tape to the left end of its contents and halts. It
optionally writes a certain symbol to or clears the cells it moves over while traveling to the
left. The input tape is not modified. This machine can be run between two phases of a computation
to re-normalise a work-tape head without disturbing anything else.

In its initial state `start` the machine takes one unconditional step left, into state `scan`. In
state `scan` it walks left over symbols, writing `write` to every cell it leaves; on the first
blank it moves the head right and halts. By default `write` is `none` and the machine writes
nothing; with `write := some none` it erases the part of the word it walks over.

This is a one-tape machine; to rewind tape `i` of a `k`-tape machine, place it there with
`Turing.MultiTapeTM.tapeEmb` and transport its run with
`Turing.MultiTapeTM.runFrom_tapeEmb`. The input head, the output and every other tape are then
untouched by construction.

## Main results

* `Turing.MultiTapeTM.rewindWork`: the one-tape machine that rewinds its head to the start of its
  word.
* `Turing.MultiTapeTM.runFrom_rewindWork`: its run from the initial state, with the special cases
  `Turing.MultiTapeTM.runFrom_rewindWork_none` (nothing is written) and
  `Turing.MultiTapeTM.runFrom_rewindWork_erase` (the whole word is erased).
* `Turing.MultiTapeTM.workTapePos_runFrom_rewindWork`: the rewound head stays within `[-1, p]`.
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

/-- The one-tape rewinding machine. In state `start` it moves its head left, unconditionally, and
enters state `scan`. In state `scan` it writes `write` over a symbol and moves left, staying in
`scan`; on the first blank it moves right and halts. The input head never moves and nothing is
ever output. -/
public def rewindWork (Symbol : Type*) (write : Option (Option Symbol) := none) :
    MultiTapeTM 1 Symbol RewindWorkState where
  q₀ := .start
  tr q _ work :=
    match q, work 0 with
    | .start, _ => ⟨0, fun _ => (none, -1), none, some .scan⟩
    | .scan, some _ => ⟨0, fun _ => (write, -1), none, some .scan⟩
    | .scan, none => ⟨0, fun _ => (none, 1), none, none⟩

namespace RewindWork

variable {write : Option (Option Symbol)} {ip : Fin (input.length + 2)} {t : ℤ → Option Symbol}
  {out : List Symbol} {p : ℤ}

/-- Moving the head left in state `start`, unconditionally, entering `scan`. -/
lemma step_start :
    (rewindWork Symbol write).step ⟨some .start, ip, fun _ => t, fun _ => p, out⟩ =
      ⟨some .scan, ip, fun _ => t, fun _ => p - 1, out⟩ := by
  rw [step_apply_of_state rfl]
  simp [rewindWork, Action.apply, sub_eq_add_neg]

/-- Walking left in state `scan`: over a symbol the machine writes `write` and the head moves left,
staying in `scan`. -/
lemma step_scan_some {s : Symbol} (hs : t p = some s) :
    (rewindWork Symbol write).step ⟨some .scan, ip, fun _ => t, fun _ => p, out⟩ =
      ⟨some .scan, ip, fun _ => write.elim t (Function.update t p), fun _ => p - 1, out⟩ := by
  rw [step_apply_of_state rfl]
  cases write <;> simp [rewindWork, Action.apply, Cfg.workTapeSymbols, hs, sub_eq_add_neg]

/-- Halting in state `scan`: on the first blank — the cell at position `-1` — the head moves right
and the machine halts. -/
lemma step_scan_none (hs : t p = none) :
    (rewindWork Symbol write).step ⟨some .scan, ip, fun _ => t, fun _ => p, out⟩ =
      ⟨none, ip, fun _ => t, fun _ => p + 1, out⟩ := by
  rw [step_apply_of_state rfl]
  simp [rewindWork, Action.apply, Cfg.workTapeSymbols, hs]

/-- The scanning phase: from `scan` at cell `l - 1` of the word, after `n ≤ l` steps the head has
walked left `n` cells, writing `write` to the cells it left. -/
lemma runFrom_scan {w : List Symbol} (hw : t = tapeOfList w) {l : ℕ} (hl : l ≤ w.length) (n : ℕ)
    (hn : n ≤ l) :
    (rewindWork Symbol write).runFrom
        ⟨some .scan, ip, fun _ => t, fun _ => (l : ℤ) - 1, out⟩ n =
      ⟨some .scan, ip, fun _ z => if (l : ℤ) - n ≤ z ∧ z < l then write.getD (t z) else t z,
        fun _ => (l : ℤ) - 1 - n, out⟩ := by
  induction n with
  | zero => simp [runFrom, show ∀ z : ℤ, ¬((l : ℤ) ≤ z ∧ z < l) by omega]
  | succ n ih =>
    have hsym : (fun z => if (l : ℤ) - n ≤ z ∧ z < l then write.getD (t z) else t z)
        ((l : ℤ) - 1 - n) = some (w[l - 1 - n]'(by omega)) := by
      dsimp only
      rw [ite_eq_right (by omega), hw,
        show (l : ℤ) - 1 - n = ((l - 1 - n : ℕ) : ℤ) by omega, tapeOfList_ofNat]
      exact List.getElem?_eq_getElem (by omega)
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega), step_scan_some hsym]
    congr 2
    · cases write with
      | none => simp
      | some c =>
        funext _ z
        simp only [Option.elim_some, Function.update_apply, Option.getD_some]
        split_ifs <;> first | rfl | omega
    · funext _
      omega

end RewindWork

open RewindWork in
/-- **The run of the one-tape machine that rewinds its head.** Started with the tape holding a word
`w` and the head at a position `p ≤ w.length` — inside the word or at the frontier just past it —
after `p + 2` steps the machine has halted with the head back at position `0`, `write` applied to
the cells `0, …, p - 1` and nothing else changed. -/
public theorem runFrom_rewindWork (write : Option (Option Symbol)) (ip : Fin (input.length + 2))
    (t : ℤ → Option Symbol) (out : List Symbol) {w : List Symbol} (hw : t = tapeOfList w) {p : ℕ}
    (hp : p ≤ w.length) :
    (rewindWork Symbol write).runFrom
        ⟨some (rewindWork Symbol write).q₀, ip, fun _ => t, fun _ => (p : ℤ), out⟩ (p + 2) =
      ⟨none, ip, fun _ z => if 0 ≤ z ∧ z < p then write.getD (t z) else t z, fun _ => 0, out⟩ := by
  rw [show (rewindWork Symbol write).q₀ = .start from rfl, runFrom, Function.iterate_succ_apply,
    step_start, Function.iterate_succ_apply', ← runFrom, runFrom_scan hw hp p le_rfl,
    show (p : ℤ) - 1 - p = -1 by omega, step_scan_none (by simp [hw]; rfl)]
  simp

/-- **Rewinding without writing** changes nothing but the position of the head. -/
public theorem runFrom_rewindWork_none (ip : Fin (input.length + 2)) (t : ℤ → Option Symbol)
    (out : List Symbol) {w : List Symbol} (hw : t = tapeOfList w) {p : ℕ} (hp : p ≤ w.length) :
    (rewindWork Symbol).runFrom
        ⟨some (rewindWork Symbol).q₀, ip, fun _ => t, fun _ => (p : ℤ), out⟩ (p + 2) =
      ⟨none, ip, fun _ => t, fun _ => 0, out⟩ := by
  simpa using runFrom_rewindWork none ip t out hw hp

/-- **Rewinding while erasing** from the frontier of the word leaves the tape blank. -/
public theorem runFrom_rewindWork_erase (ip : Fin (input.length + 2)) (t : ℤ → Option Symbol)
    (out : List Symbol) {w : List Symbol} (hw : t = tapeOfList w) :
    (rewindWork Symbol (some none)).runFrom
        ⟨some (rewindWork Symbol (some none)).q₀, ip, fun _ => t, fun _ => (w.length : ℤ), out⟩
        (w.length + 2) =
      ⟨none, ip, fun _ _ => none, fun _ => 0, out⟩ := by
  rw [runFrom_rewindWork _ ip t out hw le_rfl]
  congr 2
  funext _ z
  split_ifs with h
  · rfl
  · rw [hw, tapeOfList_eq_none_iff]
    omega

open RewindWork in
/-- At every step, the head is within `[-1, p]`: it walks from its start `p ≤ w.length` down to
`-1` and back to `0`, where it stays. -/
public theorem workTapePos_runFrom_rewindWork (write : Option (Option Symbol))
    (ip : Fin (input.length + 2)) (t : ℤ → Option Symbol) (out : List Symbol) {w : List Symbol}
    (hw : t = tapeOfList w) {p : ℕ} (hp : p ≤ w.length) (m : ℕ) :
    ((rewindWork Symbol write).runFrom
        ⟨some (rewindWork Symbol write).q₀, ip, fun _ => t, fun _ => (p : ℤ), out⟩
        m).workTapePos 0 ∈ Set.Icc (-1) (p : ℤ) := by
  rcases m with _ | m
  · simp [runFrom]
  rcases Nat.lt_or_ge m (p + 1) with hlt | hge
  · -- After the initial left move, take `m` scanning steps.
    rw [show (rewindWork Symbol write).q₀ = .start from rfl, runFrom, Function.iterate_succ_apply,
      step_start, ← runFrom, runFrom_scan hw hp m (by omega)]
    simp only [Set.mem_Icc]
    constructor <;> omega
  · have hrun := runFrom_rewindWork write ip t out hw hp
    rw [runFrom_eq_of_halt _ _ (by omega : p + 2 ≤ m + 1) (by rw [hrun]), hrun]
    simp

end Turing.MultiTapeTM
