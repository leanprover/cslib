/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# A machine that marks the cell left of its head

A tiny one-work-tape machine that writes a chosen symbol (or blank) into the cell immediately to
the left of its head and returns the head to where it started. It runs in exactly two steps and
touches nothing but a single cell of its work tape.

In its initial state `start` the machine takes one unconditional step left, into state `put`. In
state `put` it writes `write` to the cell under the head and moves right, back to the starting
position, and halts. The input head never moves and nothing is ever output.

This is a one-tape machine; to mark a cell of tape `i` of a `k`-tape machine, place it there with
`Turing.MultiTapeTM.tapeEmb` and transport its run with `Turing.MultiTapeTM.runFrom_tapeEmb`. The
input head, the output and every other tape are then untouched by construction.

## Main results

* `Turing.MultiTapeTM.markWork`: the one-tape machine that marks the cell left of its head.
* `Turing.MultiTapeTM.runFrom_markWork`: its run from the initial state.
* `Turing.MultiTapeTM.workTapePos_runFrom_markWork`: the head stays within `[p - 1, p]`.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-- Control states of `markWork`: `start` steps one cell left, `put` writes and steps back. -/
public inductive MarkWorkState : Type
  | start
  | put
  deriving DecidableEq

public instance : Fintype MarkWorkState := ⟨{.start, .put}, fun q => by cases q <;> simp⟩

/-- `markWork Symbol write`: from its head at cell `p`, step left to `p-1`, write `write` there
(erasing when `write = none`), step back to `p`, and halt. One work tape, no input moves, no
output. -/
public def markWork (Symbol : Type*) (write : Option Symbol) :
    MultiTapeTM 1 Symbol MarkWorkState :=
  ofTr .start fun q _ _ =>
    match q with
    | .start => ⟨0, fun _ => (none, -1), none, some .put⟩
    | .put => ⟨0, fun _ => (some write, 1), none, none⟩

namespace MarkWork

variable {write : Option Symbol} {ip : Fin (input.length + 2)} {tp : ℤ → Option Symbol}
  {out : List Symbol} {p : ℤ}

/-- Stepping left in state `start`, unconditionally, entering `put`. -/
lemma step_start :
    (markWork Symbol write).step ⟨some .start, ip, fun _ => tp, fun _ => p, out⟩ =
      ⟨some .put, ip, fun _ => tp, fun _ => p - 1, out⟩ := by
  rw [step_of_state rfl]
  simp [markWork, Action.apply, sub_eq_add_neg]

/-- Writing in state `put`: the head is at `p - 1`, the machine writes `write` there, moves right
back to `p` and halts. -/
lemma step_put :
    (markWork Symbol write).step ⟨some .put, ip, fun _ => tp, fun _ => p - 1, out⟩ =
      ⟨none, ip, fun _ => Function.update tp (p - 1) write, fun _ => p, out⟩ := by
  rw [step_of_state rfl]
  simp [markWork, Action.apply, sub_eq_add_neg]

end MarkWork

open MarkWork in
/-- From head at `p`, after 2 steps the cell `p-1` holds `write` and the head is back at `p`;
nothing else changes. `ip`, `out` and the input tape are untouched. -/
public theorem runFrom_markWork (write : Option Symbol) {input : List Symbol}
    (ip : Fin (input.length + 2)) (tp : ℤ → Option Symbol) (out : List Symbol) (p : ℤ) :
    (markWork Symbol write).runFrom
        ⟨some (markWork Symbol write).q₀, ip, fun _ => tp, fun _ => p, out⟩ 2 =
      ⟨none, ip, fun _ => Function.update tp (p - 1) write, fun _ => p, out⟩ := by
  rw [show (markWork Symbol write).q₀ = .start from rfl, runFrom, Function.iterate_succ_apply,
    step_start, Function.iterate_one, step_put]

open MarkWork in
/-- The work-tape head stays within `[p-1, p]` throughout the run. -/
public theorem workTapePos_runFrom_markWork (write : Option Symbol) {input : List Symbol}
    (ip : Fin (input.length + 2)) (tp : ℤ → Option Symbol) (out : List Symbol) (p : ℤ)
    (n : ℕ) :
    ((markWork Symbol write).runFrom
        ⟨some (markWork Symbol write).q₀, ip, fun _ => tp, fun _ => p, out⟩ n).workTapePos 0
      ∈ Set.Icc (p - 1) p := by
  match n with
  | 0 => simp [runFrom]
  | 1 =>
    rw [show (markWork Symbol write).q₀ = .start from rfl, runFrom, Function.iterate_one,
      step_start]
    simp only [Set.mem_Icc]
    constructor <;> omega
  | (m + 2) =>
    rw [runFrom_eq_of_halt _ _ (by omega : 2 ≤ m + 2)
      (by rw [runFrom_markWork]), runFrom_markWork]
    simp only [Set.mem_Icc]
    constructor <;> omega

end Turing.MultiTapeTM
