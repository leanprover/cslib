/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# A machine that writes the cell to the left of its head

A two-state, one-tape machine that writes a symbol into the cell immediately left of its head and
puts the head back where it was. It is the smallest machine that leaves the normal form of
`Turing.MultiTapeTM.TransformsTapes` — in which a tape is blank at every negative cell — and comes
back to it, which is exactly what is needed to set up and tear down the *flag tape* of
`Turing.MultiTapeTM.inputFromTape`, whose mark lives at cell `-1`.

In its initial state `start` the machine moves its head one cell left and enters state `write`. In
state `write` it writes `w`, moves the head one cell right and halts. The run therefore takes two
steps, touches two cells and leaves nothing else changed; with `w := none` it erases the cell
again.

## Main results

* `Turing.MultiTapeTM.writeLeft`: the machine.
* `Turing.MultiTapeTM.runFrom_writeLeft`: its run, in two steps.
* `Turing.MultiTapeTM.spaceUsed_writeLeft_le`: it touches two cells.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-- The control states of the machine that writes the cell to its left: `start` moves the head
left, `write` writes and moves it back. -/
public inductive WriteLeftState : Type
  | start
  | write
  deriving DecidableEq

public instance : Fintype WriteLeftState := ⟨{.start, .write}, fun q => by cases q <;> simp⟩

/-- The one-tape machine that writes `w` into the cell left of its head and returns the head to
its starting position. The input head never moves and nothing is ever output. -/
@[expose] public def writeLeft (w : Option Symbol) : MultiTapeTM 1 Symbol WriteLeftState where
  q₀ := .start
  tr q _ _ :=
    match q with
    | .start => ⟨0, fun _ => (none, -1), none, some .write⟩
    | .write => ⟨0, fun _ => (some w, 1), none, none⟩

@[simp]
public lemma writeLeft_q₀ (w : Option Symbol) :
    (writeLeft w).q₀ = (WriteLeftState.start : WriteLeftState) := rfl

namespace WriteLeft

variable {w : Option Symbol} {ip : Fin (input.length + 2)} {t : ℤ → Option Symbol}
  {out : List Symbol} {p : ℤ}

/-- Moving the head left in state `start`, unconditionally, entering `write`. -/
private lemma step_start :
    (writeLeft w).step ⟨some .start, ip, fun _ => t, fun _ => p, out⟩ =
      ⟨some .write, ip, fun _ => t, fun _ => p - 1, out⟩ := by
  rw [step_apply_of_state rfl]
  simp [writeLeft, Action.apply, sub_eq_add_neg]

/-- Writing and moving back in state `write`, halting. -/
private lemma step_write :
    (writeLeft w).step ⟨some .write, ip, fun _ => t, fun _ => p, out⟩ =
      ⟨none, ip, fun _ => Function.update t p w, fun _ => p + 1, out⟩ := by
  rw [step_apply_of_state rfl]
  simp [writeLeft, Action.apply]

end WriteLeft

open WriteLeft in
/-- **The run of the machine that writes the cell to its left.** After two steps the cell at
`p - 1` holds `w`, the head is back at `p` and nothing else has changed. -/
public theorem runFrom_writeLeft (w : Option Symbol) (ip : Fin (input.length + 2))
    (t : ℤ → Option Symbol) (out : List Symbol) (p : ℤ) :
    (writeLeft w).runFrom ⟨some (writeLeft w).q₀, ip, fun _ => t, fun _ => p, out⟩ 2 =
      ⟨none, ip, fun _ => Function.update t (p - 1) w, fun _ => p, out⟩ := by
  rw [writeLeft_q₀, runFrom, Function.iterate_succ_apply, step_start,
    Function.iterate_succ_apply, step_write]
  simp

open WriteLeft in
/-- The head only ever stands at `p` or at `p - 1`. -/
public theorem workTapePos_runFrom_writeLeft (w : Option Symbol) (ip : Fin (input.length + 2))
    (t : ℤ → Option Symbol) (out : List Symbol) (p : ℤ) (m : ℕ) :
    ((writeLeft w).runFrom ⟨some (writeLeft w).q₀, ip, fun _ => t, fun _ => p, out⟩
        m).workTapePos 0 ∈ ({p - 1, p} : Finset ℤ) := by
  have hrun := runFrom_writeLeft w ip t out p
  rcases m with _ | _ | m
  · simp [runFrom]
  · rw [writeLeft_q₀, runFrom, Function.iterate_succ_apply, Function.iterate_zero_apply, step_start]
    simp
  · rw [runFrom_eq_of_halt _ _ (by omega : 2 ≤ m + 1 + 1) (by rw [hrun]), hrun]
    simp

/-- **Space of the machine that writes the cell to its left:** the two cells `p - 1` and `p`. -/
public theorem spaceUsed_writeLeft_le (w : Option Symbol) (ip : Fin (input.length + 2))
    (t : ℤ → Option Symbol) (out : List Symbol) (p : ℤ) (n : ℕ) :
    (writeLeft w).spaceUsed ⟨some (writeLeft w).q₀, ip, fun _ => t, fun _ => p, out⟩ n ≤ 2 := by
  simp only [spaceUsed, Fin.sum_univ_one]
  refine le_trans (spaceUsedByTape_le_card _ (S := {p - 1, p})
    fun m _ => workTapePos_runFrom_writeLeft w ip t out p m) ?_
  exact le_trans (Finset.card_insert_le _ _) (by simp)

end Turing.MultiTapeTM
