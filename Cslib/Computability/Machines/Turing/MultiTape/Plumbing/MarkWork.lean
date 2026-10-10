/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# A machine that marks the cell left of its head

`markWork Symbol write` is a machine with one work tape that writes `write` to the cell left of its
head and moves the head back, halting after two steps. It neither moves the input head nor emits
output. To use it on tape `i` of a machine with more tapes, embed it with
`Turing.MultiTapeTM.tapeEmb`.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-- The states of `markWork`: `start` steps left, `put` writes and steps back. -/
public inductive MarkWorkState : Type
  | start
  | put
  deriving DecidableEq

public instance : Fintype MarkWorkState := ⟨{.start, .put}, fun q => by cases q <;> simp⟩

/-- `markWork Symbol write` steps left, writes `write` (erasing if `write = none`), steps back
right and halts. -/
public def markWork (Symbol : Type*) (write : Option Symbol) :
    MultiTapeTM 1 Symbol MarkWorkState :=
  ofTr .start fun q _ _ =>
    match q with
    | .start => ⟨0, fun _ => (none, -1), none, some .put⟩
    | .put => ⟨0, fun _ => (some write, 1), none, none⟩

/-- Started with its head at `p`, after two steps `markWork Symbol write` has halted with `write`
at cell `p - 1` and its head back at `p`. -/
public theorem runFrom_markWork (write : Option Symbol) (ip : Fin (input.length + 2))
    (tp : ℤ → Option Symbol) (out : List Symbol) (p : ℤ) :
    (markWork Symbol write).runFrom
        ⟨some (markWork Symbol write).q₀, ip, fun _ => tp, fun _ => p, out⟩ 2 =
      ⟨none, ip, fun _ => Function.update tp (p - 1) write, fun _ => p, out⟩ := by
  simp [runFrom, step_of_state, markWork, Action.apply, sub_eq_add_neg]

/-- `markWork Symbol write` visits at most two cells: its starting cell and the one to its left. -/
public theorem spaceUsed_markWork_le (write : Option Symbol) (ip : Fin (input.length + 2))
    (tp : ℤ → Option Symbol) (out : List Symbol) (p : ℤ) (n : ℕ) :
    (markWork Symbol write).spaceUsed
        ⟨some (markWork Symbol write).q₀, ip, fun _ => tp, fun _ => p, out⟩ n ≤ 2 := by
  rw [spaceUsed, Fin.sum_univ_one]
  refine (spaceUsedByTape_le_card _ (S := {p - 1, p}) fun m _ => ?_).trans Finset.card_le_two
  match m with
  | 0 => simp [runFrom]
  | 1 => simp [runFrom, step_of_state, markWork, Action.apply, sub_eq_add_neg]
  | m + 2 =>
    rw [runFrom_eq_of_halt _ _ (by omega : 2 ≤ m + 2) (by rw [runFrom_markWork]),
      runFrom_markWork]
    simp

end Turing.MultiTapeTM
