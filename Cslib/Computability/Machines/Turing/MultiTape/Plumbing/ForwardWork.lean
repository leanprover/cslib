/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# A machine that moves to the end of a word

`forwardWork Symbol` moves the head of its work tape to the right over the word it holds and halts
on the frontier, the first blank cell just past the word. It never modifies a tape, never moves the
input head and never outputs.

On a word of length `l`, started with the head at cell `p ≤ l`, the machine takes `l - p + 1` steps
and the head stays within the cells `p, …, l`.

This is a one-tape machine; to move the head of tape `i` of a `k`-tape machine to the end of its
word, place it there with `Turing.MultiTapeTM.tapeEmb` and transport its run with
`Turing.MultiTapeTM.runFrom_tapeEmb`. The input head, the output and every other tape are then
untouched by construction.

## Main results

* `Turing.MultiTapeTM.forwardWork`: the one-tape machine that moves its head to the frontier of
  its word.
* `Turing.MultiTapeTM.runFrom_forwardWork`: its run from the initial state.
* `Turing.MultiTapeTM.workTapePos_runFrom_forwardWork`: its head stays within `[p, w.length]`.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-- The one-tape machine that moves its head to the end of its word. Over a symbol it moves right;
on the first blank it halts without moving. -/
public def forwardWork (Symbol : Type*) : MultiTapeTM 1 Symbol Unit :=
  ofTr () fun _ _ work ↦
    match work 0 with
    | some _ => ⟨0, fun _ => (none, 1), none, some ()⟩
    | none => ⟨0, fun _ => (none, 0), none, none⟩

namespace ForwardWork

variable {inpos : Fin (input.length + 2)} {out : List Symbol}

/-- Walking right over the word: from cell `p`, after `n` steps with `p + n ≤ w.length` the head
is at cell `p + n`. -/
lemma runFrom_walk {w : List Symbol} {p : ℕ} (n : ℕ) (hn : p + n ≤ w.length) :
    (forwardWork Symbol).runFrom
        ⟨some (), inpos, fun _ => tapeOfList w, fun _ => (p : ℤ), out⟩ n =
      ⟨some (), inpos, fun _ => tapeOfList w, fun _ => (p : ℤ) + n, out⟩ := by
  induction n with
  | zero => simp [runFrom]
  | succ n ih =>
    have hsym : tapeOfList w ((p : ℤ) + n) = some (w[p + n]'(by lia)) := by
      rw [← Nat.cast_add, tapeOfList_ofNat]
      exact List.getElem?_eq_getElem (by lia)
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by lia), step_of_state rfl]
    simp [forwardWork, Action.apply, Cfg.workTapeSymbols, hsym, add_assoc]

end ForwardWork

open ForwardWork in
/-- **The run of the machine that moves to the end of the word.** Started with the tape holding a
word `w` and the head at a cell `p` with `p + n = w.length`, after `n + 1` steps the machine has
halted with the head on the frontier `w.length` and nothing else changed. -/
public theorem runFrom_forwardWork (inpos : Fin (input.length + 2)) (w : List Symbol)
    (out : List Symbol) {p n : ℕ} (hpn : p + n = w.length) :
    (forwardWork Symbol).runFrom
        ⟨some (forwardWork Symbol).q₀, inpos, fun _ => tapeOfList w, fun _ => (p : ℤ), out⟩
        (n + 1) =
      ⟨none, inpos, fun _ => tapeOfList w, fun _ => (w.length : ℤ), out⟩ := by
  rw [runFrom, Function.iterate_succ_apply', ← runFrom, runFrom_walk _ hpn.le,
    show (p : ℤ) + n = w.length by lia, step_of_state rfl]
  simp [forwardWork, Action.apply, Cfg.workTapeSymbols]

/-- At every step, the head is within `[p, w.length]`. -/
public theorem workTapePos_runFrom_forwardWork (inpos : Fin (input.length + 2))
    (w : List Symbol) (out : List Symbol) {p : ℕ} (hp : p ≤ w.length) (m : ℕ) :
    ((forwardWork Symbol).runFrom
        ⟨some (forwardWork Symbol).q₀, inpos, fun _ => tapeOfList w, fun _ => (p : ℤ), out⟩
        m).workTapePos 0 ∈ Set.Icc (p : ℤ) w.length := by
  rcases Nat.lt_or_ge m (w.length - p + 1) with hlt | hge
  · rw [ForwardWork.runFrom_walk m (by lia)]
    simp only [Set.mem_Icc]
    constructor <;> lia
  · have hrun := runFrom_forwardWork inpos w out (Nat.add_sub_cancel' hp)
    rw [runFrom_eq_of_halt _ _ hge (by rw [hrun]), hrun]
    simp [hp]

end Turing.MultiTapeTM
