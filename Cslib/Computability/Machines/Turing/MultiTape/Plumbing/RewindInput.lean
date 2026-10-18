/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes

/-!
# A machine that rewinds the input head

A two-state machine that, when started in its initial state at any input-head position, returns the
head to position 1 (the first input symbol when the input is nonempty, otherwise the right boundary)
and halts there. It has no work tapes at all and never outputs, so running it in between two phases
of a computation re-normalizes the input head without disturbing anything else: place it inside a
machine with `k` work tapes with `Turing.MultiTapeTM.noTapes` and transport its run with
`Turing.MultiTapeTM.runFrom_noTapes`, which leaves every work tape and work head where it was.

In its initial state `start` the machine moves the input head one cell left and enters state `walk`.
The input head is clamped at the left boundary, so this has no effect if the head already is at
position `0`, and it moves a head at the right boundary `input.length + 1` back onto the input.
In state `walk` the machine moves left over symbols. Since the input tape holds a list of
(non-blank) symbols, the first blank to the left of the head is the cell at position `0`; the
halting transition moves right, onto position `1`.

From position `p` the run halts after `p + 1` steps, or after `2` steps if `p = 0`.

## Main results

* `Turing.MultiTapeTM.rewindInput`: the machine that rewinds the input head.
* `Turing.MultiTapeTM.runFrom_rewindInput`: its run from the initial state.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-- The control states of the rewinding machine: `start` takes one unconditional step left,
`walk` moves left towards the left boundary of the input. -/
public inductive RewindState : Type
  | start
  | walk
  deriving DecidableEq

public instance : Fintype RewindState := ⟨{.start, .walk}, fun q => by cases q <;> simp⟩

/-- The only kind of action the rewinding machine takes: move the input head by `m` and enter
`state`, without output. -/
abbrev inputAction (m : SignType) (state : Option RewindState) : Action 0 Symbol RewindState :=
  ⟨m, nofun, none, state⟩

/-- The rewinding machine. In state `start` it moves the input head left, unconditionally, and
enters `walk`. In state `walk` it moves left over a symbol; on the first blank it moves right and
halts. The machine has no work tapes and nothing is output. -/
public def rewindInput (Symbol : Type*) : MultiTapeTM 0 Symbol RewindState :=
  ofTr .start fun q inp _ =>
    match q, inp with
    | .start, _ => inputAction (-1) (some .walk)
    | .walk, some _ => inputAction (-1) (some .walk)
    | .walk, none => inputAction 1 none

namespace Rewind

variable {tapes : Fin 0 → ℤ → Option Symbol} {heads : Fin 0 → ℤ} {out : List Symbol}

/-- A live step moves the input head and changes the state; nothing else changes. -/
lemma step_eq {c : Cfg 0 Symbol RewindState input} {q : RewindState} (hc : c.state = some q) :
    (rewindInput Symbol).step c =
      let a := (rewindInput Symbol).tr q c.inputSymbol c.workTapeSymbols
      ⟨a.state, moveInputPos c.inputPos a.inputTape, c.workTapes, c.workTapePos, c.output⟩ := by
  rw [step_of_state hc]
  refine Cfg.ext rfl rfl (Subsingleton.elim _ _) (Subsingleton.elim _ _) ?_
  simp only [rewindInput, tr_ofTr, Action.apply_output]
  split <;> simp

/-- From `walk` at position `p ≤ input.length` the machine halts with the input head at position `1`
after `p + 1` steps. -/
lemma runFrom_walk (p : Fin (input.length + 2)) (hp : p.val ≤ input.length) :
    (rewindInput Symbol).runFrom ⟨some .walk, p, tapes, heads, out⟩ (p.val + 1) =
      ⟨none, 1, tapes, heads, out⟩ := by
  induction hj : p.val generalizing p with
  | zero =>
    obtain rfl : p = 0 := Fin.ext hj
    rw [runFrom, Function.iterate_one, step_eq rfl, inputSymbol_eq_none_of_boundary (.inl rfl)]
    simp only [rewindInput, tr_ofTr]
    rfl
  | succ j ih =>
    rw [runFrom, Function.iterate_succ_apply, ← runFrom, step_eq rfl,
      inputSymbolInner j (by grind) (by omega)]
    simp only [rewindInput, tr_ofTr]
    exact ih (moveInputPos p .neg) (by grind [SignType.cast]) (by grind [SignType.cast])

end Rewind

/-- From its initial state at input position `p` the machine halts after `p - 1 + 2` steps, with
the input head at position `1` and everything else unchanged. -/
public theorem runFrom_rewindInput (p : Fin (input.length + 2))
    (tapes : Fin 0 → ℤ → Option Symbol) (heads : Fin 0 → ℤ) (out : List Symbol) :
    (rewindInput Symbol).runFrom ⟨some (rewindInput Symbol).q₀, p, tapes, heads, out⟩
      (p.val - 1 + 2) = ⟨none, 1, tapes, heads, out⟩ := by
  have h : (moveInputPos p .neg).val = p.val - 1 := by grind [SignType.cast]
  rw [runFrom, Function.iterate_succ_apply, Rewind.step_eq rfl, ← runFrom, ← h]
  simp only [rewindInput, tr_ofTr]
  exact Rewind.runFrom_walk (moveInputPos p .neg) (by omega)

end Turing.MultiTapeTM
