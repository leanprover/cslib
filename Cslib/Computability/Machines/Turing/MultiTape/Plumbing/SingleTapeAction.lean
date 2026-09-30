/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Actions on a single work tape

Small plumbing machines typically operate on one designated work tape only: they never move the
input head, never output and leave every other work tape alone. `Turing.Action.onTape` is the
action of such a machine, so its transition function only needs to name what happens on the
designated tape.

## Main definitions

* `Turing.Action.onTape`: the action that only touches one work tape.

## Main results

* `Turing.Action.onTape_workTapes_self`, `Turing.Action.onTape_workTapes_of_ne`: the effect of
  `onTape` on the designated and on every other work tape.
* `Turing.Action.apply_onTape`: applying `onTape` changes only the state, the designated tape and
  its head.
* `Turing.MultiTapeTM.runFrom_frame_of_onTape`: a machine whose actions are all `onTape i` actions
  never moves the input head, never outputs and never touches any work tape other than `i`.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The action that only touches work tape `i`: it writes `write` to tape `i`, moves its head by
`move` and enters `state`. The input head and all other work heads stay put, no other work tape is
written and nothing is output. -/
@[simps inputTape output state]
def Action.onTape (i : Fin k) (write : Option (Option Symbol)) (move : SignType)
    (state : Option State) : Action k Symbol State :=
  ⟨0, Function.update (fun _ => (none, 0)) i (write, move), none, state⟩

namespace Action

variable {i : Fin k} {write : Option (Option Symbol)} {move : SignType} {state : Option State}

/-- On tape `i` the action writes `write` and moves by `move`. -/
@[simp]
lemma onTape_workTapes_self :
    (onTape i write move state).workTapes i = (write, move) := by
  simp [onTape]

/-- Every other work tape is neither written nor moved. -/
@[simp]
lemma onTape_workTapes_of_ne {l : Fin k} (h : l ≠ i) :
    (onTape i write move state).workTapes l = (none, 0) := by
  simp [onTape, h]

/-- An action writing nothing to tape `i` writes nothing at all. -/
@[simp]
lemma onTape_workTapes_fst_none (l : Fin k) :
    ((onTape i (none : Option (Option Symbol)) move state).workTapes l).1 = none := by
  by_cases h : l = i <;> simp [h]

/-- An action not moving the head of tape `i` moves no work head at all. -/
@[simp]
lemma onTape_workTapes_snd_zero (l : Fin k) :
    ((onTape i write (0 : SignType) state).workTapes l).2 = 0 := by
  by_cases h : l = i <;> simp [h]

/-- Applying `onTape` changes only the state, tape `i` and the head of tape `i`. -/
lemma apply_onTape (cfg : Cfg k Symbol State input) :
    (onTape i write move state).apply cfg =
      ⟨state, cfg.inputPos,
        Function.update cfg.workTapes i
          (write.elim (cfg.workTapes i) (Function.update (cfg.workTapes i) (cfg.workTapePos i))),
        Function.update cfg.workTapePos i (cfg.workTapePos i + move), cfg.output⟩ := by
  refine Cfg.ext rfl (by simp) ?_ ?_ (by simp)
  · refine Function.eq_update_iff.2 ⟨?_, fun l hl => by simp [hl]⟩
    cases write with
    | none => simp
    | some s => simp
  · exact Function.eq_update_iff.2 ⟨by simp, fun l hl => by simp [hl]⟩

/-- Applying an `onTape` action that writes nothing changes only the state and the head of
tape `i`. -/
@[simp]
lemma apply_onTape_none (cfg : Cfg k Symbol State input) :
    (onTape i (none : Option (Option Symbol)) move state).apply cfg =
      ⟨state, cfg.inputPos, cfg.workTapes,
        Function.update cfg.workTapePos i (cfg.workTapePos i + move), cfg.output⟩ := by
  simp [apply_onTape]

end Action

/-- **The frame of a single-tape machine.** A machine whose actions are all `onTape i` actions
never moves the input head, never outputs and never writes or moves any work tape other than
`i`. -/
theorem MultiTapeTM.runFrom_frame_of_onTape {tm : MultiTapeTM k Symbol State}
    {i : Fin k} (htr : ∀ q inp work, ∃ write move state,
      tm.tr q inp work = .onTape i write move state)
    (c : Cfg k Symbol State input) (m : ℕ) :
    (tm.runFrom c m).inputPos = c.inputPos ∧
      (∀ j ≠ i, (tm.runFrom c m).workTapes j = c.workTapes j ∧
        (tm.runFrom c m).workTapePos j = c.workTapePos j) ∧
      (tm.runFrom c m).output = c.output := by
  induction m with
  | zero => exact ⟨rfl, fun _ _ => ⟨rfl, rfl⟩, rfl⟩
  | succ m ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    generalize tm.runFrom c m = c' at ih ⊢
    cases hc : c'.state with
    | none => rwa [step_of_halt hc]
    | some q =>
      obtain ⟨_, _, _, h⟩ := htr q c'.inputSymbol c'.workTapeSymbols
      rw [step_apply_of_state hc, h, Action.apply_onTape]
      exact ⟨ih.1, fun j hj => by simpa [Function.update_of_ne hj] using ih.2.1 j hj, ih.2.2⟩

end Turing
