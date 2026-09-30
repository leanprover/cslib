/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Configuration

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
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*}

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

end Action

end Turing
