/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Complexity of the identity function

A machine with a single state and no work tapes scans the input from left to right, copying each
symbol to the output tape, and halts on the blank at the right end of the input. On input `w` it
outputs `w` after `w.length + 1` steps, and having no work tapes it uses zero space.

## Main results

* `Turing.MultiTapeTM.computableInTimeAndSpace_id`: the identity is computable in one step per
  input symbol and zero space.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-- The copy machine: a single state and no work tapes. It copies every input symbol to the output
tape while moving right, and halts on reading the blank at the right end of the input. -/
def copy : MultiTapeTM 0 Symbol Unit where
  q₀ := ()
  tr _ s _ :=
    match s with
    | some b => { inputTape := 1, workTapes := Fin.elim0, output := some b, state := some () }
    | none => { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }

namespace Copy

/-- The configuration of the copy machine in state `q` after copying the first `n` input symbols
to the output: the input head is over cell `n + 1` (capped at the right end marker) and there are
no work tapes. `input` is explicit because it only occurs in the type. -/
def cfg (input : List Symbol) (q : Option Unit) (n : ℕ) : Cfg 0 Symbol Unit input :=
  ⟨q, ⟨min (n + 1) (input.length + 1), by omega⟩, fun _ _ => none, fun _ => 0, input.take n⟩

/-- Over an input symbol, the copy machine emits it and moves right. -/
lemma step_scan {n : ℕ} (hn : n < input.length) :
    copy.step (cfg input (some ()) n) = cfg input (some ()) (n + 1) := by
  have hsym : (cfg input (some ()) n).inputSymbol = some input[n] :=
    inputSymbolInner n (by simp [cfg]; omega) hn
  rw [step_apply_of_state rfl, hsym]
  apply Cfg.ext_zero_tapes (by rfl)
  · simp [cfg, copy, moveInputPos]
    grind
  · simp only [cfg, copy, Action.apply, Option.toList_some]
    grind [List.take_add_one]

/-- On the blank at the right end of the input, the copy machine halts in place. -/
lemma step_halt :
    copy.step (cfg input (some ()) input.length) = cfg input none input.length := by
  have hsym : (cfg input (some ()) input.length).inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (Or.inr (by simp [cfg]))
  rw [step_apply_of_state rfl, hsym]
  apply Cfg.ext_zero_tapes <;> simp [cfg, copy, Action.apply]

/-- After `n ≤ input.length` steps, the copy machine has copied the first `n` input symbols. -/
lemma runFrom_scan (n : ℕ) (hn : n ≤ input.length) :
    copy.runFrom (copy.initCfg input) n = cfg input (some ()) n := by
  induction n with
  | zero => exact Cfg.ext_zero_tapes rfl rfl rfl
  | succ n ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, ih (by omega), step_scan (by omega)]

/-- The complete run: after `input.length + 1` steps the copy machine has halted with the input
copied to the output. -/
lemma runFrom_full (input : List Symbol) :
    copy.runFrom (copy.initCfg input) (input.length + 1) = cfg input none input.length := by
  rw [runFrom, Function.iterate_succ_apply', ← runFrom, runFrom_scan _ le_rfl, step_halt]

/-- The copy machine outputs its input unchanged, in `input.length + 1` steps and zero space. -/
theorem computesInTimeAndSpace (input : List Symbol) :
    ComputesInTimeAndSpace copy input input (input.length + 1) 0 :=
  ⟨by rw [runFrom_full]; rfl, by rw [runFrom_full]; simp [cfg],
    copy.spaceUsed_zero_tapes_eq_zero _ _ rfl⟩

end Copy

variable {α : Type*}

/-- The identity function is computable in one step per input symbol and zero space. -/
public theorem computableInTimeAndSpace_id {enc : α ↪ List Bool} :
    ComputableInTimeAndSpace (id : α → α) enc enc
      (fun a => (enc a).length + 1) (fun _ => 0) :=
  ⟨0, Unit, inferInstance, copy, fun a =>
    ⟨(enc a).length + 1, le_rfl, 0, le_rfl, Copy.computesInTimeAndSpace (enc a)⟩⟩

end Turing.MultiTapeTM
