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
    | some b => { inputTape := 1, workTapes := fun i => i.elim0, output := some b,
                  state := some () }
    | none => { inputTape := 0, workTapes := fun i => i.elim0, output := none, state := none }

namespace Copy

/-- A configuration of the copy machine, given by the input, the control state, the input head
position and the output written so far. There are no work tapes. `input` is explicit because it is
inferable only through the expected type: the head position is written as an anonymous
constructor, which pins nothing. -/
def cfg (input : List Symbol) (q : Option Unit) (p : Fin (input.length + 2))
    (out : List Symbol) : Cfg 0 Symbol Unit input :=
  ⟨q, p, fun _ _ => none, fun _ => 0, out⟩

/-- With no work tapes, configurations are equal as soon as the state, the input position and the
output agree. -/
lemma cfg_ext {c₁ c₂ : Cfg 0 Symbol Unit input} (hstate : c₁.state = c₂.state)
    (hpos : c₁.inputPos = c₂.inputPos) (hout : c₁.output = c₂.output) : c₁ = c₂ :=
  Cfg.ext hstate hpos (funext fun i => i.elim0) (funext fun i => i.elim0) hout

/-- Over an input symbol, the copy machine emits it and moves right. -/
lemma step_scan {n : ℕ} (hn : n < input.length) (out : List Symbol) :
    copy.step (cfg input (some ()) ⟨n + 1, by omega⟩ out) =
      cfg input (some ()) ⟨n + 2, by omega⟩ (out ++ [input[n]]) := by
  have hsym : (cfg input (some ()) ⟨n + 1, by omega⟩ out).inputSymbol =
      some input[n] := inputSymbolInner n (by simp only [cfg]; omega) hn
  unfold step
  simp only [cfg] at hsym ⊢
  rw [hsym]
  refine cfg_ext rfl ?_ rfl
  apply Fin.ext
  simp [copy, Action.apply, moveInputPos]
  grind

/-- On the blank at the right end of the input, the copy machine halts in place. -/
lemma step_halt (out : List Symbol) :
    copy.step (cfg input (some ()) ⟨input.length + 1, by omega⟩ out) =
      cfg input none ⟨input.length + 1, by omega⟩ out := by
  have hsym : (cfg input (some ()) ⟨input.length + 1, by omega⟩ out).inputSymbol =
      none :=
    inputSymbol_eq_none_of_boundary (Or.inr rfl)
  unfold step
  simp only [cfg] at hsym ⊢
  rw [hsym]
  exact cfg_ext rfl (by simp [copy, Action.apply]) (by simp [copy, Action.apply])

/-- After `n ≤ input.length` steps, the copy machine has copied the first `n` input symbols to the
output and its head is over the `n`-th cell of the input. -/
lemma runFrom_scan (n : ℕ) (hn : n ≤ input.length) :
    copy.runFrom (copy.initCfg input) n =
      cfg input (some ()) ⟨n + 1, by omega⟩ (input.take n) := by
  induction n with
  | zero => exact cfg_ext rfl rfl rfl
  | succ n ih =>
    rw [runFrom_succ_eq_step', ih (by omega), step_scan (by omega)]
    have htake : input.take n ++ [input[n]] = input.take (n + 1) := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
    rw [htake]

/-- The complete run: after `input.length + 1` steps the copy machine has halted with the input
copied to the output. -/
lemma runFrom_full (input : List Symbol) :
    copy.runFrom (copy.initCfg input) (input.length + 1) =
      cfg input none ⟨input.length + 1, by omega⟩ input := by
  rw [runFrom_succ_eq_step', runFrom_scan input.length le_rfl, List.take_length, step_halt]

/-- The copy machine outputs its input unchanged, in `input.length + 1` steps and zero space. -/
theorem computesInTimeAndSpace (input : List Symbol) :
    ComputesInTimeAndSpace copy input input (input.length + 1) 0 :=
  ⟨by rw [runFrom_full]; rfl, by rw [runFrom_full]; rfl,
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
