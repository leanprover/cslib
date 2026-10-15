/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Basic.Finite.Sum
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs

/-!
# Tidiness is free at zero space

A machine that runs in zero space has no work tapes
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_no_work_tapes`), so the only part of its
final configuration that can differ from the start is the input head. Following it with
`Turing.MultiTapeTM.rewindInput` moves that head back, which makes the computation tidy in the
sense of `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`.

## Main results

* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInTimeAndSpace`: a function
  computable in time `t` and zero space is computable tidily in time `2 * t + 2` and zero space.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-! ### Machines without work tapes -/

section NoWorkTapes

variable {State : Type*} {tm : MultiTapeTM 0 Symbol State}

open Sequential in
/-- If a machine without work tapes has a run path from its start to a halted configuration, then
following it with `Turing.MultiTapeTM.rewindInput` computes the output of that configuration
tidily: the rewind returns the input head from its position `p` in `p - 1 + 2` further steps. -/
public theorem computesTidily_seq_rewindInput_of_runPath {q : tm.RunPath input}
    (hh : q.head = wordsCfg input (some tm.q₀) (fun _ => []) []) (hl : q.last.Halted) :
    (tm.seq (rewindInput Symbol)).ComputesTidilyInTimeAndSpace input q.last.output
      (q.time + (q.last.inputPos.val - 1 + 2)) 0 := by
  let r := MultiTapeNTM.RunPath.ofDeterministic (rewindInput Symbol)
    (q.last.withState (some (rewindInput Symbol).q₀)) (q.last.inputPos.val - 1 + 2)
  have hr : r.last = wordsCfg input none (fun _ => []) q.last.output :=
    (runFrom_rewindInput q.last.inputPos q.last.workTapes q.last.workTapePos q.last.output).trans
      (Cfg.ext_zero_tapes rfl rfl rfl)
  obtain ⟨p, hph, hpl, hpt, -⟩ := exists_runPath_seq hl rfl (by rw [hr]; rfl)
  exact computesTidily_iff.mpr ⟨p, by rw [hph, hh]; rfl, by simp [hpl, hr, rightCfg], hpt,
    by simp [MultiTapeNTM.RunPath.space]⟩

/-- A machine without work tapes that computes `output` in time `t`, followed by
`Turing.MultiTapeTM.rewindInput`, computes `output` tidily in time `2 * t + 2`: in `t` steps the
input head moves at most `t` cells, so the rewind takes at most `t + 2` steps. -/
public theorem ComputesInTimeAndSpace.computesTidily_seq_rewindInput {output : List Symbol}
    {t s : ℕ} (h : ComputesInTimeAndSpace tm input output t s) :
    (tm.seq (rewindInput Symbol)).ComputesTidilyInTimeAndSpace input output (2 * t + 2) 0 := by
  obtain ⟨⟨u, hu_halt, hu_out⟩, htime, -⟩ := h
  -- the computation path of `t` steps ends halted
  let q := MultiTapeNTM.ComputationPath.ofDeterministic tm input t
  have hl : q.last.Halted := htime q le_rfl
  -- the machine has halted after both `t` and `u` steps, so the outputs agree
  have hout : q.last.output = output := by
    change (tm.runFrom (tm.initCfg input) t).output = output
    rcases le_total u t with hut | htu
    · rw [runFrom_eq_of_halt _ _ hut hu_halt, hu_out]
    · rw [← runFrom_eq_of_halt _ _ htu hl, hu_out]
  have hpos : q.last.inputPos.val ≤ 1 + t := by
    change ((tm.runFrom (tm.initCfg input) t).inputPos : ℕ) ≤ 1 + t
    simpa [Cfg.init] using inputPos_runFrom_le tm (tm.initCfg input) t
  have h := computesTidily_seq_rewindInput_of_runPath (q := q.toRunPath)
    (q.head_eq.trans (Cfg.init_eq_wordsCfg _ _)) hl
  rw [hout] at h
  exact h.mono (by change t + _ ≤ _; omega) le_rfl

end NoWorkTapes

/-! ### Zero space -/

/-- A function computable in time `t` and zero space is computable tidily in time `2 * t + 2` and
zero space: the machine has no work tapes, so it suffices to rewind the input head. -/
public theorem ComputableInTimeAndSpace.computableTidilyInTimeAndSpace {α β : Type*}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {t : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t (fun _ => 0)) :
    ComputableTidilyInTimeAndSpace f encIn encOut (fun a => 2 * t a + 2) (fun _ => 0) := by
  rcases isEmpty_or_nonempty α with _ | _
  · exact ⟨0, Unit, inferInstance, nop 0 Bool, isEmptyElim⟩
  · obtain ⟨State, hfin, tm, htm⟩ := h.exists_no_work_tapes
    exact ⟨0, State ⊕ RewindState, inferInstance, tm.seq (rewindInput Bool),
      fun a => (htm a).computesTidily_seq_rewindInput⟩

end Turing.MultiTapeTM
