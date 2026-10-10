/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Basic.Finite.Sum
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy

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

/-- If a machine without work tapes halts with output `output` and its input head at `p`, then
following it with `Turing.MultiTapeTM.rewindInput` computes `output` tidily, with `p - 1 + 2`
extra steps for the rewind. -/
public theorem computesTidily_seq_rewindInput_of_runFrom {State : Type*}
    {tm : MultiTapeTM 0 Symbol State} {output : List Symbol} {p : Fin (input.length + 2)}
    {tapes : Fin 0 → ℤ → Option Symbol} {heads : Fin 0 → ℤ} {t : ℕ}
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
      ⟨none, p, tapes, heads, output⟩) :
    (tm.seq (rewindInput Symbol)).ComputesTidilyInTimeAndSpace input output
      (t + (p.val - 1 + 2)) 0 := by
  refine computesTidily_iff.mpr ⟨?_, (spaceUsed_zero_tapes_eq_zero _ _ rfl).le⟩
  have hfin : (rewindInput Symbol).runFrom
      ⟨some (rewindInput Symbol).q₀, p, tapes, heads, output⟩ (p.val - 1 + 2) =
      wordsCfg input none (fun _ => []) output :=
    (runFrom_rewindInput p tapes heads output).trans (Cfg.ext_zero_tapes rfl rfl rfl)
  exact runFrom_seq hrun rfl hfin rfl

/-- A machine without work tapes that computes `output` in time `t`, followed by
`Turing.MultiTapeTM.rewindInput`, computes `output` tidily in time `2 * t + 2`: in `t` steps the
input head moves at most `t` cells, so the rewind takes at most `t + 2` steps. -/
public theorem ComputesInTimeAndSpace.computesTidily_seq_rewindInput {State : Type*}
    {tm : MultiTapeTM 0 Symbol State} {output : List Symbol} {t s : ℕ}
    (h : ComputesInTimeAndSpace tm input output t s) :
    (tm.seq (rewindInput Symbol)).ComputesTidilyInTimeAndSpace input output (2 * t + 2) 0 := by
  obtain ⟨⟨u, hu_halt, hu_out⟩, htime, -⟩ := h
  have ht : (tm.runFrom (tm.initCfg input) t).Halted := runsInTime_iff_halted.mp htime
  -- the machine has halted after both `t` and `u` steps, so the outputs agree
  have hout : (tm.runFrom (tm.initCfg input) t).output = output := by
    obtain ⟨v, hvt, hv⟩ := exists_haltsAt ht
    rw [hv.runFrom_eq hvt, ← hu_out, hv.runFrom_eq (hv.le_of_halted hu_halt)]
  have hrun : tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
      ⟨none, (tm.runFrom (tm.initCfg input) t).inputPos,
        (tm.runFrom (tm.initCfg input) t).workTapes,
        (tm.runFrom (tm.initCfg input) t).workTapePos, output⟩ := by
    rw [← Cfg.init_eq_wordsCfg]
    exact Cfg.ext_zero_tapes ht rfl hout
  have hpos := inputPos_runFrom_le tm (tm.initCfg input) t
  have hone : ((tm.initCfg input).inputPos : ℕ) = 1 := by simp [Cfg.init]
  exact (computesTidily_seq_rewindInput_of_runFrom hrun).mono (by omega) le_rfl

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
