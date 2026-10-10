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
  computable in zero space is computable *tidily*, with the time bound doubled and the space
  bound still zero.
-/

namespace Turing.MultiTapeTM

variable {Symbol : Type*} {input : List Symbol}

/-! ### Machines without work tapes compute tidily -/

/-- A machine without work tapes that halts in the words normal form except for its input head
computes tidily once the rewinding machine follows it. The hypothesis is the run of the machine
alone, which may leave the input head at any position `p`; the composite pays the `p - 1 + 2`
steps of the rewind on top. -/
public theorem computesTidily_seq_rewindInput_of_runFrom {State : Type*}
    {tm : MultiTapeTM 0 Symbol State} {output : List Symbol} {p : Fin (input.length + 2)}
    {tapes : Fin 0 → ℤ → Option Symbol} {heads : Fin 0 → ℤ} {t : ℕ}
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
      ⟨none, p, tapes, heads, output⟩) :
    (tm.seq (rewindInput Symbol)).ComputesTidilyInTimeAndSpace input output
      (t + (p.val - 1 + 2)) 0 := by
  refine computesTidily_of_runFrom ?_ (le_of_eq (spaceUsed_zero_tapes_eq_zero _ _ rfl))
  have hfin : (rewindInput Symbol).runFrom
      ⟨some (rewindInput Symbol).q₀, p, tapes, heads, output⟩ (p.val - 1 + 2) =
      wordsCfg input none (fun _ => []) output :=
    (runFrom_rewindInput p tapes heads output).trans (Cfg.ext_zero_tapes rfl rfl rfl)
  exact runFrom_seq hrun rfl hfin rfl

/-- **A machine without work tapes computes tidily** once the rewinding machine follows it. With
no work tape there is nothing to clean up: the one blemish of the halting configuration is the
input head, and it has had only `t` steps to stray from the start, so the rewind costs at most
`t + 2` further steps. -/
public theorem ComputesInTimeAndSpace.computesTidily_seq_rewindInput {State : Type*}
    {tm : MultiTapeTM 0 Symbol State} {output : List Symbol} {t s : ℕ}
    (h : ComputesInTimeAndSpace tm input output t s) :
    (tm.seq (rewindInput Symbol)).ComputesTidilyInTimeAndSpace input output (2 * t + 2) 0 := by
  obtain ⟨⟨u, hu_halt, hu_out⟩, htime, -⟩ := h
  have ht : (tm.runFrom (tm.initCfg input) t).Halted := runsInTime_iff_halted.mp htime
  -- Both `t` and `u` steps reach a halted configuration, so the outputs agree.
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
  have hone : ((tm.initCfg input).inputPos : ℕ) = 1 := by
    simp [Cfg.init]
  rw [hone] at hpos
  exact (computesTidily_seq_rewindInput_of_runFrom hrun).mono (by omega) le_rfl

/-! ### Zero space is tidy -/

/-- **A computation in zero space can be made tidy**: zero space forces a machine without work
tapes (`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_no_work_tapes`), and such a machine
leaves nothing behind but its input head, which a final rewind returns. The time bound doubles;
the space bound stays zero. -/
public theorem ComputableInTimeAndSpace.computableTidilyInTimeAndSpace {α β : Type*}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {t : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t (fun _ => 0)) :
    ComputableTidilyInTimeAndSpace f encIn encOut (fun a => 2 * t a + 2) (fun _ => 0) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨0, Unit, inferInstance, nop 0 Bool, fun a => (hα.false a).elim⟩
  · obtain ⟨State, hfin, tm, htm⟩ := h.exists_no_work_tapes
    exact ⟨0, State ⊕ RewindState, inferInstance, tm.seq (rewindInput Bool),
      fun a => (htm a).computesTidily_seq_rewindInput⟩

end Turing.MultiTapeTM
