/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy

/-!
# Writing the output as a word on a work tape

`outputToWord tm` runs `tm` with its output redirected onto a new last work tape
(`Turing.MultiTapeTM.outputToTape`), then moves the head of that tape back to cell `0`
(`Turing.MultiTapeTM.rewindWork`).

If `tm` computes `output` tidily (`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`), then
`outputToWord tm` takes blank work tapes to blank work tapes, except that the last one holds
`output`, and emits nothing.

## Main results

* `Turing.MultiTapeTM.outputToWord`: the composed machine.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.outputToWord`: its specification.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `tm` with its output written to a new last work tape, whose head is then moved back to
cell `0`. -/
noncomputable def outputToWord (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol (State ⊕ RewindWorkState) :=
  tm.outputToTape.seq ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k)))

/-- Redirecting the output of a blank `wordsCfg` configuration adds a blank last work tape. -/
lemma outCfg_wordsCfg (q : Option State) :
    outCfg (wordsCfg input q (fun _ : Fin k => []) []) = wordsCfg input q (fun _ => []) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [outCfg, wordsCfg]

/-- The last work tape of `outCfg (wordsCfg input q ws out)`, as a one-tape configuration: it holds
`out`, with its head at the end of `out`. -/
lemma oneTapeCfg_outCfg_wordsCfg (q : Option State) (ws : Fin k → List Symbol)
    (out : List Symbol) :
    oneTapeCfg (Fin.last k) (outCfg (wordsCfg input q ws out)) =
      ⟨q, 1, fun _ => tapeOfList out, fun _ => (out.length : ℤ), []⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg]

open Sequential in
/-- If `tm` computes `output` tidily, then `outputToWord tm`, started on blank work tapes, halts
with `output` on its last work tape, every other work tape blank, and nothing emitted. -/
theorem ComputesTidilyInTimeAndSpace.outputToWord {tm : MultiTapeTM k Symbol State}
    {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    TransformsTapes tm.outputToWord
      (fun inp ws => inp = input ∧ ws = fun _ => [])
      (fun _ _ ws' e => ws' = Function.update (fun _ => []) (Fin.last k) output ∧ e = [])
      (t + output.length + 2) (s + 2 * output.length + k + 3) := by
  obtain ⟨hrun, hspace⟩ := computesTidily_iff.mp h
  rw [transformsTapes_iff_nil_output]
  rintro inp _ ⟨hin, rfl⟩
  subst inp
  -- phase 1: `outputToTape` mirrors `tm` through `outCfg`
  have hphase1 : tm.outputToTape.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
      outCfg (wordsCfg input none (fun _ => []) output) := by
    rw [← outCfg_wordsCfg, runFrom_outCfg, hrun]
  -- phase 2: rewind the head of the last tape from the end of `output` to cell `0`
  have hphase2 : ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).runFrom
      (outCfg (wordsCfg input (some (rewindWork Symbol).q₀) (fun _ => []) output))
      (output.length + 2) =
        wordsCfg input none (Function.update (fun _ => []) (Fin.last k) output) [] := by
    rw [runFrom_tapeEmb, oneTapeCfg_outCfg_wordsCfg, runFrom_rewindWork_none _ _ _ rfl le_rfl,
      embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
      simp [wordsCfg]
  rw [add_assoc t]
  refine ⟨_, [], runFrom_seq hphase1 rfl hphase2 rfl, ⟨rfl, rfl⟩, ?_⟩
  -- phase 1 costs `s + output.length + 1`, phase 2 costs `output.length + 2 + k`
  have h₁ := spaceUsed_outputToTape tm (wordsCfg input (some tm.q₀) (fun _ => []) []) t
  have h₂ := spaceUsed_tapeEmb_le (rewindWork Symbol) (Fin.last k)
    (outCfg (wordsCfg input (some (rewindWork Symbol).q₀) (fun _ => []) output)) (output.length + 2)
  have h₃ := spaceUsed_rewindWork_le (input := input) none 1 (tapeOfList output) [] rfl le_rfl
    (output.length + 2)
  rw [outCfg_wordsCfg, hrun, wordsCfg_output] at h₁
  rw [oneTapeCfg_outCfg_wordsCfg] at h₂
  exact (spaceUsed_seq_le hphase1 rfl (congrArg Cfg.state hphase2)).trans
    ((Nat.add_le_add h₁ h₂).trans (by omega))

end Turing.MultiTapeTM
