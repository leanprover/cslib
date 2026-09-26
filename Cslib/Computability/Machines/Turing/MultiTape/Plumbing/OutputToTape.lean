/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Redirecting the output to a work tape

`outputToTape tm` behaves like `tm`, except that whatever `tm` would append to the write-only
output tape is written on a fresh work tape instead, whose head always stands at the write
frontier.

Since the output is append-only, the frontier position is a *function of the configuration* —
the length of the output so far — so the redirected machine mirrors the original through the
configuration map `outCfg`. The main lemmas show that one step and an entire run of the redirected
machine mirror the corresponding step and run of `tm`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `tm`, with its output writes redirected onto a fresh last work tape, whose head always stands
at the write frontier. -/
@[expose] public def outputToTape (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol State where
  q₀ := tm.q₀
  tr q inp work :=
    let a := tm.tr q inp fun j => work j.castSucc
    { inputTape := a.inputTape
      workTapes := Fin.lastCases
        (match a.output with
          | none => (none, 0)
          | some s => (some (some s), 1))
        (fun j => a.workTapes j)
      output := none
      state := a.state }

/-- A configuration of `tm`, as the redirected machine sees it: the output so far sits on the
last work tape with the head at its end, and the real output is empty. -/
@[expose] public def outCfg (c : Cfg k Symbol State input) :
    Cfg (k + 1) Symbol State input :=
  ⟨c.state, c.inputPos,
    Fin.lastCases (tapeOfList c.output) (fun j => c.workTapes j),
    Fin.lastCases (c.output.length : ℤ) (fun j => c.workTapePos j),
    []⟩

@[simp]
public lemma outCfg_inputSymbol (c : Cfg k Symbol State input) :
    (outCfg c).inputSymbol = c.inputSymbol := rfl

@[simp]
public lemma outCfg_workTapes_last (c : Cfg k Symbol State input) :
    (outCfg c).workTapes (Fin.last k) = tapeOfList c.output := by
  simp [outCfg]

@[simp]
public lemma outCfg_workTapes_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapes j.castSucc = c.workTapes j := by
  simp [outCfg]

@[simp]
public lemma outCfg_workTapePos_last (c : Cfg k Symbol State input) :
    (outCfg c).workTapePos (Fin.last k) = (c.output.length : ℤ) := by
  simp [outCfg]

@[simp]
public lemma outCfg_workTapePos_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapePos j.castSucc = c.workTapePos j := by
  simp [outCfg]

@[simp]
public lemma outCfg_workTapeSymbols_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapeSymbols j.castSucc = c.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- The redirection is a step-semiconjugation. -/
public lemma step_outCfg (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input) :
    tm.outputToTape.step (outCfg c) = outCfg (tm.step c) := by
  cases hq : c.state with
  | none => simp [outCfg, hq]
  | some q =>
    rw [step_apply_of_state (cfg := outCfg c) hq, step_apply_of_state hq]
    simp only [outputToTape, outCfg_inputSymbol, outCfg_workTapeSymbols_castSucc]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
      cases h : (tm.tr q c.inputSymbol c.workTapeSymbols).output <;>
      simp [h, tapeOfList_append_single, SignType.cast]

/-- The redirected run mirrors the original. -/
public lemma runFrom_outCfg (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input)
    (n : ℕ) :
    tm.outputToTape.runFrom (outCfg c) n = outCfg (tm.runFrom c n) :=
  runFrom_comm (step_outCfg tm) c n

section WithOutput

/-- `outputToTape tm` never writes the real output, so replacing it commutes with a step. -/
public lemma step_outputToTape_withOutput (tm : MultiTapeTM k Symbol State)
    (c : Cfg (k + 1) Symbol State input) (out : List Symbol) :
    tm.outputToTape.step (c.withOutput out) = (tm.outputToTape.step c).withOutput out := by
  cases hq : c.state with
  | none => simp [hq]
  | some q =>
    rw [step_apply_of_state (cfg := c.withOutput out) hq, step_apply_of_state hq]
    exact Cfg.ext rfl rfl rfl rfl (by simp [outputToTape])

/-- The redirected run commutes with the real output already present. -/
public lemma runFrom_outputToTape_withOutput (tm : MultiTapeTM k Symbol State)
    (c : Cfg (k + 1) Symbol State input) (out : List Symbol) (n : ℕ) :
    tm.outputToTape.runFrom (c.withOutput out) n = (tm.outputToTape.runFrom c n).withOutput out :=
  runFrom_comm (step_outputToTape_withOutput tm · out) c n

/-- `outputToTape`'s space does not depend on the real output already present. -/
public lemma spaceUsed_outputToTape_withOutput (tm : MultiTapeTM k Symbol State)
    (c : Cfg (k + 1) Symbol State input) (out : List Symbol) (u : ℕ) :
    tm.outputToTape.spaceUsed (c.withOutput out) u = tm.outputToTape.spaceUsed c u := by
  refine spaceUsed_eq_of_workTapePos _ _ u fun m hm => ?_
  rw [runFrom_outputToTape_withOutput]; rfl

end WithOutput

/-- The initial configuration of the redirected machine is the original's through `outCfg`. -/
public lemma initCfg_outputToTape (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.outputToTape.initCfg input = outCfg (tm.initCfg input) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [initCfg, Cfg.init]

/-- **Space of the output-redirected machine.** The `k` inner tapes visit exactly what the original
does, and the frontier head only walks between the initial and the final length of the output, so
the redirection costs at most the final output length plus one. -/
public lemma spaceUsed_outputToTape (tm : MultiTapeTM k Symbol State)
    (c : Cfg k Symbol State input) (u : ℕ) :
    tm.outputToTape.spaceUsed (outCfg c) u ≤
      tm.spaceUsed c u + ((tm.runFrom c u).output.length + 1) := by
  simpa using spaceUsed_le_of_workTapePos_embedding (tm := tm) Fin.castSuccEmb c (outCfg c)
    ((tm.runFrom c u).output.length + 1) (fun m _ j => by simp [runFrom_outCfg])
    fun l hl => by
      induction l using Fin.lastCases with
      | last =>
        refine (spaceUsedByTape_le_card _
          (S := .Icc (c.output.length : ℤ) (tm.runFrom c u).output.length) fun m hm => ?_).trans
          (by simp)
        have h0 : c.output.length ≤ (tm.runFrom c m).output.length :=
          tm.length_output_mono c (Nat.zero_le m)
        have hu : (tm.runFrom c m).output.length ≤ (tm.runFrom c u).output.length :=
          tm.length_output_mono c hm
        simp only [runFrom_outCfg, outCfg_workTapePos_last, Finset.mem_Icc]
        omega
      | cast j => exact absurd ⟨j, rfl⟩ hl

end Turing.MultiTapeTM
