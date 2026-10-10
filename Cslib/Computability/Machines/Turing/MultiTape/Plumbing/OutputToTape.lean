/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Redirecting the output to a work tape

`outputToTape tm` behaves like `tm`, except that whatever `tm` would append to the write-only
output tape is written on a fresh work tape instead, whose head always stands at the write
frontier.

Since the output is append-only, the frontier position is a *function of the configuration* —
the length of the output so far — so the redirected machine mirrors the original through the
configuration map `outCfg`. One step of the redirected machine mirrors the corresponding step of
`tm`, so `outCfgHom` maps every run path of `tm` to a run path of the redirected machine; the space
of the mapped path exceeds that of the original by at most the final output length plus one.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `tm`, with its output writes redirected onto a fresh last work tape, whose head always stands
at the write frontier. -/
@[expose] public noncomputable def outputToTape (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol State :=
  ofTr tm.q₀ fun q inp work =>
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
    rw [step_of_state (cfg := outCfg c) hq, step_of_state hq]
    simp only [outputToTape, tr_ofTr, outCfg_inputSymbol, outCfg_workTapeSymbols_castSucc]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases with
    | cast j => simp
    | last =>
      cases h : (tm.tr q c.inputSymbol c.workTapeSymbols).output <;>
        simp [h, tapeOfList_append_single, SignType.cast]

/-- The redirection preserves steps, so it maps run paths of `tm` to run paths of the redirected
machine. -/
@[expose, simps! apply] public noncomputable def outCfgHom (tm : MultiTapeTM k Symbol State) :
    (tm.stepRel input).Hom (tm.outputToTape.stepRel input) :=
  stepHom outCfg (step_outCfg tm)

/-- The initial configuration of the redirected machine is the original's through `outCfg`. -/
public lemma initCfg_outputToTape (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.outputToTape.initCfg input = outCfg (tm.initCfg input) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [MultiTapeNTM.initCfg, Cfg.init]

/-- **Space of the output-redirected path.** The `k` inner tapes visit exactly what the original
path visits, and the frontier head only walks up to the final length of the output, so the
redirection costs at most the final output length plus one. -/
public lemma space_map_outCfgHom_le (tm : MultiTapeTM k Symbol State) (p : tm.RunPath input) :
    (p.map (outCfgHom tm)).space ≤ p.space + (p.last.output.length + 1) := by
  simpa using p.space_map_le (outCfgHom tm) Fin.castSuccEmb (p.last.output.length + 1)
    (fun c _ j => outCfg_workTapePos_castSucc c j) fun l hl => by
      induction l using Fin.lastCases with
      | last =>
        refine (p.spaceUsedByTape_map_le_card _
          (S := .Icc 0 (p.last.output.length : ℤ)) ?_).trans (by simp)
        rintro _ ⟨n, rfl⟩
        have : (p n).output.length ≤ p.last.output.length := p.length_output_mono (Fin.le_last n)
        simp only [outCfgHom_apply, outCfg_workTapePos_last, Finset.mem_Icc]
        omega
      | cast j => exact absurd ⟨j, rfl⟩ hl

end Turing.MultiTapeTM
