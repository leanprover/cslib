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

`ntm.outputToTape` behaves like `ntm`, except that whatever `ntm` would append to the write-only
output tape is written on a fresh work tape instead, whose head always stands at the write
frontier.

Since the output is append-only, the frontier position is a *function of the configuration* —
the length of the output so far — so the redirected machine mirrors the original through the
configuration map `outCfg`. The main lemmas show that one step and an entire run path of the
redirected machine mirror the corresponding step and run path of `ntm`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `ntm`, with its output writes redirected onto a fresh last work tape, whose head always stands
at the write frontier. -/
@[expose] public def _root_.Turing.MultiTapeNTM.outputToTape (ntm : MultiTapeNTM k Symbol State) :
    MultiTapeNTM (k + 1) Symbol State :=
  ntm.adapt (fun inp _ => inp) (fun work j => work j.castSucc) fun _ a =>
    { a with
      workTapes := Fin.lastCases
        (match a.output with
          | none => (none, 0)
          | some s => (some (some s), 1))
        a.workTapes
      output := none }

/-- The deterministic machine `tm` with its output redirected onto a fresh last work tape. -/
public abbrev outputToTape (tm : MultiTapeTM k Symbol State) : MultiTapeTM (k + 1) Symbol State :=
  ⟨tm.toMultiTapeNTM.outputToTape, tm.deterministic.adapt⟩

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

/-- The redirection preserves steps, so it maps run paths of `ntm` to run paths of the redirected
machine. -/
@[expose, simps! apply] public def _root_.Turing.MultiTapeNTM.outCfgHom
    (ntm : MultiTapeNTM k Symbol State) :
    (ntm.stepRel input).Hom (ntm.outputToTape.stepRel input) :=
  MultiTapeNTM.adaptHom outCfg (fun _ => rfl) (fun _ => rfl)
    (fun c => funext (outCfg_workTapeSymbols_castSucc c)) fun c a => by
      refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases with
      | cast j => simp [Action.apply]
      | last =>
        cases h : a.output <;> simp [h, Action.apply, tapeOfList_append_single, SignType.cast]

/-- The initial configuration of the redirected machine is the original's through `outCfg`. -/
public lemma _root_.Turing.MultiTapeNTM.initCfg_outputToTape (ntm : MultiTapeNTM k Symbol State)
    (input : List Symbol) : ntm.outputToTape.initCfg input = outCfg (ntm.initCfg input) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [MultiTapeNTM.initCfg, Cfg.init]

/-- **Space of the output-redirected path.** The `k` inner tapes visit exactly what the original
path visits, and the frontier head only walks up to the final length of the output, so the
redirection costs at most the final output length plus one. -/
public lemma _root_.Turing.MultiTapeNTM.space_map_outCfgHom_le (ntm : MultiTapeNTM k Symbol State)
    (p : ntm.RunPath input) :
    (p.map ntm.outCfgHom).space ≤ p.space + (p.last.output.length + 1) := by
  simpa [Finset.card_compl] using p.space_map_le _ Fin.castSuccEmb
    (fun _ => .Icc 0 (p.last.output.length : ℤ)) (fun c _ => outCfg_workTapePos_castSucc c)
    fun c ⟨n, hn⟩ l hl => by
      induction l using Fin.lastCases with
      | last =>
        have : c.output.length ≤ p.last.output.length := hn ▸ p.length_output_mono (Fin.le_last n)
        simpa using this
      | cast j => exact absurd ⟨j, rfl⟩ hl

end Turing.MultiTapeTM
