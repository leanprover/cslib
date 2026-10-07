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
configuration map `outCfg`. `RunPath.outputToTape` transports a path through this map. The main
lemmas show that one step and an entire run of the redirected machine mirror the corresponding
step and run of `tm`.
-/

namespace Turing.MultiTapeNTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `tm`, with its output writes redirected onto a fresh last work tape, whose head always stands
at the write frontier. -/
@[expose] public def outputToTape (tm : MultiTapeNTM k Symbol State) :
    MultiTapeNTM (k + 1) Symbol State where
  q₀ := tm.q₀
  Tr q inp work b := ∃ a, tm.Tr q inp (fun j ↦ work j.castSucc) a ∧ b =
    { inputTape := a.inputTape
      workTapes := Fin.lastCases
        (match a.output with
          | none => (none, 0)
          | some s => (some (some s), 1))
        a.workTapes
      output := none
      state := a.state }

/-- Redirecting the output preserves determinism. -/
public lemma IsDeterministic.outputToTape {tm : MultiTapeNTM k Symbol State}
    (h : tm.IsDeterministic) : tm.outputToTape.IsDeterministic := by
  intro q inp work
  obtain ⟨a, ha, hu⟩ := h q inp (fun j ↦ work j.castSucc)
  refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
  rintro b ⟨a', ha', rfl⟩
  rw [hu a' ha']

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

/-- The redirection preserves steps. `RunPath.outputToTape` transports the whole path. -/
public lemma step_outCfg (tm : MultiTapeNTM k Symbol State)
    {c c' : Cfg k Symbol State input} (h : tm.Step c c') :
    tm.outputToTape.Step (outCfg c) (outCfg c') := by
  cases hq : c.state with
  | none =>
    obtain rfl := (step_of_halt hq).mp h
    exact (step_of_halt (c := outCfg c') hq).mpr rfl
  | some q =>
    obtain ⟨a, ha, rfl⟩ := (step_of_state hq).mp h
    refine (step_of_state (c := outCfg c) hq).mpr
      ⟨_, ⟨a, by simpa using ha, rfl⟩, ?_⟩
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases with
    | cast j => simp
    | last => cases ha : a.output <;> simp [ha, tapeOfList_append_single, SignType.cast]

/-- A path with its output redirected to the last work tape. -/
@[expose] public def RunPath.outputToTape {tm : MultiTapeNTM k Symbol State}
    (p : tm.RunPath input) : tm.outputToTape.RunPath input :=
  p.map ⟨outCfg, step_outCfg tm⟩

/-- `outputToTape tm` never writes the real output, so replacing it preserves the step relation. -/
public lemma step_outputToTape_withOutput (tm : MultiTapeNTM k Symbol State)
    {c c' : Cfg (k + 1) Symbol State input} (h : tm.outputToTape.Step c c') (out : List Symbol) :
    tm.outputToTape.Step (c.withOutput out) (c'.withOutput out) := by
  cases hq : c.state with
  | none =>
    obtain rfl := (step_of_halt hq).mp h
    exact (step_of_halt (c := c'.withOutput out) hq).mpr rfl
  | some q =>
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := (step_of_state hq).mp h
    refine (step_of_state (c := c.withOutput out) hq).mpr ⟨_, ⟨a, ha, rfl⟩, ?_⟩
    exact Cfg.ext rfl rfl rfl rfl (by simp)

/-- Replace the real output along a path of `outputToTape tm`, which never writes to it. -/
@[expose] public def RunPath.withOutput {tm : MultiTapeNTM k Symbol State}
    (p : tm.outputToTape.RunPath input) (out : List Symbol) : tm.outputToTape.RunPath input :=
  p.map ⟨(Cfg.withOutput · out), (step_outputToTape_withOutput tm · out)⟩

/-- `outputToTape`'s space does not depend on the real output already present. -/
public lemma RunPath.space_withOutput {tm : MultiTapeNTM k Symbol State}
    (p : tm.outputToTape.RunPath input) (out : List Symbol) :
    (p.withOutput out).space = p.space :=
  p.space_map_eq _ fun _ _ ↦ rfl

/-- The initial configuration of the redirected machine is the original's through `outCfg`. -/
public lemma initCfg_outputToTape (tm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    tm.outputToTape.initCfg input = outCfg (tm.initCfg input) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [MultiTapeNTM.initCfg, Cfg.init]

/-- **Space of the output-redirected machine.** The `k` inner tapes visit exactly what the original
does, and the frontier head only walks between the initial and the final length of the output, so
the redirection costs at most the final output length plus one. -/
public lemma RunPath.space_outputToTape_le {tm : MultiTapeNTM k Symbol State}
    (p : tm.RunPath input) :
    p.outputToTape.space ≤ p.space + (p.last.output.length + 1) := by
  simpa [RunPath.outputToTape] using p.space_map_le ⟨outCfg, step_outCfg tm⟩ Fin.castSuccEmb
    (p.last.output.length + 1) (fun _ _ _ ↦ by simp) fun l hl ↦ by
      induction l using Fin.lastCases with
      | cast j => exact absurd ⟨j, rfl⟩ hl
      | last =>
        refine (RunPath.spaceUsedByTape_le_card _
          (S := .Icc (p.head.output.length : ℤ) p.last.output.length) ?_).trans (by simp)
        rintro _ ⟨n, rfl⟩
        change (outCfg (p n)).workTapePos (Fin.last k) ∈ _
        rw [outCfg_workTapePos_last, Finset.mem_Icc]
        have h0 := p.length_output_mono (Fin.zero_le n)
        have h1 := p.length_output_mono (Fin.le_last n)
        exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

end Turing.MultiTapeNTM
