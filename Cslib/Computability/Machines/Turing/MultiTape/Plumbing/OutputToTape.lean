/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Redirecting the output to a work tape

`outputToTape tm` behaves like `tm`, except that whatever `tm` would append to the write-only
output tape is written on a fresh work tape instead, whose head always stands at the write
frontier.

Since the output is append-only, the frontier position is a *function of the configuration* —
the length of the output so far — so the redirected machine mirrors the original through the
configuration map `outCfg`. The main lemmas show that one step and an entire run path of the
redirected machine mirror the corresponding step and run path of `tm`.

`outputToWord tm` then moves the head of the new work tape back to cell `0`
(`Turing.MultiTapeTM.rewindWork`). If `tm` computes `output` tidily
(`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`), then `outputToWord tm` takes blank work tapes
to blank work tapes, except that the last one holds `output`, and emits nothing.

## Main definitions

* `Turing.MultiTapeTM.outputToTape`: the machine writing its output to a work tape.
* `Turing.MultiTapeTM.outCfgHom`: the configuration map `outCfg` as a step-preserving map, which
  maps run paths.
* `Turing.MultiTapeTM.outputToWord`: the machine writing its output as a word on a work tape.

## Main results

* `Turing.MultiTapeTM.step_outCfg`: one step of the redirected machine mirrors one step of `tm`.
* `Turing.MultiTapeTM.space_map_outCfgHom_le`: the space bound for a redirected path.
*`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.outputToWord`: its specification.
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
public lemma step_outCfg (tm : MultiTapeTM k Symbol State) :
    Function.Semiconj (outCfg (input := input)) tm.step tm.outputToTape.step := by
  intro c
  symm
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
  simpa [Finset.card_compl] using p.space_map_le _ Fin.castSuccEmb
    (fun _ => .Icc 0 (p.last.output.length : ℤ)) (fun c _ => outCfg_workTapePos_castSucc c)
    fun c ⟨n, hn⟩ l hl => by
      induction l using Fin.lastCases with
      | last =>
        have : c.output.length ≤ p.last.output.length := hn ▸ p.length_output_mono (Fin.le_last n)
        simpa using this
      | cast j => exact absurd ⟨j, rfl⟩ hl

/-! ### Rewinding the output tape -/

/-- `tm` with its output written to a new last work tape, whose head is then moved back to
cell `0`. -/
@[expose] public noncomputable def outputToWord (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol (State ⊕ RewindWorkState) :=
  tm.outputToTape.seq ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k)))

/-- Redirecting the output of a blank `wordsCfg` configuration adds a blank last work tape. -/
private lemma outCfg_wordsCfg (q : Option State) :
    outCfg (wordsCfg input q (fun _ : Fin k => []) []) = wordsCfg input q (fun _ => []) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [outCfg, wordsCfg]

/-- The last work tape of `outCfg (wordsCfg input q ws out)`, as a one-tape configuration: it holds
`out`, with its head at the end of `out`. -/
private lemma oneTapeCfg_outCfg_wordsCfg (q : Option State) (ws : Fin k → List Symbol)
    (out : List Symbol) :
    oneTapeCfg (Fin.last k) (outCfg (wordsCfg input q ws out)) =
      ⟨q, 1, fun _ => tapeOfList out, fun _ => (out.length : ℤ), []⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg]

/-- Rewinding the last work tape of `outCfg (wordsCfg input q (fun _ => []) out)` takes
`out.length + 2` steps and leaves `out` as a word on that tape: it runs `rewindWork` on that tape.
-/
private lemma exists_runPath_rewindLast (out : List Symbol) :
    ∃ p : ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).RunPath input,
      p.head = outCfg (wordsCfg input (some (rewindWork Symbol).q₀) (fun _ : Fin k => []) out) ∧
      p.last = wordsCfg input none (Function.update (fun _ => []) (Fin.last k) out) [] ∧
      p.time = out.length + 2 ∧ p.space ≤ out.length + k + 3 := by
  let cfg := outCfg (wordsCfg input (some (rewindWork Symbol).q₀) (fun _ : Fin k => []) out)
  let r := MultiTapeNTM.RunPath.ofDeterministic (rewindWork Symbol) (oneTapeCfg (Fin.last k) cfg)
    (out.length + 2)
  refine ⟨r.map (embedHom _ (tapeEmb (Fin.last k)) cfg.workTapes cfg.workTapePos),
    embed_oneTapeCfg _ cfg, ?_, rfl, ?_⟩
  · change embed _ ((rewindWork Symbol).runFrom (oneTapeCfg _ cfg) (out.length + 2)) _ _ = _
    rw [oneTapeCfg_outCfg_wordsCfg, runFrom_rewindWork_none _ _ _ rfl le_rfl, embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
      simp [cfg, wordsCfg]
  · -- the rewind takes `out.length + 2` steps on one tape, every other tape stays where it is
    have : r.space ≤ 1 * (out.length + 2 + 1) := r.space_le_mul_time_add_one
    exact (space_map_embedHom_le ..).trans (by omega)

open Sequential in
/-- If `tm` computes `output` tidily, then `outputToWord tm`, started on blank work tapes, halts
with `output` on its last work tape, every other work tape blank, and nothing emitted. -/
public theorem ComputesTidilyInTimeAndSpace.outputToWord {tm : MultiTapeTM k Symbol State}
    {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    TransformsTapes tm.outputToWord
      (fun inp ws => inp = input ∧ ws = fun _ => [])
      (fun _ _ ws' e => ws' = Function.update (fun _ => []) (Fin.last k) output ∧ e = [])
      (t + output.length + 2) (s + 2 * output.length + k + 4) := by
  obtain ⟨p, hh, hl, ht, hs⟩ := computesTidily_iff.mp h
  unfold MultiTapeTM.outputToWord
  rw [transformsTapes_iff_nil_output]
  rintro inp _ ⟨hin, rfl⟩
  subst inp
  -- run `tm` with its output on the last work tape, then rewind that tape
  let p₀ := p.map (outCfgHom tm)
  have hl₀ : p₀.last = outCfg (wordsCfg input none (fun _ => []) output) := by simp [p₀, hl]
  have hs₀ : p₀.space ≤ p.space + (output.length + 1) := by
    simpa [hl] using space_map_outCfgHom_le tm p
  obtain ⟨p₁, hh₁, hl₁, ht₁, hs₁⟩ := exists_runPath_rewindLast (k := k) (input := input) output
  obtain ⟨q, hqh, hql, hqt, hqs⟩ := exists_runPath_seq_space_le (p₀ := p₀) (p₁ := p₁)
    (by rw [hl₀]; rfl) (by rw [hh₁, hl₀]; rfl) (by rw [hl₁]; rfl)
  refine ⟨_, [], ⟨rfl, rfl⟩, q, ?_, by simp [hql, hl₁, rightCfg], ?_, by omega⟩
  · simp only [hqh, p₀, RelSeries.head_map, outCfgHom_apply, hh, outCfg_wordsCfg]
    rfl
  · simp only [MultiTapeNTM.RunPath.time] at ht ht₁ ⊢
    have : p₀.length = p.length := rfl
    omega

end Turing.MultiTapeTM
