/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Writing the output as a word on a work tape

`outputToWord tm` runs `tm` with its output written to a new last work tape instead of the output
tape (`outputToTape tm`), and then moves the head of that tape back to cell `0`
(`Turing.MultiTapeTM.rewindWork`). While `outputToTape tm` runs, the last work tape holds the
output so far, with its head on the cell right after it.

If `tm` computes `output` tidily (`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`), then
`outputToWord tm` takes blank work tapes to blank work tapes, except that the last one holds
`output`, and emits nothing.

## Main results

* `Turing.MultiTapeTM.outputToWord`: the composed machine.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.outputToWord`: its specification.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-! ### Writing the output to a work tape -/

/-- `tm`, with its output writes redirected onto a fresh last work tape, whose head always stands
at the write frontier. -/
noncomputable def outputToTape (tm : MultiTapeTM k Symbol State) :
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
def outCfg (c : Cfg k Symbol State input) :
    Cfg (k + 1) Symbol State input :=
  ⟨c.state, c.inputPos,
    Fin.lastCases (tapeOfList c.output) (fun j => c.workTapes j),
    Fin.lastCases (c.output.length : ℤ) (fun j => c.workTapePos j),
    []⟩

@[simp]
lemma outCfg_inputSymbol (c : Cfg k Symbol State input) :
    (outCfg c).inputSymbol = c.inputSymbol := rfl

@[simp]
lemma outCfg_workTapes_last (c : Cfg k Symbol State input) :
    (outCfg c).workTapes (Fin.last k) = tapeOfList c.output := by
  simp [outCfg]

@[simp]
lemma outCfg_workTapes_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapes j.castSucc = c.workTapes j := by
  simp [outCfg]

@[simp]
lemma outCfg_workTapePos_last (c : Cfg k Symbol State input) :
    (outCfg c).workTapePos (Fin.last k) = (c.output.length : ℤ) := by
  simp [outCfg]

@[simp]
lemma outCfg_workTapePos_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapePos j.castSucc = c.workTapePos j := by
  simp [outCfg]

@[simp]
lemma outCfg_workTapeSymbols_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapeSymbols j.castSucc = c.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- The redirection is a step-semiconjugation. -/
lemma step_outCfg (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input) :
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

/-- The redirected run mirrors the original. -/
lemma runFrom_outCfg (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input)
    (n : ℕ) :
    tm.outputToTape.runFrom (outCfg c) n = outCfg (tm.runFrom c n) :=
  (Function.Semiconj.iterate_right (fun c => (step_outCfg tm c).symm) n c).symm

/-- **Space of the output-redirected machine.** The `k` inner tapes visit exactly what the original
does, and the frontier head only walks between the initial and the final length of the output, so
the redirection costs at most the final output length plus one. -/
lemma spaceUsed_outputToTape (tm : MultiTapeTM k Symbol State)
    (c : Cfg k Symbol State input) (u : ℕ) :
    tm.outputToTape.spaceUsed (outCfg c) u ≤
      tm.spaceUsed c u + ((tm.runFrom c u).output.length + 1) := by
  let p : tm.RunPath input :=
    { length := u
      toFun n := tm.runFrom c n
      step n := by simp [runFrom, Function.iterate_succ_apply'] }
  simpa using tm.spaceUsed_le_of_workTapePos_embedding Fin.castSuccEmb c (outCfg c)
    ((tm.runFrom c u).output.length + 1) (fun m _ j => by simp [runFrom_outCfg])
    fun l hl => by
      induction l using Fin.lastCases with
      | last =>
        refine (spaceUsedByTape_le_card _
          (S := .Icc (c.output.length : ℤ) (tm.runFrom c u).output.length) fun m hm => ?_).trans
          (by simp)
        have h0 : c.output.length ≤ (tm.runFrom c m).output.length := by
          simpa [p, runFrom] using
            p.length_output_mono (Fin.zero_le ⟨m, Nat.lt_succ_of_le hm⟩)
        have hu : (tm.runFrom c m).output.length ≤ (tm.runFrom c u).output.length :=
          p.length_output_mono (Fin.le_last ⟨m, Nat.lt_succ_of_le hm⟩)
        simp only [runFrom_outCfg, outCfg_workTapePos_last, Finset.mem_Icc]
        omega
      | cast j => exact absurd ⟨j, rfl⟩ hl

/-! ### Rewinding the output tape -/

/-- `tm` with its output written to a new last work tape, whose head is then moved back to
cell `0`. -/
public noncomputable def outputToWord (tm : MultiTapeTM k Symbol State) :
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

/-- Rewinding the last work tape of `outCfg (wordsCfg input q (fun _ => []) out)` takes
`out.length + 2` steps, leaves `out` as a word on that tape and visits at most `out.length + k + 2`
cells. -/
private lemma runFrom_rewindLast (out : List Symbol) :
    let rewind := (rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))
    let cfg := outCfg (wordsCfg input (some (rewindWork Symbol).q₀) (fun _ : Fin k => []) out)
    rewind.runFrom cfg (out.length + 2) =
        wordsCfg input none (Function.update (fun _ => []) (Fin.last k) out) [] ∧
      rewind.spaceUsed cfg (out.length + 2) ≤ out.length + k + 2 := by
  intro rewind cfg
  refine ⟨?_, (spaceUsed_tapeEmb_le _ _ cfg _).trans ?_⟩
  · rw [runFrom_tapeEmb, oneTapeCfg_outCfg_wordsCfg, runFrom_rewindWork_none _ _ _ rfl le_rfl,
      embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
      simp [cfg, wordsCfg]
  · have := spaceUsed_rewindWork_le (input := input) none 1 (tapeOfList out) [] rfl le_rfl
      (out.length + 2)
    rw [oneTapeCfg_outCfg_wordsCfg]
    omega

open Sequential in
/-- If `tm` computes `output` tidily, then `outputToWord tm`, started on blank work tapes, halts
with `output` on its last work tape, every other work tape blank, and nothing emitted. -/
public theorem ComputesTidilyInTimeAndSpace.outputToWord {tm : MultiTapeTM k Symbol State}
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
  -- run `tm` with its output on the last work tape, then rewind that tape
  have h₁ : tm.outputToTape.runFrom (wordsCfg input (some tm.q₀) (fun _ => []) []) t =
      outCfg (wordsCfg input none (fun _ => []) output) := by
    rw [← outCfg_wordsCfg, runFrom_outCfg, hrun]
  obtain ⟨h₂, hs₂⟩ := runFrom_rewindLast (k := k) (input := input) output
  have hs₁ := spaceUsed_outputToTape tm (wordsCfg input (some tm.q₀) (fun _ => []) []) t
  rw [outCfg_wordsCfg, hrun, wordsCfg_output] at hs₁
  rw [add_assoc t]
  exact ⟨_, [], runFrom_seq h₁ rfl h₂ rfl, ⟨rfl, rfl⟩,
    (spaceUsed_seq_le h₁ rfl (congrArg Cfg.state h₂)).trans
      ((Nat.add_le_add hs₁ hs₂).trans (by omega))⟩

end Turing.MultiTapeTM
