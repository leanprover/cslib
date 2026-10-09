/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy

/-!
# Turning a tidy computation into a word-to-word tape transformation

`outputToWord tm` redirects a machine's output onto a fresh last work tape and then rewinds that
tape's head back to the start. It is the sequential composition of `outputToTape tm`, which writes
what `tm` would output onto the fresh tape (with the head left at the write frontier), and
`rewindWork` placed on that last tape, which walks the head back to `0` without erasing.

For a machine that computes *tidily* — halting with every work tape blank, every work head and the
input head back where they started — the composite is a genuine `wordsCfg → wordsCfg` tape
transformation: it takes blank tapes to blank tapes except for the last tape, which ends up holding
the emitted word with its head at the start.

## Main results

* `Turing.MultiTapeTM.outputToWord`: the composed machine.
* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.outputToWord`: a tidy computation becomes a tape
  transformation placing the output on the last tape.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `tm`, with its output redirected onto a fresh last work tape whose head is then rewound to the
start: `outputToTape tm` followed by `rewindWork` placed on the last tape. -/
noncomputable def outputToWord (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol (State ⊕ RewindWorkState) :=
  tm.outputToTape.seq ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k)))

/-- **Glue.** The redirected view of a word configuration with no output is the word configuration
on `k + 1` tapes whose last word is empty. -/
lemma outCfg_wordsCfg (q : Option State) (ws : Fin k → List Symbol) :
    outCfg (wordsCfg input q ws []) = wordsCfg input q (Fin.snoc ws []) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [outCfg, wordsCfg]

open Sequential in
/-- **A tidy computation becomes a word-to-word tape transformation.** Started on blank tapes,
`outputToWord tm` halts with every tape blank except the fresh last tape, which holds the emitted
word with its head back at the start. -/
theorem ComputesTidilyInTimeAndSpace.outputToWord {k : ℕ} {Symbol State : Type*}
    {tm : MultiTapeTM k Symbol State} {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    TransformsTapes tm.outputToWord
      (fun inp ws => inp = input ∧ ws = fun _ => [])
      (fun _ _ ws' e => ws' = Function.update (fun _ => []) (Fin.last k) output ∧ e = [])
      (t + output.length + 2) (s + 2 * output.length + k + 3) := by
  obtain ⟨hrun, hspace⟩ := computesTidily_iff.mp h
  -- abbreviations for the two phases and the junction configuration
  set tm₁ : MultiTapeTM (k + 1) Symbol RewindWorkState :=
    (rewindWork Symbol).extendTapes (tapeEmb (Fin.last k)) with htm₁
  rw [transformsTapes_iff_nil_output]
  rintro inp ws ⟨hin, rfl⟩
  subst inp
  set mid : Cfg (k + 1) Symbol State input := outCfg (wordsCfg input none (fun _ => []) output)
    with hmid_def
  have hwo : tm.outputToWord = tm.outputToTape.seq tm₁ := rfl
  -- the blank `k + 1` tapes are the blank `k` tapes with a blank last tape adjoined
  have hsnoc : (fun _ : Fin (k + 1) => ([] : List Symbol)) =
      Fin.snoc (fun _ : Fin k => ([] : List Symbol)) [] :=
    funext fun l => by induction l using Fin.lastCases <;> simp
  -- the starting configuration, handed over to the sequential composition
  have hstart : wordsCfg input (some (tm.outputToTape.seq tm₁).q₀) (fun _ => []) [] =
      leftCfg tm₁ (wordsCfg input (some tm.outputToTape.q₀) (fun _ => []) []) := rfl
  -- PHASE 1: outputToTape mirrors `tm` through `outCfg`
  have hphase1 : tm.outputToTape.runFrom
      (wordsCfg input (some tm.outputToTape.q₀) (fun _ => []) []) t = mid := by
    rw [hmid_def, hsnoc, ← outCfg_wordsCfg, show tm.outputToTape.q₀ = tm.q₀ from rfl,
      runFrom_outCfg, hrun]
  have hmid_halt : mid.Halted := by rw [hmid_def]; rfl
  -- PHASE 2: rewind the last tape's head from the frontier back to the start
  have hphase2 : tm₁.runFrom (mid.withState (some tm₁.q₀)) (output.length + 2) =
      wordsCfg input none (Function.update (fun _ => []) (Fin.last k) output) [] := by
    rw [htm₁, show tm₁.q₀ = (rewindWork Symbol).q₀ from rfl, runFrom_tapeEmb]
    have hone : (rewindWork Symbol).runFrom
        (oneTapeCfg (Fin.last k) (mid.withState (some (rewindWork Symbol).q₀)))
        (output.length + 2) =
          ⟨none, 1, fun _ => tapeOfList output, fun _ => 0, []⟩ := by
      have := runFrom_rewindWork_none (input := input) (Symbol := Symbol) 1 (tapeOfList output) []
        (w := output) rfl (p := output.length) le_rfl
      simpa only [oneTapeCfg, hmid_def, outCfg, Cfg.withState, wordsCfg,
        outCfg_workTapes_last, outCfg_workTapePos_last, Fin.lastCases_last] using this
    rw [hone, embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases with
      | last => simp [wordsCfg]
      | cast j =>
        simp [hmid_def, wordsCfg, outCfg_workTapes_castSucc, outCfg_workTapePos_castSucc,
          Cfg.withState]
  refine ⟨Function.update (fun _ => []) (Fin.last k) output, [], ?_, ⟨rfl, rfl⟩, ?_⟩
  · -- chain the two phases at run level; the junction `mid` is not a `wordsCfg`
    rw [show t + output.length + 2 = t + (output.length + 2) by omega, hwo,
      hstart, runFrom_seq hphase1 hmid_halt hphase2 rfl]
    rw [rightCfg, mapState_wordsCfg]
    rfl
  · -- SPACE: phase 1 costs `s + output.length + 1`, phase 2 costs `output.length + 2 + k`
    rw [show t + output.length + 2 = t + (output.length + 2) by omega, hwo,
      hstart]
    refine (spaceUsed_seq_le hphase1 hmid_halt (by rw [hphase2]; rfl)).trans ?_
    -- phase 1 space
    have h1 : tm.outputToTape.spaceUsed
        (wordsCfg input (some tm.outputToTape.q₀) (fun _ => []) []) t ≤ s + output.length + 1 := by
      rw [hsnoc, ← outCfg_wordsCfg, show tm.outputToTape.q₀ = tm.q₀ from rfl]
      refine (spaceUsed_outputToTape tm (wordsCfg input (some tm.q₀) (fun _ => []) []) t).trans ?_
      rw [hrun]
      simp only [wordsCfg_output]
      omega
    -- phase 2 space: the head stays within `[-1, output.length]`, one cell per other tape
    have h2 : tm₁.spaceUsed (mid.withState (some tm₁.q₀)) (output.length + 2) ≤
        output.length + 2 + k := by
      rw [htm₁, show tm₁.q₀ = (rewindWork Symbol).q₀ from rfl]
      refine (spaceUsed_tapeEmb_le (rewindWork Symbol) (Fin.last k) _ _).trans ?_
      have hcard : (rewindWork Symbol).spaceUsed
          (oneTapeCfg (Fin.last k) (mid.withState (some (rewindWork Symbol).q₀)))
          (output.length + 2) ≤ output.length + 2 := by
        rw [spaceUsed, Fin.sum_univ_one]
        refine (spaceUsedByTape_le_card _ (S := .Icc (-1) (output.length : ℤ)) fun m _ => ?_).trans
          (by rw [Int.card_Icc]; omega)
        have hpos := workTapePos_runFrom_rewindWork (input := input) (Symbol := Symbol) none 1
          (tapeOfList output) [] (w := output) rfl (p := output.length) le_rfl m
        refine Finset.mem_Icc.2 ?_
        simpa only [oneTapeCfg, hmid_def, outCfg, Cfg.withState, wordsCfg, outCfg_workTapes_last,
          outCfg_workTapePos_last, Fin.lastCases_last, Set.mem_Icc] using hpos
      omega
    omega

end Turing.MultiTapeTM
