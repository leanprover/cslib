/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.StepLemmas
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Redirecting the output to a work tape

`outputToTape tm` behaves like `tm`, except that whatever `tm` would append to the write-only
output tape is written on a fresh work tape instead, whose head always stands at the write
frontier. The design is due to Samuel Schlesinger (leanprover/cslib#872).

Since the output is append-only, the frontier position is a *function of the configuration* —
the length of the output so far — so the redirected machine mirrors the original through the
configuration map `outCfg`, an unconditional step-semiconjugation: the run lemma is one
application of `Turing.MultiTapeTM.runFrom_comm_of_step`, with no induction.
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
  change Fin.lastCases (motive := fun _ => ℤ → Option Symbol) (tapeOfList c.output)
    (fun j => c.workTapes j) (Fin.last k) = _
  exact Fin.lastCases_last

@[simp]
public lemma outCfg_workTapes_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapes j.castSucc = c.workTapes j := by
  change Fin.lastCases (motive := fun _ => ℤ → Option Symbol) (tapeOfList c.output)
    (fun j => c.workTapes j) j.castSucc = _
  exact Fin.lastCases_castSucc j

@[simp]
public lemma outCfg_workTapePos_last (c : Cfg k Symbol State input) :
    (outCfg c).workTapePos (Fin.last k) = (c.output.length : ℤ) := by
  change Fin.lastCases (motive := fun _ => ℤ) ((c.output.length : ℤ))
    (fun j => c.workTapePos j) (Fin.last k) = _
  exact Fin.lastCases_last

@[simp]
public lemma outCfg_workTapePos_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapePos j.castSucc = c.workTapePos j := by
  change Fin.lastCases (motive := fun _ => ℤ) ((c.output.length : ℤ))
    (fun j => c.workTapePos j) j.castSucc = _
  exact Fin.lastCases_castSucc j

@[simp]
public lemma outCfg_workTapeSymbols_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapeSymbols j.castSucc = c.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- The redirection is a step-semiconjugation. -/
public lemma step_outCfg (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input) :
    tm.outputToTape.step (outCfg c) = outCfg (tm.step c) := by
  cases hq : c.state with
  | none =>
    have h1 : (outCfg c).state = none := hq
    simp only [step, h1, hq]
  | some q =>
    have h1 : (outCfg c).state = some q := hq
    have hargs : (fun j : Fin k => (outCfg c).workTapeSymbols j.castSucc) =
        c.workTapeSymbols := funext fun j => outCfg_workTapeSymbols_castSucc c j
    simp only [step, h1, hq, outputToTape]
    rw [hargs, outCfg_inputSymbol]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext l z
      induction l using Fin.lastCases with
      | last =>
        rcases hout : (tm.tr q c.inputSymbol c.workTapeSymbols).output with _ | sym
        · simp [Action.apply, hout, Fin.lastCases_last]
        · simp only [Action.apply, hout, Fin.lastCases_last, outCfg_workTapes_last,
            outCfg_workTapePos_last, Option.toList_some, tapeOfList_append_single]
      | cast j =>
        rcases hw : ((tm.tr q c.inputSymbol c.workTapeSymbols).workTapes j).1 with _ | w <;>
          simp [Action.apply, hw, Fin.lastCases_castSucc]
    · funext l
      induction l using Fin.lastCases with
      | last =>
        rcases hout : (tm.tr q c.inputSymbol c.workTapeSymbols).output with _ | sym <;>
          simp [Action.apply, hout, Fin.lastCases_last, SignType.cast]
      | cast j =>
        simp [Action.apply, Fin.lastCases_castSucc]

/-- The redirected run mirrors the original. -/
public lemma runFrom_outCfg (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input)
    (n : ℕ) :
    tm.outputToTape.runFrom (outCfg c) n = outCfg (tm.runFrom c n) :=
  runFrom_comm_of_step outCfg (step_outCfg tm) c n

section WithOutput

/-- `outputToTape tm` never writes the real output, so replacing it commutes with a step. -/
public lemma step_outputToTape_withOutput (tm : MultiTapeTM k Symbol State)
    (c : Cfg (k + 1) Symbol State input) (out : List Symbol) :
    tm.outputToTape.step (c.withOutput out) = (tm.outputToTape.step c).withOutput out := by
  cases hq : c.state with
  | none =>
    have h1 : (c.withOutput out).state = none := hq
    rw [step_of_halt h1, step_of_halt hq]
  | some q =>
    have h1 : (c.withOutput out).state = some q := hq
    have hin : (c.withOutput out).inputSymbol = c.inputSymbol := rfl
    have hws : (c.withOutput out).workTapeSymbols = c.workTapeSymbols := rfl
    have hout : (tm.outputToTape.tr q c.inputSymbol c.workTapeSymbols).output = none := by
      simp [outputToTape]
    rw [step_apply_of_state h1, step_apply_of_state hq, hin, hws]
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext l z; simp [Cfg.withOutput]
    · funext l; simp [Cfg.withOutput]
    · simp only [Action.apply_output, Cfg.withOutput_output, hout, Option.toList_none,
        List.append_nil]

/-- The redirected run commutes with the real output already present. -/
public lemma runFrom_outputToTape_withOutput (tm : MultiTapeTM k Symbol State)
    (c : Cfg (k + 1) Symbol State input) (out : List Symbol) (n : ℕ) :
    tm.outputToTape.runFrom (c.withOutput out) n = (tm.outputToTape.runFrom c n).withOutput out :=
  runFrom_comm_of_step (fun c => c.withOutput out)
    (fun c => step_outputToTape_withOutput tm c out) c n

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
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext l z
    induction l using Fin.lastCases with
    | last => simp [initCfg, Cfg.init]
    | cast j => simp [initCfg, Cfg.init]
  · funext l
    induction l using Fin.lastCases with
    | last => simp [initCfg, Cfg.init]
    | cast j => simp [initCfg, Cfg.init]

/-- The output can only grow. -/
public lemma length_output_mono (tm : MultiTapeTM k Symbol State)
    (c : Cfg k Symbol State input) (d : ℕ) :
    c.output.length ≤ (tm.runFrom c d).output.length := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [runFrom_succ_eq_step', step_output, List.length_append]
    omega

/-- Redirecting the output costs the length of the output, and nothing else: the frontier head
walks over exactly the cells of the written output. -/
public lemma spaceUsed_outputToTape (tm : MultiTapeTM k Symbol State)
    (c : Cfg k Symbol State input) (u : ℕ) :
    tm.outputToTape.spaceUsed (outCfg c) u ≤
      tm.spaceUsed c u + ((tm.runFrom c u).output.length + 1) := by
  have hmirror : ∀ m, tm.outputToTape.runFrom (outCfg c) m = outCfg (tm.runFrom c m) :=
    fun m => runFrom_outCfg tm c m
  have hcast : ∀ j : Fin k, tm.outputToTape.visitedByTapeHead (outCfg c) u j.castSucc =
      tm.visitedByTapeHead c u j := by
    intro j
    refine Finset.image_congr fun m _ => ?_
    rw [hmirror m, outCfg_workTapePos_castSucc]
  have hlast : tm.outputToTape.visitedByTapeHead (outCfg c) u (Fin.last k) ⊆
      Finset.Icc (c.output.length : ℤ) ((tm.runFrom c u).output.length : ℤ) := by
    intro z hz
    obtain ⟨m, hm, rfl⟩ := mem_visitedByTapeHead.mp hz
    rw [hmirror m, outCfg_workTapePos_last]
    have h1 := length_output_mono tm c m
    have h2 : (tm.runFrom c m).output.length ≤ (tm.runFrom c u).output.length := by
      have h := length_output_mono tm (tm.runFrom c m) (u - m)
      rw [← runFrom_add, show m + (u - m) = u from by omega] at h
      exact h
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  calc tm.outputToTape.spaceUsed (outCfg c) u
      = (∑ j : Fin k, tm.outputToTape.spaceUsedByTape (outCfg c) u j.castSucc) +
        tm.outputToTape.spaceUsedByTape (outCfg c) u (Fin.last k) :=
        Fin.sum_univ_castSucc _
    _ ≤ tm.spaceUsed c u + ((tm.runFrom c u).output.length + 1) := by
        refine Nat.add_le_add (le_of_eq ?_) ?_
        · exact Finset.sum_congr rfl fun j _ => congrArg Finset.card (hcast j)
        · calc tm.outputToTape.spaceUsedByTape (outCfg c) u (Fin.last k)
              ≤ (Finset.Icc (c.output.length : ℤ)
                ((tm.runFrom c u).output.length : ℤ)).card := Finset.card_le_card hlast
            _ = (((tm.runFrom c u).output.length : ℤ) + 1 - (c.output.length : ℤ)).toNat :=
                Int.card_Icc _ _
            _ ≤ (tm.runFrom c u).output.length + 1 := by omega

end Turing.MultiTapeTM
