/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Tactic.FinCases
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WriteLeft

/-!
# Reading the input from a work tape, in normal form

`inputFromTapeFlagged tm mark` is `Turing.MultiTapeTM.inputFromTape` wrapped in the two steps that
set up and tear down its flag tape. `inputFromTape` expects its flag tape to carry `mark` at cell
`-1`, which is outside the normal form of `Turing.MultiTapeTM.TransformsTapes` — there every tape
is blank at every negative cell. The wrapper writes the mark before the computation and erases it
afterwards, using `Turing.MultiTapeTM.writeLeft`, so the composite starts and ends in normal form.

The hypothesis that makes this work is that `tm` *computes normally*, cf.
`Turing.MultiTapeTM.ComputesNormalizedInTimeAndSpace`: it halts with its work tapes blank and its
input head back at the start. The input head of `tm` is simulated by the virtual input head, so
only then are the two fresh heads back at cell `0` at the end, where the teardown step expects
them.

Unlike `Turing.MultiTapeTM.outputToTapeRewound` this is *not* a
`Turing.MultiTapeTM.TransformsTapes`: the composite still emits the output of `tm` on the real
output tape, which `TransformsTapes` forbids. It is therefore stated directly as a run, in the same
`Turing.wordsCfg` vocabulary.

## Main definitions

* `Turing.MultiTapeTM.inputFromTapeFlagged`: the wrapped machine.

## Main results

* `Turing.MultiTapeTM.runFrom_inputFromTapeFlagged`: its run, from a word configuration holding the
  simulated input on the first fresh tape to the same configuration with the output emitted.
* `Turing.MultiTapeTM.spaceUsed_inputFromTapeFlagged`: its space.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input outerInput : List Symbol}

/-- `tm`, reading its input from the first of two fresh work tapes, with the flag tape set up and
torn down so that the whole machine starts and ends in normal form. -/
def inputFromTapeFlagged (tm : MultiTapeTM k Symbol State) (mark : Symbol) :
    MultiTapeTM (k + 2) Symbol (WriteLeftState ⊕ (State ⊕ WriteLeftState)) :=
  ((writeLeft (some mark)).extendTapes (tapeEmb (flagTape k))).seq
    (tm.inputFromTape.seq ((writeLeft none).extendTapes (tapeEmb (flagTape k))))

@[simp]
lemma inputFromTapeFlagged_q₀ (tm : MultiTapeTM k Symbol State) (mark : Symbol) :
    (tm.inputFromTapeFlagged mark).q₀ = .inl .start := rfl

namespace InputFromTapeFlagged

variable {tm : MultiTapeTM k Symbol State} {output : List Symbol} {t s : ℕ}

/-- The flag tape of a word configuration whose two fresh tapes hold the simulated input and
nothing: blank, with its head at `0`. -/
private lemma oneTapeCfg_flagTape (q : Option State) (ws : Fin k → List Symbol)
    (out : List Symbol) :
    oneTapeCfg (flagTape k) (wordsCfg outerInput q (Fin.append ws ![input, []]) out) =
      ⟨q, 1, fun _ => fun _ => none, fun _ => 0, out⟩ := by
  simp [oneTapeCfg, flagTape, wordsCfg]

/-- Setting or clearing the mark on the flag tape of a word configuration is exactly the
difference between that configuration and its redirected form. -/
private lemma embed_flagTape (q : Option State) (ws : Fin k → List Symbol) (out : List Symbol)
    (c : ℤ → Option Symbol) (mark : Symbol) (hc : c = Function.update (fun _ => none) (-1)
      (some mark)) :
    embed (tapeEmb (flagTape k)) (⟨q, 1, fun _ => c, fun _ => 0, out⟩ :
        Cfg 1 Symbol State outerInput)
        (fun l => tapeOfList ((Fin.append ws ![input, []] : Fin (k + 2) → List Symbol) l))
        (fun _ => 0) =
      inCfg mark (wordsCfg input q ws out) outerInput := by
  subst hc
  have hne (j : Fin k) : Fin.castAdd 2 j ≠ Fin.natAdd k 1 :=
    Fin.ne_of_val_ne (by simp; omega)
  rw [embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext l
    induction l using Fin.addCases with
    | left j => simp [inCfg, flagTape, wordsCfg, Function.update_of_ne (hne j)]
    | right i => fin_cases i <;> simp [inCfg, flagTape, wordsCfg, Fin.ext_iff]

/-- **The setup phase.** Two steps put the mark on the flag tape and bring its head back. -/
private lemma runFrom_phase₀ (mark : Symbol) (ws : Fin k → List Symbol) (out : List Symbol) :
    ((writeLeft (some mark)).extendTapes (tapeEmb (flagTape k))).runFrom
        (wordsCfg outerInput (some ((writeLeft (some mark)).extendTapes
          (tapeEmb (flagTape k))).q₀) (Fin.append ws ![input, []]) out) 2 =
      inCfg mark (wordsCfg input (none : Option WriteLeftState) ws out) outerInput := by
  rw [extendTapes_q₀, runFrom_tapeEmb, oneTapeCfg_flagTape, runFrom_writeLeft]
  exact embed_flagTape _ _ _ _ _ (by simp)

/-- The flag tape of a redirected word configuration: blank apart from the mark at `-1`, with its
head at `0`. -/
private lemma oneTapeCfg_inCfg_flagTape (mark : Symbol) (q : Option State)
    (ws : Fin k → List Symbol) (out : List Symbol) :
    oneTapeCfg (flagTape k) (inCfg mark (wordsCfg input q ws out) outerInput) =
      ⟨q, 1, fun _ => Function.update (fun _ => none) (-1) (some mark), fun _ => 0, out⟩ := by
  simp [oneTapeCfg, inCfg, flagTape, wordsCfg]

/-- **The teardown phase.** Two steps erase the mark again, putting the configuration back into
normal form. -/
private lemma runFrom_phase₂ (mark : Symbol) (ws : Fin k → List Symbol) (out : List Symbol) :
    ((writeLeft none).extendTapes (tapeEmb (flagTape k))).runFrom
        ((inCfg mark (wordsCfg input (none : Option State) ws out) outerInput).withState
          (some ((writeLeft (none : Option Symbol)).extendTapes (tapeEmb (flagTape k))).q₀)) 2 =
      wordsCfg outerInput none (Fin.append ws ![input, []]) out := by
  have hne (j : Fin k) : Fin.castAdd 2 j ≠ Fin.natAdd k 1 :=
    Fin.ne_of_val_ne (by simp; omega)
  rw [withState_inCfg, withState_wordsCfg, extendTapes_q₀, runFrom_tapeEmb,
    oneTapeCfg_inCfg_flagTape, runFrom_writeLeft, embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext l
    induction l using Fin.addCases with
    | left j => simp [inCfg, flagTape, wordsCfg, Function.update_of_ne (hne j)]
    | right i => fin_cases i <;> simp [inCfg, flagTape, wordsCfg, Fin.ext_iff]

/-- **The computing phase.** The redirected machine runs `tm` on the word on the virtual input
tape, emitting its output after whatever was already there. -/
private lemma runFrom_phase₁ (h : tm.ComputesNormalizedInTimeAndSpace input output t s)
    (mark : Symbol) (out : List Symbol) :
    tm.inputFromTape.runFrom
        (inCfg mark (wordsCfg input (some tm.inputFromTape.q₀) (fun _ => []) out) outerInput) t =
      inCfg mark (wordsCfg input none (fun _ => []) (out ++ output)) outerInput := by
  rw [show wordsCfg input (some tm.inputFromTape.q₀) (fun _ => ([] : List Symbol)) out =
      (wordsCfg input (some tm.q₀) (fun _ => ([] : List Symbol)) []).prependOutput out from by
        simp, prependOutput_inCfg, runFrom_prependOutput, runFrom_inCfg, h.1,
    ← prependOutput_inCfg]
  simp

/-- **The space of the computing phase.** On top of the space of `tm` the two fresh tapes cost the
cells the simulated input head can reach. -/
private lemma spaceUsed_phase₁ (h : tm.ComputesNormalizedInTimeAndSpace input output t s)
    (mark : Symbol) (out : List Symbol) :
    tm.inputFromTape.spaceUsed
        (inCfg mark (wordsCfg input (some tm.inputFromTape.q₀) (fun _ => []) out) outerInput) t ≤
      s + 2 * (input.length + 2) := by
  rw [show wordsCfg input (some tm.inputFromTape.q₀) (fun _ => ([] : List Symbol)) out =
      (wordsCfg input (some tm.q₀) (fun _ => ([] : List Symbol)) []).prependOutput out from by
        simp, prependOutput_inCfg, spaceUsed_prependOutput]
  exact (spaceUsed_inputFromTape _ _ _ _ _).trans (Nat.add_le_add_right h.2 _)

/-- **The space of the setup phase**, and, with the mark already in place, of the teardown phase:
the two cells of the flag tape, plus one cell for each other tape. -/
private lemma spaceUsed_writeLeft_flagTape (w : Option Symbol)
    (c : Cfg (k + 2) Symbol WriteLeftState outerInput)
    (hstate : c.state = some (writeLeft w).q₀) (hpos : c.workTapePos (flagTape k) = 0) (n : ℕ) :
    ((writeLeft w).extendTapes (tapeEmb (flagTape k))).spaceUsed c n ≤ k + 3 := by
  have hone : oneTapeCfg (flagTape k) c =
      ⟨some (writeLeft w).q₀, c.inputPos, fun _ => c.workTapes (flagTape k),
        fun _ => (0 : ℤ), c.output⟩ :=
    Cfg.ext hstate rfl rfl (funext fun _ => hpos) rfl
  refine (spaceUsed_tapeEmb_le _ _ _ _).trans ?_
  rw [hone]
  have := spaceUsed_writeLeft_le (input := outerInput) w c.inputPos (c.workTapes (flagTape k))
    c.output 0 n
  omega

/-- The flag head of a redirected word configuration rests at `0`, because the simulated input
head rests at the start of the input. -/
private lemma workTapePos_inCfg_flagTape {State' : Type*} (mark : Symbol) (q : Option State)
    (q' : Option State') (ws : Fin k → List Symbol) (out : List Symbol) :
    ((inCfg mark (wordsCfg input q ws out) outerInput).withState q').workTapePos (flagTape k)
      = 0 := by
  simp [flagTape, wordsCfg, Cfg.withState]

end InputFromTapeFlagged

open InputFromTapeFlagged Sequential in
/-- **The run of the wrapped machine.** Started in normal form with the simulated input on the
first of its two fresh tapes, it halts in normal form with the output of `tm` emitted, after
`t + 4` steps: two to set the flag up, the `t` steps of `tm`, and two to tear it down. -/
theorem runFrom_inputFromTapeFlagged {tm : MultiTapeTM k Symbol State} {output : List Symbol}
    {t s : ℕ} (h : tm.ComputesNormalizedInTimeAndSpace input output t s) (mark : Symbol)
    (outerInput out : List Symbol) :
    (tm.inputFromTapeFlagged mark).runFrom
        (wordsCfg outerInput (some (tm.inputFromTapeFlagged mark).q₀)
          (Fin.append (fun _ => []) ![input, []]) out) (t + 4) =
      wordsCfg outerInput none (Fin.append (fun _ => []) ![input, []]) (out ++ output) := by
  rw [show t + 4 = 2 + (t + 2) from by omega]
  have h₁ : (tm.inputFromTape.seq ((writeLeft none).extendTapes (tapeEmb (flagTape k)))).runFrom
      (((inCfg mark (wordsCfg input (none : Option WriteLeftState) (fun _ => []) out)
          outerInput).withState (some (tm.inputFromTape.seq
            ((writeLeft (none : Option Symbol)).extendTapes (tapeEmb (flagTape k)))).q₀)))
      (t + 2) =
      rightCfg (wordsCfg outerInput none (Fin.append (fun _ => []) ![input, []])
        (out ++ output)) :=
    runFrom_seq (runFrom_phase₁ h mark out) rfl (runFrom_phase₂ mark (fun _ => []) (out ++ output))
      rfl
  exact runFrom_seq (runFrom_phase₀ mark (fun _ => []) out) rfl h₁ rfl

open InputFromTapeFlagged Sequential in
/-- **The space of the wrapped machine.** On top of the space of `tm` the virtual input tape and
the flag tape each cost the cells the simulated input head can reach, and the setup and teardown
steps cost one cell on every tape they do not use. -/
theorem spaceUsed_inputFromTapeFlagged {tm : MultiTapeTM k Symbol State} {output : List Symbol}
    {t s : ℕ} (h : tm.ComputesNormalizedInTimeAndSpace input output t s) (mark : Symbol)
    (outerInput out : List Symbol) :
    (tm.inputFromTapeFlagged mark).spaceUsed
        (wordsCfg outerInput (some (tm.inputFromTapeFlagged mark).q₀)
          (Fin.append (fun _ => []) ![input, []]) out) (t + 4) ≤
      s + 2 * input.length + 2 * k + 10 := by
  rw [show t + 4 = 2 + (t + 2) from by omega]
  have hmid := runFrom_phase₀ (k := k) (input := input) (outerInput := outerInput) mark
    (fun _ => []) out
  have hspace₀ : ((writeLeft (some mark)).extendTapes (tapeEmb (flagTape k))).spaceUsed
      (wordsCfg outerInput (some ((writeLeft (some mark)).extendTapes (tapeEmb (flagTape k))).q₀)
        (Fin.append (fun _ => []) ![input, []]) out) 2 ≤ k + 3 :=
    spaceUsed_writeLeft_flagTape _ _ rfl (by simp [flagTape, wordsCfg]) 2
  have hspace₂ : ((writeLeft (none : Option Symbol)).extendTapes
        (tapeEmb (flagTape k))).spaceUsed
      ((inCfg mark (wordsCfg input (none : Option State) (fun _ => []) (out ++ output))
        outerInput).withState (some ((writeLeft (none : Option Symbol)).extendTapes
          (tapeEmb (flagTape k))).q₀)) 2 ≤ k + 3 :=
    spaceUsed_writeLeft_flagTape _ _ rfl (workTapePos_inCfg_flagTape _ _ _ _ _) 2
  have hhalt₂ : ((((writeLeft (none : Option Symbol)).extendTapes
      (tapeEmb (flagTape k))).runFrom
      ((inCfg mark (wordsCfg input (none : Option State) (fun _ => []) (out ++ output))
        outerInput).withState (some ((writeLeft (none : Option Symbol)).extendTapes
          (tapeEmb (flagTape k))).q₀)) 2)).Halted := by
    rw [runFrom_phase₂]
    rfl
  have hspace₁ : (tm.inputFromTape.seq ((writeLeft none).extendTapes
        (tapeEmb (flagTape k)))).spaceUsed
      ((inCfg mark (wordsCfg input (none : Option WriteLeftState) (fun _ => []) out)
        outerInput).withState (some (tm.inputFromTape.seq
          ((writeLeft (none : Option Symbol)).extendTapes (tapeEmb (flagTape k)))).q₀)) (t + 2) ≤
      (s + 2 * (input.length + 2)) + (k + 3) :=
    (spaceUsed_seq_le (runFrom_phase₁ h mark out) rfl hhalt₂).trans
      (Nat.add_le_add (spaceUsed_phase₁ h mark out) hspace₂)
  have hrun₁ : (tm.inputFromTape.seq ((writeLeft none).extendTapes
      (tapeEmb (flagTape k)))).runFrom
      ((inCfg mark (wordsCfg input (none : Option WriteLeftState) (fun _ => []) out)
        outerInput).withState (some (tm.inputFromTape.seq
          ((writeLeft (none : Option Symbol)).extendTapes (tapeEmb (flagTape k)))).q₀))
      (t + 2) =
      rightCfg (wordsCfg outerInput none (Fin.append (fun _ => []) ![input, []])
        (out ++ output)) :=
    runFrom_seq (runFrom_phase₁ h mark out) rfl (runFrom_phase₂ mark (fun _ => []) (out ++ output))
      rfl
  have hhalt₁ : ((tm.inputFromTape.seq ((writeLeft none).extendTapes
      (tapeEmb (flagTape k)))).runFrom
      ((inCfg mark (wordsCfg input (none : Option WriteLeftState) (fun _ => []) out)
        outerInput).withState (some (tm.inputFromTape.seq
          ((writeLeft (none : Option Symbol)).extendTapes (tapeEmb (flagTape k)))).q₀))
      (t + 2)).Halted := by
    rw [hrun₁]
    rfl
  -- spell the start out as a first-phase configuration, so that `spaceUsed_seq_le` applies
  -- without the elaborator having to unfold `inputFromTapeFlagged` against a metavariable
  have hstart : (tm.inputFromTapeFlagged mark).spaceUsed
      (wordsCfg outerInput (some (tm.inputFromTapeFlagged mark).q₀)
        (Fin.append (fun _ => []) ![input, []]) out) (2 + (t + 2)) =
      (((writeLeft (some mark)).extendTapes (tapeEmb (flagTape k))).seq
        (tm.inputFromTape.seq ((writeLeft none).extendTapes (tapeEmb (flagTape k))))).spaceUsed
        (leftCfg (tm.inputFromTape.seq ((writeLeft none).extendTapes (tapeEmb (flagTape k))))
          (wordsCfg outerInput (some ((writeLeft (some mark)).extendTapes
            (tapeEmb (flagTape k))).q₀) (Fin.append (fun _ => []) ![input, []]) out))
        (2 + (t + 2)) := rfl
  rw [hstart]
  have := (spaceUsed_seq_le hmid rfl hhalt₁).trans (Nat.add_le_add hspace₀ hspace₁)
  omega

end Turing.MultiTapeTM
