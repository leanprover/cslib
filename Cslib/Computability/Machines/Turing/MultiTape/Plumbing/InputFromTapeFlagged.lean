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

The hypothesis that makes this work is that `tm` starts and ends in normal form, with its input
head back at the start: the input head of `tm` is simulated by the virtual input head, so only then
are the two fresh heads back at cell `0` at the end, where the teardown step expects them.

The composite still emits what `tm` emits, on the real output tape, so this is a
`Turing.MultiTapeTM.TransformsTapes` only because that specification describes the output as a
suffix appended to the ambient one. Together with
`Turing.MultiTapeTM.transformsTapes_outputToTapeRewound`, which turns such an emission back into a
word on a work tape, the two adapters stack.

## Main definitions

* `Turing.MultiTapeTM.inputFromTapeFlagged`: the wrapped machine.

## Main results

* `Turing.MultiTapeTM.runFrom_inputFromTapeFlagged_of_runFrom`: its run, from any run of the
  original machine that ends in normal form.
* `Turing.MultiTapeTM.transformsTapes_inputFromTapeFlagged`: the resulting specification. The
  bounds are numbers, so the length of the simulated input has to be bounded uniformly.
* `Turing.MultiTapeTM.runFrom_inputFromTapeFlagged`: the special case of a whole computation,
  cf. `Turing.MultiTapeTM.ComputesNormalizedInTimeAndSpace`.
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

/-- **The computing phase.** The redirected machine mirrors `tm` run on the word on the virtual
input tape. -/
private lemma runFrom_phase₁ {ws ws' : Fin k → List Symbol} {out e : List Symbol}
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) ws out) t =
      wordsCfg input none ws' (out ++ e)) (mark : Symbol) :
    tm.inputFromTape.runFrom
        (inCfg mark (wordsCfg input (some tm.inputFromTape.q₀) ws out) outerInput) t =
      inCfg mark (wordsCfg input none ws' (out ++ e)) outerInput := by
  rw [inputFromTape_q₀, runFrom_inCfg, hrun]

/-- **The space of the computing phase.** On top of the space of `tm` the two fresh tapes cost the
cells the simulated input head can reach. -/
private lemma spaceUsed_phase₁ {ws : Fin k → List Symbol} {out : List Symbol}
    (hspace : tm.spaceUsed (wordsCfg input (some tm.q₀) ws out) t ≤ s) (mark : Symbol) :
    tm.inputFromTape.spaceUsed
        (inCfg mark (wordsCfg input (some tm.inputFromTape.q₀) ws out) outerInput) t ≤
      s + 2 * (input.length + 2) :=
  (spaceUsed_inputFromTape _ _ _ _ _).trans (Nat.add_le_add_right hspace _)

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
first of its two fresh tapes, it mirrors a run of `tm` on that word and halts in normal form,
after `t + 4` steps: two to set the flag up, the `t` steps of `tm`, and two to tear it down. -/
theorem runFrom_inputFromTapeFlagged_of_runFrom {tm : MultiTapeTM k Symbol State}
    {ws ws' : Fin k → List Symbol} {out e : List Symbol} {t : ℕ}
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) ws out) t =
      wordsCfg input none ws' (out ++ e))
    (mark : Symbol) (outerInput : List Symbol) :
    (tm.inputFromTapeFlagged mark).runFrom
        (wordsCfg outerInput (some (tm.inputFromTapeFlagged mark).q₀)
          (Fin.append ws ![input, []]) out) (t + 4) =
      wordsCfg outerInput none (Fin.append ws' ![input, []]) (out ++ e) := by
  rw [show t + 4 = 2 + (t + 2) from by omega]
  have h₁ : (tm.inputFromTape.seq ((writeLeft none).extendTapes (tapeEmb (flagTape k)))).runFrom
      (((inCfg mark (wordsCfg input (none : Option WriteLeftState) ws out)
          outerInput).withState (some (tm.inputFromTape.seq
            ((writeLeft (none : Option Symbol)).extendTapes (tapeEmb (flagTape k)))).q₀)))
      (t + 2) =
      rightCfg (wordsCfg outerInput none (Fin.append ws' ![input, []]) (out ++ e)) :=
    runFrom_seq (runFrom_phase₁ hrun mark) rfl (runFrom_phase₂ mark ws' (out ++ e)) rfl
  exact runFrom_seq (runFrom_phase₀ mark ws out) rfl h₁ rfl

open InputFromTapeFlagged Sequential in
/-- **The space of the wrapped machine.** On top of the space of `tm` the virtual input tape and
the flag tape each cost the cells the simulated input head can reach, and the setup and teardown
steps cost one cell on every tape they do not use. -/
theorem spaceUsed_inputFromTapeFlagged_of_runFrom {tm : MultiTapeTM k Symbol State}
    {ws ws' : Fin k → List Symbol} {out e : List Symbol} {t s : ℕ}
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) ws out) t =
      wordsCfg input none ws' (out ++ e))
    (hspace : tm.spaceUsed (wordsCfg input (some tm.q₀) ws out) t ≤ s)
    (mark : Symbol) (outerInput : List Symbol) :
    (tm.inputFromTapeFlagged mark).spaceUsed
        (wordsCfg outerInput (some (tm.inputFromTapeFlagged mark).q₀)
          (Fin.append ws ![input, []]) out) (t + 4) ≤
      s + 2 * input.length + 2 * k + 10 := by
  rw [show t + 4 = 2 + (t + 2) from by omega]
  have hmid := runFrom_phase₀ (input := input) (outerInput := outerInput) mark ws out
  have hspace₀ : ((writeLeft (some mark)).extendTapes (tapeEmb (flagTape k))).spaceUsed
      (wordsCfg outerInput (some ((writeLeft (some mark)).extendTapes (tapeEmb (flagTape k))).q₀)
        (Fin.append ws ![input, []]) out) 2 ≤ k + 3 :=
    spaceUsed_writeLeft_flagTape _ _ rfl (by simp [flagTape, wordsCfg]) 2
  have hspace₂ : ((writeLeft (none : Option Symbol)).extendTapes
        (tapeEmb (flagTape k))).spaceUsed
      ((inCfg mark (wordsCfg input (none : Option State) ws' (out ++ e))
        outerInput).withState (some ((writeLeft (none : Option Symbol)).extendTapes
          (tapeEmb (flagTape k))).q₀)) 2 ≤ k + 3 :=
    spaceUsed_writeLeft_flagTape _ _ rfl (workTapePos_inCfg_flagTape _ _ _ _ _) 2
  have hhalt₂ : ((((writeLeft (none : Option Symbol)).extendTapes
      (tapeEmb (flagTape k))).runFrom
      ((inCfg mark (wordsCfg input (none : Option State) ws' (out ++ e))
        outerInput).withState (some ((writeLeft (none : Option Symbol)).extendTapes
          (tapeEmb (flagTape k))).q₀)) 2)).Halted := by
    rw [runFrom_phase₂]
    rfl
  have hspace₁ : (tm.inputFromTape.seq ((writeLeft none).extendTapes
        (tapeEmb (flagTape k)))).spaceUsed
      ((inCfg mark (wordsCfg input (none : Option WriteLeftState) ws out)
        outerInput).withState (some (tm.inputFromTape.seq
          ((writeLeft (none : Option Symbol)).extendTapes (tapeEmb (flagTape k)))).q₀)) (t + 2) ≤
      (s + 2 * (input.length + 2)) + (k + 3) :=
    (spaceUsed_seq_le (runFrom_phase₁ hrun mark) rfl hhalt₂).trans
      (Nat.add_le_add (spaceUsed_phase₁ hspace mark) hspace₂)
  have hrun₁ : (tm.inputFromTape.seq ((writeLeft none).extendTapes
      (tapeEmb (flagTape k)))).runFrom
      ((inCfg mark (wordsCfg input (none : Option WriteLeftState) ws out)
        outerInput).withState (some (tm.inputFromTape.seq
          ((writeLeft (none : Option Symbol)).extendTapes (tapeEmb (flagTape k)))).q₀))
      (t + 2) =
      rightCfg (wordsCfg outerInput none (Fin.append ws' ![input, []]) (out ++ e)) :=
    runFrom_seq (runFrom_phase₁ hrun mark) rfl (runFrom_phase₂ mark ws' (out ++ e)) rfl
  have hhalt₁ : ((tm.inputFromTape.seq ((writeLeft none).extendTapes
      (tapeEmb (flagTape k)))).runFrom
      ((inCfg mark (wordsCfg input (none : Option WriteLeftState) ws out)
        outerInput).withState (some (tm.inputFromTape.seq
          ((writeLeft (none : Option Symbol)).extendTapes (tapeEmb (flagTape k)))).q₀))
      (t + 2)).Halted := by
    rw [hrun₁]
    rfl
  -- spell the start out as a first-phase configuration, so that `spaceUsed_seq_le` applies
  -- without the elaborator having to unfold `inputFromTapeFlagged` against a metavariable
  have hstart : (tm.inputFromTapeFlagged mark).spaceUsed
      (wordsCfg outerInput (some (tm.inputFromTapeFlagged mark).q₀)
        (Fin.append ws ![input, []]) out) (2 + (t + 2)) =
      (((writeLeft (some mark)).extendTapes (tapeEmb (flagTape k))).seq
        (tm.inputFromTape.seq ((writeLeft none).extendTapes (tapeEmb (flagTape k))))).spaceUsed
        (leftCfg (tm.inputFromTape.seq ((writeLeft none).extendTapes (tapeEmb (flagTape k))))
          (wordsCfg outerInput (some ((writeLeft (some mark)).extendTapes
            (tapeEmb (flagTape k))).q₀) (Fin.append ws ![input, []]) out))
        (2 + (t + 2)) := rfl
  rw [hstart]
  have := (spaceUsed_seq_le hmid rfl hhalt₁).trans (Nat.add_le_add hspace₀ hspace₁)
  omega

/-- **Reading the input of a tape transformation from a work tape.** If `tm` transforms words and
emits, then `tm` reading its input from the first of two fresh work tapes transforms the same words
on the first `k` tapes, leaves the simulated input and the flag tape as it found them, and emits
the same word. The result is again a `Turing.MultiTapeTM.TransformsTapes`, which is what makes the
two adapters stack.

The bounds need a bound `m` on the length of the simulated input, since they are numbers while the
word on the virtual input tape varies; `hm` supplies it. -/
theorem transformsTapes_inputFromTapeFlagged {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {t s m : ℕ} (h : TransformsTapes tm P Q t s) (mark : Symbol)
    (hm : ∀ inp ws, P inp ws → inp.length ≤ m) :
    TransformsTapes (tm.inputFromTapeFlagged mark)
      (fun _ ws => ∃ inp w, ws = Fin.append w ![inp, []] ∧ P inp w)
      (fun _ ws ws' e => ∃ inp w w', ws = Fin.append w ![inp, []] ∧
        ws' = Fin.append w' ![inp, []] ∧ Q inp w w' e)
      (t + 4) (s + 2 * m + 2 * k + 10) := by
  rintro outerInput ws out ⟨inp, w, rfl, hP⟩
  obtain ⟨w', e, hrun, hQ, hspace⟩ := h inp w out hP
  refine ⟨Fin.append w' ![inp, []], e,
    runFrom_inputFromTapeFlagged_of_runFrom hrun mark outerInput, ⟨inp, w, w', rfl, rfl, hQ⟩, ?_⟩
  have hs := spaceUsed_inputFromTapeFlagged_of_runFrom hrun hspace mark outerInput
  have := hm inp w hP
  omega

/-- **The run of the wrapped machine on a normalized computation.** Started in normal form with
the input on the first of its two fresh tapes, it halts in normal form with the output of `tm`
emitted. -/
theorem runFrom_inputFromTapeFlagged {tm : MultiTapeTM k Symbol State} {output : List Symbol}
    {t s : ℕ} (h : tm.ComputesNormalizedInTimeAndSpace input output t s) (mark : Symbol)
    (outerInput out : List Symbol) :
    (tm.inputFromTapeFlagged mark).runFrom
        (wordsCfg outerInput (some (tm.inputFromTapeFlagged mark).q₀)
          (Fin.append (fun _ => []) ![input, []]) out) (t + 4) =
      wordsCfg outerInput none (Fin.append (fun _ => []) ![input, []]) (out ++ output) := by
  obtain ⟨ws', e, hrun, ⟨rfl, rfl⟩, -⟩ := h.transformsTapes input (fun _ => []) out ⟨rfl, rfl⟩
  exact runFrom_inputFromTapeFlagged_of_runFrom hrun mark outerInput

/-- **The space of the wrapped machine on a normalized computation.** -/
theorem spaceUsed_inputFromTapeFlagged {tm : MultiTapeTM k Symbol State} {output : List Symbol}
    {t s : ℕ} (h : tm.ComputesNormalizedInTimeAndSpace input output t s) (mark : Symbol)
    (outerInput out : List Symbol) :
    (tm.inputFromTapeFlagged mark).spaceUsed
        (wordsCfg outerInput (some (tm.inputFromTapeFlagged mark).q₀)
          (Fin.append (fun _ => []) ![input, []]) out) (t + 4) ≤
      s + 2 * input.length + 2 * k + 10 := by
  obtain ⟨ws', e, hrun, ⟨rfl, rfl⟩, hspace⟩ :=
    h.transformsTapes input (fun _ => []) out ⟨rfl, rfl⟩
  exact spaceUsed_inputFromTapeFlagged_of_runFrom hrun hspace mark outerInput

end Turing.MultiTapeTM
