/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# Turning a computation into a tape transformer

`outputToTapeRewound tm` runs `tm` with its output redirected to a fresh work tape and then walks
the head of that tape back to the start of the word it has written. It is `outputToTape` followed
by `rewindWork`, which is needed because `outputToTape` leaves the new head at the write frontier,
one cell past the last symbol, whereas the normal form of `Turing.MultiTapeTM.TransformsTapes`
wants every head at cell `0`.

The point of the construction is `transformsTapes_outputToTapeRewound`: a machine that
*computes normally* — halting with its work tapes blank and all heads reset, cf.
`Turing.MultiTapeTM.ComputesNormalizedInTimeAndSpace` — becomes, after this redirection, an
ordinary tape transformer, and can therefore be used as a component by every combinator of the
plumbing layer. The normalization hypothesis is exactly what is needed: the redirection does not
touch the original tapes or the input head, so whatever mess `tm` leaves behind would be left
behind by the redirected machine too, and the result would not be in normal form.

## Main definitions

* `Turing.MultiTapeTM.outputToTapeRewound`: the redirected and rewound machine.

## Main results

* `Turing.MultiTapeTM.runFrom_outputToTapeRewound`: its run, from a word configuration with blank
  tapes to the same configuration with the output on the last tape.
* `Turing.MultiTapeTM.transformsTapes_outputToTapeRewound`: the resulting specification. The bounds
  depend on the input through the length of the output, so this is a *family* of specifications,
  one per input, as described in `TransformsTapes.lean`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `tm` with its output redirected onto a fresh last work tape, whose head is afterwards walked
back to the start of the word written there. -/
def outputToTapeRewound (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol (State ⊕ RewindWorkState) :=
  tm.outputToTape.seq ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k)))

@[simp]
lemma outputToTapeRewound_q₀ (tm : MultiTapeTM k Symbol State) :
    tm.outputToTapeRewound.q₀ = .inl tm.q₀ := rfl

namespace OutputToTapeRewound

/-- Adding an empty word on a fresh last tape to blank tapes leaves blank tapes. -/
private lemma snoc_nil :
    (Fin.snoc (fun _ => ([] : List Symbol)) [] : Fin (k + 1) → List Symbol) = fun _ => [] := by
  funext l
  induction l using Fin.lastCases <;> simp

variable {tm : MultiTapeTM k Symbol State} {output : List Symbol} {t s : ℕ}

/-- The configuration in which the first phase halts, spelled out: the output sits on the last
tape, but its head is still at the frontier just past it, so this is not a `wordsCfg`. The state
type is `RewindWorkState` because this is read as the *start* of the rewinding phase. -/
private def frontierCfg (ws : Fin k → List Symbol) (output out : List Symbol) :
    Cfg (k + 1) Symbol RewindWorkState input :=
  ⟨some (rewindWork Symbol).q₀, 1,
    fun l => tapeOfList ((Fin.snoc ws output : Fin (k + 1) → List Symbol) l),
    Fin.snoc (fun _ => (0 : ℤ)) (output.length : ℤ), out⟩

/-- The handoff: the first phase halts exactly where the rewinding phase starts. -/
private lemma withState_outCfg_wordsCfg (q : Option State) (ws : Fin k → List Symbol)
    (output out : List Symbol) :
    (Cfg.withOutput (outCfg (wordsCfg input q ws output)) out).withState
        (some ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).q₀) =
      frontierCfg ws output out := by
  rw [outCfg_wordsCfg_output]
  rfl

/-- **The redirection phase.** A normalized computation, redirected, turns blank tapes into blank
tapes with the output on the last one, leaving the head of that tape at the frontier. -/
private lemma runFrom_phase₀ (h : tm.ComputesNormalizedInTimeAndSpace input output t s)
    (out : List Symbol) :
    tm.outputToTape.runFrom (wordsCfg input (some tm.outputToTape.q₀) (fun _ => []) out) t =
      (outCfg (wordsCfg input none (fun _ => []) output)).withOutput out := by
  rw [show (wordsCfg input (some tm.outputToTape.q₀) (fun _ => []) out
        : Cfg (k + 1) Symbol State input) =
      (outCfg (wordsCfg input (some tm.q₀) (fun _ => []) [])).withOutput out from by
    rw [outputToTape_q₀, outCfg_wordsCfg, snoc_nil, withOutput_wordsCfg],
    runFrom_outputToTape_withOutput, runFrom_outCfg, h.1]

/-- The one-tape view of the start of the rewinding phase: the output, with the head at its
frontier. -/
private lemma oneTapeCfg_frontierCfg (ws : Fin k → List Symbol) (output out : List Symbol) :
    oneTapeCfg (Fin.last k) (frontierCfg (input := input) ws output out) =
      ⟨some (rewindWork Symbol).q₀, 1, fun _ => tapeOfList output,
        fun _ => (output.length : ℤ), out⟩ := by
  simp [oneTapeCfg, frontierCfg]

/-- **The rewinding phase.** Walking the head of the last tape back over the output puts the
configuration into normal form. -/
private lemma runFrom_phase₁ (ws : Fin k → List Symbol) (output out : List Symbol) :
    ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).runFrom
        (frontierCfg (input := input) ws output out) (output.length + 2) =
      wordsCfg input none (Fin.snoc ws output) out := by
  rw [runFrom_tapeEmb, oneTapeCfg_frontierCfg,
    runFrom_rewindWork_none _ _ _ rfl (le_refl output.length), embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;>
    induction l using Fin.lastCases with
    | last => simp [frontierCfg, wordsCfg]
    | cast j => simp [frontierCfg, wordsCfg]

/-- **The space of the rewinding phase.** The head walks from the frontier back to `0`, visiting
`|output| + 2` cells, and each of the `k` other tapes contributes the single cell its motionless
head stands on. -/
private lemma spaceUsed_phase₁ (ws : Fin k → List Symbol) (output out : List Symbol) (n : ℕ) :
    ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).spaceUsed
        (frontierCfg (input := input) ws output out) n ≤ output.length + 2 + k := by
  refine le_trans (spaceUsed_tapeEmb_le _ _ _ _) ?_
  rw [oneTapeCfg_frontierCfg]
  have := spaceUsed_rewindWork_le (Symbol := Symbol) (input := input) none 1 (tapeOfList output)
    out rfl (le_refl output.length) n
  omega

end OutputToTapeRewound

open OutputToTapeRewound in
/-- **The run of the redirected and rewound machine.** Started on blank tapes, it halts in normal
form with the output of `tm` on its fresh last tape, after `t + |output| + 2` steps: the `t` steps
of `tm`, and the walk of the new head from the frontier back to the start. -/
theorem runFrom_outputToTapeRewound {tm : MultiTapeTM k Symbol State} {output : List Symbol}
    {t s : ℕ} (h : tm.ComputesNormalizedInTimeAndSpace input output t s) (out : List Symbol) :
    tm.outputToTapeRewound.runFrom
        (wordsCfg input (some tm.outputToTapeRewound.q₀) (fun _ => []) out)
        (t + (output.length + 2)) =
      wordsCfg input none (Fin.snoc (fun _ => []) output) out := by
  have h₁ : ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).runFrom
      ((((outCfg (wordsCfg (State := State) input none (fun _ => []) output)).withOutput
        out).withState (some ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).q₀)))
      (output.length + 2) = wordsCfg input none (Fin.snoc (fun _ => []) output) out := by
    rw [withState_outCfg_wordsCfg]
    exact runFrom_phase₁ _ output out
  exact runFrom_seq (runFrom_phase₀ h out) rfl h₁ rfl

open OutputToTapeRewound in
/-- **The space of the redirected and rewound machine.** On top of the space of `tm` the output
tape costs twice the length of the output — once for writing it and once for walking back over
it — plus the boundary cell at each end, and the `k` original tapes each cost one cell while the
head is being rewound. -/
theorem spaceUsed_outputToTapeRewound {tm : MultiTapeTM k Symbol State} {output : List Symbol}
    {t s : ℕ} (h : tm.ComputesNormalizedInTimeAndSpace input output t s) (out : List Symbol) :
    tm.outputToTapeRewound.spaceUsed
        (wordsCfg input (some tm.outputToTapeRewound.q₀) (fun _ => []) out)
        (t + (output.length + 2)) ≤ s + 2 * output.length + k + 3 := by
  -- the redirection visits what `tm` visits, plus the cells of the output and its frontier
  have hspace₀ : tm.outputToTape.spaceUsed
      (wordsCfg input (some tm.outputToTape.q₀) (fun _ => []) out) t ≤ s + output.length + 1 := by
    rw [show (wordsCfg input (some tm.outputToTape.q₀) (fun _ => []) out
          : Cfg (k + 1) Symbol State input) =
        (outCfg (wordsCfg input (some tm.q₀) (fun _ => []) [])).withOutput out from by
      rw [outputToTape_q₀, outCfg_wordsCfg, snoc_nil, withOutput_wordsCfg],
      spaceUsed_outputToTape_withOutput]
    refine le_trans (spaceUsed_outputToTape _ _ _) ?_
    rw [h.1]
    exact Nat.add_le_add_right h.2 _
  have hfin : (((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).runFrom
      ((((outCfg (wordsCfg (State := State) input none (fun _ => []) output)).withOutput
        out).withState (some ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).q₀)))
      (output.length + 2)).Halted := by
    rw [withState_outCfg_wordsCfg, runFrom_phase₁]
    rfl
  -- spell the start out as a first-phase configuration, so that `spaceUsed_seq_le` applies
  -- without the elaborator having to unfold `outputToTapeRewound` against a metavariable
  have hstart : tm.outputToTapeRewound.spaceUsed
      (wordsCfg input (some tm.outputToTapeRewound.q₀) (fun _ => []) out)
      (t + (output.length + 2)) =
      (tm.outputToTape.seq ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k)))).spaceUsed
        (Sequential.leftCfg ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k)))
          (wordsCfg input (some tm.outputToTape.q₀) (fun _ => []) out))
        (t + (output.length + 2)) := rfl
  rw [hstart]
  refine le_trans (spaceUsed_seq_le (runFrom_phase₀ h out) rfl hfin) ?_
  rw [withState_outCfg_wordsCfg]
  have := spaceUsed_phase₁ (input := input) (k := k) (fun _ => []) output out (output.length + 2)
  omega

/-- **A normalized computation is a tape transformer.** Redirected onto a fresh last tape and
rewound, a machine that computes `output` from `input` leaving its tapes clean is an ordinary
`Turing.MultiTapeTM.TransformsTapes` machine: started on blank tapes it halts in normal form with
`output` on the last tape and nothing emitted.

The bounds mention the length of the output, so a machine computing a function gives one such
statement per input; `Turing.MultiTapeTM.TransformsTapes.exists` collects a family with uniform
bounds back into a single statement. -/
theorem transformsTapes_outputToTapeRewound {tm : MultiTapeTM k Symbol State}
    {output : List Symbol} {t s : ℕ}
    (h : tm.ComputesNormalizedInTimeAndSpace input output t s) :
    TransformsTapes tm.outputToTapeRewound
      (fun inp ws => inp = input ∧ ws = fun _ => [])
      (fun _ _ ws' => ws' = Fin.snoc (fun _ => []) output)
      (t + (output.length + 2)) (s + 2 * output.length + k + 3) := by
  rintro inp ws out ⟨rfl, rfl⟩
  exact ⟨_, runFrom_outputToTapeRewound h out, rfl, spaceUsed_outputToTapeRewound h out⟩

end Turing.MultiTapeTM
