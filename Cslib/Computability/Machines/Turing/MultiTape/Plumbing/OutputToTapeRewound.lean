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

The point of the construction is `transformsTapes_outputToTapeRewound`: it turns the *emission* of
a `Turing.MultiTapeTM.TransformsTapes` into a word on a work tape, so the result emits nothing and
can be plumbed further. The hypothesis is only that the machine starts and ends in normal form:
the redirection does not touch the original tapes or the input head, so whatever mess the machine
leaves behind would be left behind by the redirected machine too.

Because a whole computation *is* a tape transformation, cf.
`Turing.MultiTapeTM.ComputesFunNormalizedInTimeAndSpace`, this in particular turns a machine that
computes a function, leaving its tapes clean, into a tape transformer.

## Main definitions

* `Turing.MultiTapeTM.outputToTapeRewound`: the redirected and rewound machine.

## Main results

* `Turing.MultiTapeTM.runFrom_outputToTapeRewound_of_runFrom`: its run, from any run of the
  original machine that ends in normal form.
* `Turing.MultiTapeTM.transformsTapes_outputToTapeRewound`: the resulting specification. The
  bounds are numbers, so the length of the emitted word has to be bounded uniformly; a family of
  specifications with varying bounds is handled as described in `TransformsTapes.lean`.
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

/-- Spelling the start of the first phase as a redirected configuration. -/
private lemma wordsCfg_snoc_nil (ws : Fin k → List Symbol) (out : List Symbol) :
    (wordsCfg input (some tm.outputToTape.q₀) (Fin.snoc ws []) out
        : Cfg (k + 1) Symbol State input) =
      (outCfg (wordsCfg input (some tm.q₀) ws [])).withOutput out := by
  rw [outputToTape_q₀, outCfg_wordsCfg, withOutput_wordsCfg]

/-- **The redirection phase.** A run that leaves the words `ws'` behind and emits `e` becomes,
redirected, a run that leaves `ws'` behind and writes `e` on the fresh last tape, with the head of
that tape at the frontier just past `e`. -/
private lemma runFrom_phase₀ {ws ws' : Fin k → List Symbol} {e : List Symbol}
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) ws []) t = wordsCfg input none ws' e)
    (out : List Symbol) :
    tm.outputToTape.runFrom (wordsCfg input (some tm.outputToTape.q₀) (Fin.snoc ws []) out) t =
      (outCfg (wordsCfg input none ws' e)).withOutput out := by
  rw [wordsCfg_snoc_nil, runFrom_outputToTape_withOutput, runFrom_outCfg, hrun]

/-- **The space of the redirection phase.** On top of the space of the original run the fresh tape
costs the cells of the emitted word and the frontier cell past it. -/
private lemma spaceUsed_phase₀ {ws ws' : Fin k → List Symbol} {e : List Symbol}
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) ws []) t = wordsCfg input none ws' e)
    (hspace : tm.spaceUsed (wordsCfg input (some tm.q₀) ws []) t ≤ s) (out : List Symbol) :
    tm.outputToTape.spaceUsed
        (wordsCfg input (some tm.outputToTape.q₀) (Fin.snoc ws []) out) t ≤ s + e.length + 1 := by
  rw [wordsCfg_snoc_nil, spaceUsed_outputToTape_withOutput]
  refine le_trans (spaceUsed_outputToTape _ _ _) ?_
  rw [hrun]
  exact Nat.add_le_add_right hspace _

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
/-- **The run of the redirected and rewound machine.** A run of `tm` that leaves the words `ws'`
behind and emits `e` becomes a run that leaves `ws'` behind with `e` on its fresh last tape, in
normal form, after `t + |e| + 2` steps: the `t` steps of `tm`, and the walk of the new head from
the frontier back to the start. -/
theorem runFrom_outputToTapeRewound_of_runFrom {tm : MultiTapeTM k Symbol State}
    {ws ws' : Fin k → List Symbol} {e : List Symbol} {t : ℕ}
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) ws []) t = wordsCfg input none ws' e)
    (out : List Symbol) :
    tm.outputToTapeRewound.runFrom
        (wordsCfg input (some tm.outputToTapeRewound.q₀) (Fin.snoc ws []) out)
        (t + e.length + 2) =
      wordsCfg input none (Fin.snoc ws' e) out := by
  have h₁ : ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).runFrom
      ((((outCfg (wordsCfg (State := State) input none ws' e)).withOutput
        out).withState (some ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).q₀)))
      (e.length + 2) = wordsCfg input none (Fin.snoc ws' e) out := by
    rw [withState_outCfg_wordsCfg]
    exact runFrom_phase₁ _ e out
  exact runFrom_seq (runFrom_phase₀ hrun out) rfl h₁ rfl

open OutputToTapeRewound in
/-- **The space of the redirected and rewound machine.** The bound is the sum of the two phases
and is not tight: the redirection costs the space of `tm` plus the cells of the emitted word and
its frontier, and the rewinding costs the cells walked back over plus one cell on each of the `k`
original tapes, with the cells of the emitted word counted in both. -/
theorem spaceUsed_outputToTapeRewound_of_runFrom {tm : MultiTapeTM k Symbol State}
    {ws ws' : Fin k → List Symbol} {e : List Symbol} {t s : ℕ}
    (hrun : tm.runFrom (wordsCfg input (some tm.q₀) ws []) t = wordsCfg input none ws' e)
    (hspace : tm.spaceUsed (wordsCfg input (some tm.q₀) ws []) t ≤ s) (out : List Symbol) :
    tm.outputToTapeRewound.spaceUsed
        (wordsCfg input (some tm.outputToTapeRewound.q₀) (Fin.snoc ws []) out)
        (t + e.length + 2) ≤ s + 2 * e.length + k + 3 := by
  have hfin : (((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).runFrom
      ((((outCfg (wordsCfg (State := State) input none ws' e)).withOutput
        out).withState (some ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).q₀)))
      (e.length + 2)).Halted := by
    rw [withState_outCfg_wordsCfg, runFrom_phase₁]
    rfl
  -- spell the start out as a first-phase configuration, so that `spaceUsed_seq_le` applies
  -- without the elaborator having to unfold `outputToTapeRewound` against a metavariable
  have hstart : tm.outputToTapeRewound.spaceUsed
      (wordsCfg input (some tm.outputToTapeRewound.q₀) (Fin.snoc ws []) out)
      (t + e.length + 2) =
      (tm.outputToTape.seq ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k)))).spaceUsed
        (Sequential.leftCfg ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k)))
          (wordsCfg input (some tm.outputToTape.q₀) (Fin.snoc ws []) out))
        (t + e.length + 2) := rfl
  rw [hstart, show t + e.length + 2 = t + (e.length + 2) from by omega]
  refine le_trans (spaceUsed_seq_le (runFrom_phase₀ hrun out) rfl hfin) ?_
  rw [withState_outCfg_wordsCfg]
  have h₀ := spaceUsed_phase₀ (s := s) hrun hspace out
  have h₁ := spaceUsed_phase₁ (input := input) ws' e out (e.length + 2)
  omega

/-- **Redirecting the output of a tape transformation onto a work tape.** If `tm` transforms words
and emits, then `tm` redirected and rewound transforms the same words on the first `k` tapes and
writes what it would have emitted onto a fresh last tape, which it is given blank. The result emits
nothing, so it is a tape transformation in the strictest sense and can be plumbed further.

The bounds need a bound `o` on the length of the emitted word, since they are numbers while the
emitted word varies with the input; `ho` supplies it. -/
theorem transformsTapes_outputToTapeRewound {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {t s o : ℕ} (h : TransformsTapes tm P Q t s)
    (ho : ∀ input ws ws' e, P input ws → Q input ws ws' e → e.length ≤ o) :
    TransformsTapes tm.outputToTapeRewound
      (fun input ws => ∃ w, ws = Fin.snoc w [] ∧ P input w)
      (fun input ws ws' e => ∃ w w' v, ws = Fin.snoc w [] ∧ Q input w w' v ∧
        ws' = Fin.snoc w' v ∧ e = [])
      (t + o + 2) (s + 2 * o + k + 3) := by
  rintro inp ws out ⟨w, rfl, hP⟩
  obtain ⟨w', v, hrun, hQ, hspace⟩ := h inp w [] hP
  rw [List.nil_append] at hrun
  have hv : v.length ≤ o := ho _ _ _ _ hP hQ
  have hr := runFrom_outputToTapeRewound_of_runFrom hrun out
  have hs := spaceUsed_outputToTapeRewound_of_runFrom hrun hspace out
  have hhalt : (tm.outputToTapeRewound.runFrom
      (wordsCfg inp (some tm.outputToTapeRewound.q₀) (Fin.snoc w []) out)
      (t + v.length + 2)).state = none := by
    rw [hr]
    rfl
  refine ⟨Fin.snoc w' v, [], ?_, ⟨w, w', v, rfl, hQ, rfl, rfl⟩, ?_⟩
  · rw [List.append_nil, runFrom_eq_of_halt _ _ (by omega) hhalt, hr]
  · rw [spaceUsed_eq_of_halt _ (by omega) hhalt]
    omega

end Turing.MultiTapeTM
