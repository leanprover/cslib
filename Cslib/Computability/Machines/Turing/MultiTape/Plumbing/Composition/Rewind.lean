/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Composition.Simulation

/-! # Assembling output redirection, rewind, and input substitution -/

@[expose] public section

namespace Turing.MultiTapeTM.Composition

variable {k₀ k₁ : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}
variable (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁)

/-- Extend the output machine with the blank second-machine tape block. -/
def outputLift (cfg : Cfg (k₀ + 1) Symbol State₀ input) :=
  ExtendTapes.embed (outputEmbedding k₀ k₁) cfg (fun _ _ => none) (fun _ => 0)

@[simp]
lemma outputLift_embed (cfg : Cfg k₀ Symbol State₀ input) :
    outputLift (k₁ := k₁) (OutputToWorkTape.embed cfg) =
      ⟨cfg.state, cfg.inputPos, tapes cfg.workTapes (listTape cfg.output) (fun _ _ => none),
        tapes cfg.workTapePos cfg.output.length (fun _ => 0), []⟩ := by
  apply Cfg.ext <;> try rfl
  · exact extend_output_const _ _ _
  · exact extend_output_const _ _ _

/-- The first phase is an output-redirection run followed by the generic sequential handoff. -/
lemma embedFirst_eq (cfg : Cfg k₀ Symbol State₀ input) :
    embedFirst tm₀ tm₁ cfg =
      Sequential.left ((rewind (.work (compositionIntermediateTapeIdx k₀ k₁))).seq
        (inputMachine k₀ tm₁)) (outputLift (OutputToWorkTape.embed cfg)) := by
  rw [outputLift_embed]
  cases hs : cfg.state <;> simp [embedFirst, hs, Sequential.left, seq, rewind, Cfg.withState]

/-- Tape extension and output redirection commute with every native run. -/
lemma runFrom_outputLift (cfg : Cfg k₀ Symbol State₀ input) (n : ℕ) :
    (outputMachine tm₀ k₁).runFrom (outputLift (OutputToWorkTape.embed cfg)) n =
      outputLift (OutputToWorkTape.embed (tm₀.runFrom cfg n)) := by
  simp only [outputMachine, outputLift, ExtendTapes.runFrom_embed, OutputToWorkTape.runFrom_embed]

/-- The first embedding takes initial configurations to initial configurations. -/
lemma embedFirst_initCfg (input : List Symbol) :
    embedFirst tm₀ tm₁ (tm₀.initCfg input) = (comp tm₀ tm₁).initCfg input := by
  apply Cfg.ext <;> try rfl
  · funext i p
    cases p <;> simp [embedFirst, ite_apply, listTape]
  · funext i
    simp [embedFirst]

/-- The first component runs up to its earliest halt. -/
lemma runFrom_firstPhase (input : List Symbol) (n : ℕ)
    (hactive : ∀ m < n, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none) :
    (comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input) n =
      embedFirst tm₀ tm₁ (tm₀.runFrom (tm₀.initCfg input) n) := by
  rw [← embedFirst_initCfg, embedFirst_eq, comp, Sequential.runFrom_left]
  · rw [runFrom_outputLift, ← embedFirst_eq]
  · intro m hm
    rw [runFrom_outputLift]
    exact hactive m hm

/-- Embed the generic rewind phase into the two nested sequential machines. -/
def rewindLift (cfg : Cfg k₀ Symbol State₀ input) (q : Option RewindState) (pos : ℤ) :
    Cfg (compositionTapeCount k₀ k₁) Symbol (CompositionState State₀ State₁) input :=
  Sequential.right (Sequential.left (inputMachine k₀ tm₁)
    (Rewind.workCfg (outputLift (OutputToWorkTape.embed cfg))
      (compositionIntermediateTapeIdx k₀ k₁) q pos))

/-- A scanning rewind configuration has exactly the intermediate-tape layout. -/
lemma rewindLift_scan (cfg : Cfg k₀ Symbol State₀ input) (pos : ℤ) :
    rewindLift tm₁ cfg (some .scan) pos =
      intermediateCfg tm₀ tm₁ cfg (.inr (.inl .scan)) pos := by
  ext i z <;>
    simp [rewindLift, Sequential.right, Sequential.left, Rewind.workCfg, Cfg.withState,
      intermediateCfg, embedFirst, Function.update_apply, Fin.ext_iff]

/-- The final rewind configuration enters the initial virtual-input classifier. -/
lemma rewindLift_halt (cfg : Cfg k₀ Symbol State₀ input) :
    rewindLift tm₁ cfg none 0 =
      intermediateCfg tm₀ tm₁ cfg (.inr (.inr (.classify tm₁.q₀ .right))) 0 := by
  ext i z <;>
    simp [rewindLift, Sequential.right, Sequential.left, Rewind.workCfg, Cfg.withState,
      inputMachine, extendTapes, inputFromWorkTape,
      intermediateCfg, embedFirst, Function.update_apply, Fin.ext_iff]

/-- The halt of the output machine starts the work-tape rewind at the end of its output. -/
lemma embedFirst_halt (cfg : Cfg k₀ Symbol State₀ input) (hhalt : cfg.state = none) :
    embedFirst tm₀ tm₁ cfg = rewindLift tm₁ cfg (some .start) cfg.output.length := by
  ext i z <;>
    simp [rewindLift, Sequential.right, Sequential.left, Rewind.workCfg, Cfg.withState,
      embedFirst, hhalt, Function.update_apply, Fin.ext_iff]
  split_ifs <;> simp_all
  omega

/-- After the first machine halts, each scanning step moves left through its output. -/
lemma runFrom_firstHalt_rewind (cfg : Cfg k₀ Symbol State₀ input) (hhalt : cfg.state = none)
    (r : ℕ) (hr : r ≤ cfg.output.length) :
    (comp tm₀ tm₁).runFrom (embedFirst tm₀ tm₁ cfg) (r + 1) =
      intermediateCfg tm₀ tm₁ cfg (.inr (.inl .scan)) (cfg.output.length - 1 - r) := by
  rw [embedFirst_halt tm₀ tm₁ cfg hhalt, rewindLift, comp, Sequential.runFrom_right,
    Sequential.runFrom_left]
  · rw [runFrom_succ_eq_step, Rewind.step_work_start,
      Rewind.runFrom_work_scan _ _ cfg.output (by simp) r hr]
    exact rewindLift_scan tm₀ tm₁ cfg _
  · intro m hm
    exact Rewind.work_active _ _ cfg.output (by simp) m (by omega)

/-- Rewinding the output enters the second machine's initial classifier. -/
lemma runFrom_firstHalt_classify (cfg : Cfg k₀ Symbol State₀ input) (hhalt : cfg.state = none) :
    (comp tm₀ tm₁).runFrom (embedFirst tm₀ tm₁ cfg) (cfg.output.length + 2) =
      intermediateCfg tm₀ tm₁ cfg (.inr (.inr (.classify tm₁.q₀ .right))) 0 := by
  rw [embedFirst_halt tm₀ tm₁ cfg hhalt, rewindLift, comp, Sequential.runFrom_right,
    Sequential.runFrom_left]
  · rw [Rewind.runFrom_work _ _ cfg.output (by simp)]
    exact rewindLift_halt tm₀ tm₁ cfg
  · intro m hm
    exact Rewind.work_active _ _ cfg.output (by simp) m hm

/-- The rewound tape is the input-substitution machine's initial classifier configuration. -/
lemma intermediateCfg_classify_init (cfg : Cfg k₀ Symbol State₀ input) :
    intermediateCfg tm₀ tm₁ cfg (.inr (.inr (.classify tm₁.q₀ .right))) 0 =
      classifyCfg tm₀ tm₁ cfg (tm₁.initCfg cfg.output) .right := by
  ext i p <;>
    simp [intermediateCfg, embedFirst, classifyCfg, embedSecond, InputFromWorkTape.virtualInputPos]
  split_ifs <;> simp_all
  omega

/-- Output rewind and the initial classifier take the output length plus three steps. -/
lemma runFrom_firstHalt_to_secondInit (cfg : Cfg k₀ Symbol State₀ input)
    (hhalt : cfg.state = none) :
    (comp tm₀ tm₁).runFrom (embedFirst tm₀ tm₁ cfg) (cfg.output.length + 3) =
      embedSecond tm₀ tm₁ cfg (tm₁.initCfg cfg.output) := by
  rw [runFrom_succ_eq_step', runFrom_firstHalt_classify tm₀ tm₁ cfg hhalt,
    intermediateCfg_classify_init, step_classify_init]

/-- The first run and output rewind establish the second machine's initial state. -/
lemma runFrom_to_secondInit (input : List Symbol) (u : ℕ)
    (hhalt : (tm₀.runFrom (tm₀.initCfg input) u).state = none)
    (hactive : ∀ m < u, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none) :
    (comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input)
        (u + ((tm₀.runFrom (tm₀.initCfg input) u).output.length + 3)) =
      embedSecond tm₀ tm₁ (tm₀.runFrom (tm₀.initCfg input) u)
        (tm₁.initCfg (tm₀.runFrom (tm₀.initCfg input) u).output) := by
  rw [runFrom_add, runFrom_firstPhase tm₀ tm₁ input u hactive,
    runFrom_firstHalt_to_secondInit tm₀ tm₁ _ hhalt]

end Turing.MultiTapeTM.Composition
