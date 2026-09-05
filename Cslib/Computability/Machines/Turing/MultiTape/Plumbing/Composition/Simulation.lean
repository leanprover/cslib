/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Composition.Layout

/-! # Lifting the generic virtual-input simulation into composition -/

@[expose] public section

namespace Turing.MultiTapeTM.Composition

variable {k₀ k₁ : ℕ} {Symbol State₀ State₁ : Type*}
variable (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁)
variable {firstInput secondInput : List Symbol}

/-- Extend a virtual-input configuration while retaining the first machine's tapes. -/
def inputLift (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    (cfg : Cfg (k₁ + 1) Symbol (InputState State₁) firstInput) :=
  ExtendTapes.embed (inputEmbedding k₀ k₁) cfg
    (tapes firstCfg.workTapes (fun _ => none) (fun _ _ => none))
    (tapes firstCfg.workTapePos 0 (fun _ => 0))

/-- The second-phase embedding is tape extension followed by two sequential state embeddings. -/
lemma embedSecond_eq (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    (cfg : Cfg k₁ Symbol State₁ secondInput) :
    embedSecond tm₀ tm₁ firstCfg cfg =
      Sequential.right (Sequential.right
        (inputLift firstCfg (InputFromWorkTape.embed firstCfg.inputPos cfg))) := by
  apply Cfg.ext
  · cases hs : cfg.state <;>
      simp [embedSecond, Sequential.right, Cfg.withState, inputLift, ExtendTapes.embed,
        InputFromWorkTape.embed, hs]
  · rfl
  · exact (extend_input _ _ _ _ _).symm
  · exact (extend_input _ _ _ _ _).symm
  · rfl

/-- The classifier embedding has the same tape extension. -/
lemma classifyCfg_eq (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    (cfg : Cfg k₁ Symbol State₁ secondInput) (boundary : InputBoundary) :
    classifyCfg tm₀ tm₁ firstCfg cfg boundary =
      Sequential.right (Sequential.right
        (inputLift firstCfg (InputFromWorkTape.classifyCfg firstCfg.inputPos cfg boundary))) := by
  apply Cfg.ext
  · cases hs : cfg.state <;>
      simp [embedSecond, classifyCfg, Sequential.right, Cfg.withState, inputLift,
        ExtendTapes.embed, InputFromWorkTape.embed, InputFromWorkTape.classifyCfg, hs]
  · rfl
  · exact (extend_input _ _ _ _ _).symm
  · exact (extend_input _ _ _ _ _).symm
  · rfl

/-- Simulation of the second machine, at two composite steps per native step. -/
lemma runFrom_secondPhase (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    (cfg : Cfg k₁ Symbol State₁ secondInput) (n : ℕ) :
    (comp tm₀ tm₁).runFrom (embedSecond tm₀ tm₁ firstCfg cfg) (2 * n) =
      embedSecond tm₀ tm₁ firstCfg (tm₁.runFrom cfg n) := by
  rw [embedSecond_eq, comp, Sequential.runFrom_right, Sequential.runFrom_right]
  simp only [inputMachine, inputLift, ExtendTapes.runFrom_embed, InputFromWorkTape.runFrom_embed]
  exact (embedSecond_eq tm₀ tm₁ firstCfg _).symm

/-- Odd composite steps are the intermediate classifier configurations of the input substitution. -/
lemma runFrom_secondPhase_odd (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    (cfg : Cfg k₁ Symbol State₁ secondInput) (n : ℕ) :
    ∃ boundary, (comp tm₀ tm₁).runFrom (embedSecond tm₀ tm₁ firstCfg cfg) (2 * n + 1) =
      classifyCfg tm₀ tm₁ firstCfg (tm₁.runFrom cfg (n + 1)) boundary := by
  obtain ⟨boundary, h⟩ := InputFromWorkTape.runFrom_odd tm₁ firstCfg.inputPos cfg n
  refine ⟨boundary, ?_⟩
  rw [embedSecond_eq, comp, Sequential.runFrom_right, Sequential.runFrom_right]
  simp only [inputMachine, inputLift, ExtendTapes.runFrom_embed, h]
  exact (classifyCfg_eq tm₀ tm₁ firstCfg _ boundary).symm

/-- The initial classifier establishes the second machine's native initial configuration. -/
lemma step_classify_init (firstCfg : Cfg k₀ Symbol State₀ firstInput) :
    (comp tm₀ tm₁).step (classifyCfg tm₀ tm₁ firstCfg (tm₁.initCfg firstCfg.output) .right) =
      embedSecond tm₀ tm₁ firstCfg (tm₁.initCfg firstCfg.output) := by
  rw [classifyCfg_eq, comp, Sequential.step_right, Sequential.step_right]
  simp only [inputMachine, inputLift, ExtendTapes.step_embed, InputFromWorkTape.step_init]
  exact (embedSecond_eq tm₀ tm₁ firstCfg _).symm

end Turing.MultiTapeTM.Composition
