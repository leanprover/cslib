/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToWorkTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromWorkTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Rewind
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# Composition of deterministic multi-tape Turing machines

The composite redirects the first machine's output to an intermediate work tape, rewinds it,
and simulates the second machine with that tape as its input. Work tapes occupy disjoint blocks.
A classification step after each simulated input move restores the native boundary behavior.
Both machines use the same alphabet; no extra tape symbols are required.

`comp` is the executable construction. The `Composition` namespace also contains the
configuration embeddings used by the simulation proofs.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k₀ k₁ : ℕ}
variable {Symbol State₀ State₁ : Type*}

/-- Number of work tapes used by the composition of a `k₀`- and a `k₁`-tape machine. -/
abbrev compositionTapeCount (k₀ k₁ : ℕ) := k₀ + 1 + k₁

/-- Physical coordinate of work tape `i` of the first machine. -/
def compositionFirstTapeIdx (k₁ : ℕ) (i : Fin k₀) : Fin (compositionTapeCount k₀ k₁) :=
  i.castSucc.castAdd k₁

/-- Physical coordinate of the tape containing the intermediate output. -/
def compositionIntermediateTapeIdx (k₀ k₁ : ℕ) : Fin (compositionTapeCount k₀ k₁) :=
  (Fin.last k₀).castAdd k₁

/-- Physical coordinate of work tape `i` of the second machine. -/
def compositionSecondTapeIdx (k₀ k₁ : ℕ) (i : Fin k₁) :
    Fin (compositionTapeCount k₀ k₁) :=
  Fin.natAdd (k₀ + 1) i

@[simp]
lemma compositionFirstTapeIdx_val (k₁ : ℕ) (i : Fin k₀) :
    (compositionFirstTapeIdx k₁ i).val = i.val := rfl

@[simp]
lemma compositionIntermediateTapeIdx_val (k₀ k₁ : ℕ) :
    (compositionIntermediateTapeIdx k₀ k₁).val = k₀ := rfl

@[simp]
lemma compositionSecondTapeIdx_val (k₀ : ℕ) (i : Fin k₁) :
    (compositionSecondTapeIdx k₀ k₁ i).val = k₀ + 1 + i.val := rfl

/-- States of the three sequential phases: output, rewind, and virtual-input execution. -/
abbrev CompositionState (State₀ State₁ : Type*) := State₀ ⊕ (RewindState ⊕ InputState State₁)

/-- Assemble the first work-tape block, the intermediate tape, and the second block.
The same layout is used for tape contents and head positions. -/
@[simp]
def Composition.tapes {α : Type*} (first : Fin k₀ → α) (middle : α) (second : Fin k₁ → α)
    (i : Fin (compositionTapeCount k₀ k₁)) : α :=
  if h : i.val < k₀ then first ⟨i, h⟩
  else if hmiddle : i.val = k₀ then middle
  else second ⟨i.val - (k₀ + 1), by have := i.isLt; simp only [compositionTapeCount] at *; omega⟩

namespace Composition

/-- Place the first machine and its output tape before the second work-tape block. -/
def outputEmbedding (k₀ k₁ : ℕ) : Fin (k₀ + 1) ↪ Fin (compositionTapeCount k₀ k₁) :=
  ⟨Fin.castAdd k₁, Fin.castAdd_injective (k₀ + 1) k₁⟩

/-- Place the virtual input before the second machine's work tapes. -/
def inputEmbedding (k₀ k₁ : ℕ) : Fin (k₁ + 1) ↪ Fin (compositionTapeCount k₀ k₁) :=
  ⟨fun i => ⟨k₀ + i.val, by have := i.isLt; simp only [compositionTapeCount]; omega⟩,
    fun i j h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)⟩

@[simp]
lemma inputEmbedding_val (i : Fin (k₁ + 1)) :
    (inputEmbedding k₀ k₁ i).val = k₀ + i.val := rfl

/-- The first machine, with output redirected and the second tape block left idle. -/
def outputMachine (tm₀ : MultiTapeTM k₀ Symbol State₀) (k₁ : ℕ) :=
  tm₀.outputToWorkTape.extendTapes (outputEmbedding k₀ k₁)

/-- The second machine, with virtual input and the first tape block left idle. -/
def inputMachine (k₀ : ℕ) (tm₁ : MultiTapeTM k₁ Symbol State₁) :=
  tm₁.inputFromWorkTape.extendTapes (inputEmbedding k₀ k₁)

end Composition

/-- Compose functions by redirecting output, rewinding it, then using it as the next input. -/
def comp (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁) :
    MultiTapeTM (compositionTapeCount k₀ k₁) Symbol (CompositionState State₀ State₁) :=
  (Composition.outputMachine tm₀ k₁).seq
    ((rewind (.work (compositionIntermediateTapeIdx k₀ k₁))).seq
      (Composition.inputMachine k₀ tm₁))

namespace Composition

/-- Embed a first-machine configuration into the first phase of the composite machine. -/
def embedFirst
    (_tm₀ : MultiTapeTM k₀ Symbol State₀)
    (_tm₁ : MultiTapeTM k₁ Symbol State₁)
    {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) :
    Cfg (compositionTapeCount k₀ k₁) Symbol (CompositionState State₀ State₁) input where
  state := match cfg.state with
    | some q => some (.inl q)
    | none => some (.inr (.inl .start))
  inputPos := cfg.inputPos
  workTapes := tapes cfg.workTapes (listTape cfg.output) (fun _ _ => none)
  workTapePos := tapes cfg.workTapePos cfg.output.length (fun _ => 0)
  output := []

/-- Embed a second-machine configuration into the second phase of the composite machine. -/
def embedSecond
    (_tm₀ : MultiTapeTM k₀ Symbol State₀)
    (_tm₁ : MultiTapeTM k₁ Symbol State₁)
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput) :
    Cfg (compositionTapeCount k₀ k₁) Symbol
      (CompositionState State₀ State₁) firstInput where
  state := match secondCfg.state with
    | some q => some (.inr (.inr (.run q (InputFromWorkTape.inputMode secondCfg.inputPos))))
    | none => none
  inputPos := firstCfg.inputPos
  workTapes := tapes firstCfg.workTapes (listTape secondInput) secondCfg.workTapes
  workTapePos := tapes firstCfg.workTapePos
    (InputFromWorkTape.virtualInputPos secondCfg.inputPos) secondCfg.workTapePos
  output := secondCfg.output

/-- The intermediate configuration between the moving and classifying halves of a simulated
second-machine step. -/
def classifyCfg
    (_tm₀ : MultiTapeTM k₀ Symbol State₀)
    (_tm₁ : MultiTapeTM k₁ Symbol State₁)
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (boundary : InputBoundary) :
    Cfg (compositionTapeCount k₀ k₁) Symbol
      (CompositionState State₀ State₁) firstInput :=
  { embedSecond _tm₀ _tm₁ firstCfg secondCfg with
    state := secondCfg.state.map fun q => (.inr (.inr (.classify q boundary))) }

/-- A first-phase boundary configuration with a chosen control state and intermediate head
position. -/
def intermediateCfg
    (_tm₀ : MultiTapeTM k₀ Symbol State₀)
    (_tm₁ : MultiTapeTM k₁ Symbol State₁)
    {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input)
    (state : CompositionState State₀ State₁)
    (pos : ℤ) :
    Cfg (compositionTapeCount k₀ k₁) Symbol (CompositionState State₀ State₁) input :=
  { embedFirst _tm₀ _tm₁ cfg with
    state := some state
    workTapePos := fun i =>
      if i.val = k₀ then pos
      else (embedFirst _tm₀ _tm₁ cfg).workTapePos i }

end Composition

end Turing.MultiTapeTM
