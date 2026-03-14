/-
Copyright (c) 2026 Henning Dieterichs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henning Dieterichs
-/

module

public import Cslib.Computability.CellularAutomata.Basic
public import Mathlib.Logic.Function.Iterate

@[expose] public section

/-! # Cellular Automata: Transition Operations

This file defines the core operations on cellular automata: stepping configurations forward in time,
projecting and embedding configurations, and functorial remapping of input/output alphabets.

## Main definitions

* `CellAutomaton.embedConfig` — lift an input configuration to the internal state space.
* `CellAutomaton.projectConfig` — project an internal configuration to the output alphabet.
* `CellAutomaton.next` — apply one step of the transition function.
* `CellAutomaton.step` — iterate the transition function `t` times.
* `CellAutomaton.comp` — the full space-time computation (project each step).
* `CellAutomaton.trace` — the output trace at position 0.
* `CellAutomaton.mapProject` — remap the output alphabet.
* `CellAutomaton.mapEmbed` — remap the input alphabet.
-/

namespace Cslib.CellularAutomata

namespace CellAutomaton

variable {α β Q : Type*} (C : CellAutomaton α β Q)

/-- Embed an input configuration into the internal state space. -/
def embedConfig (c : Config α) : Config Q :=
  fun p => C.embed (c p)

/-- Project an internal configuration to the output alphabet. -/
def projectConfig (c : Config Q) : Config β :=
  fun p => C.project (c p)

/-- Apply one step of the transition function across the entire configuration. -/
def next (c : Config Q) : Config Q :=
  fun p => C.δ (c (p - 1)) (c p) (c (p + 1))

/-- Iterate the transition function `t` times. -/
def step (c : Config Q) (t : ℕ) : Config Q :=
  C.next^[t] c

/-- The full space-time computation: project each step. -/
def comp (c : Config Q) : Trace (Config β) :=
  C.projectConfig ∘ C.step c

/-- The output trace at position 0. -/
def trace (c : Config α) : Trace β :=
  (C.comp (C.embedConfig c) · 0)

/-- Remap the output alphabet. -/
def mapProject {γ : Type*} (f : β → γ) : CellAutomaton α γ Q where
  δ := C.δ
  embed := C.embed
  project := f ∘ C.project

/-- Remap the input alphabet. -/
def mapEmbed {γ : Type*} (f : γ → α) : CellAutomaton γ β Q where
  δ := C.δ
  embed := C.embed ∘ f
  project := C.project

@[simp]
theorem mapProject_next {γ : Type*} (f : β → γ) (c : Config Q) :
    (C.mapProject f).next c = C.next c := rfl

@[simp]
theorem mapEmbed_next {γ : Type*} (f : γ → α) (c : Config Q) :
    (C.mapEmbed f).next c = C.next c := rfl

@[simp]
theorem step_zero (c : Config Q) : C.step c 0 = c := by
  simp [step]

@[simp]
theorem step_succ (c : Config Q) (t : ℕ) :
    C.step c (t + 1) = C.next (C.step c t) := by
  simp [step, Function.iterate_succ_apply']

@[simp]
theorem mapProject_step {γ : Type*} (f : β → γ) (c : Config Q) (t : ℕ) :
    (C.mapProject f).step c t = C.step c t := by
  induction t with
  | zero => simp [step]
  | succ t ih => simp only [step_succ, mapProject_next, ih]

@[simp]
theorem mapEmbed_step {γ : Type*} (f : γ → α) (c : Config Q) (t : ℕ) :
    (C.mapEmbed f).step c t = C.step c t := by
  induction t with
  | zero => simp [step]
  | succ t ih => simp only [step_succ, mapEmbed_next, ih]

end CellAutomaton

end Cslib.CellularAutomata
