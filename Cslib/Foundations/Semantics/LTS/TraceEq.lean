/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Simulation

@[expose] public section

/-!
# Trace Equivalence

Definitions and results on trace equivalence for `LTS`s.

## Main definitions

- `LTS.traces`: the set of traces of a state.
- `TraceEq s₁ s₂`: `s₁` and `s₂` are trace equivalent, i.e., they have the same sets of traces.

## Notations

- `s₁ ~tr[lts] s₂`: the states `s₁` and `s₂` are trace equivalent in `lts`.

## Main statements

- `TraceEq.eqv`: trace equivalence is an equivalence relation (see `Equivalence`).
- `TraceEq.deterministic_sim`: in any deterministic `LTS`, trace equivalence is a simulation.

-/

namespace Cslib.LTS

/-- The traces of a state `s` is the set of all lists of labels `μs` such that there is a multi-step
transition labelled by `μs` originating from `s`. -/
def traces (lts : LTS State Label) (s : State) := { μs : List Label | ∃ s', lts.MTr s μs s' }

/-- If there is a multi-step transition from `s` labelled by `μs`, then `μs` is in the traces of
`s`. -/
theorem traces_in {lts : LTS State Label} (h : lts.MTr s μs s') : μs ∈ lts.traces s := by exists s'

/-- Two states are trace equivalent if they have the same set of traces. -/
def TraceEq (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (s₁ : State₁) (s₂ : State₂) :=
  lts₁.traces s₁ = lts₂.traces s₂

/--
Notation for trace equivalence.

Differently from standard pen-and-paper presentations, we require the LTSs to be mentioned
explicitly.
-/
scoped notation s " ~tr[" lts₁ "," lts₂ "] " s' => TraceEq lts₁ lts₂ s s'

/-- Homogeneous trace equivalence compares states on the same LTS. -/
abbrev HomTraceEq (lts : LTS State Label) := TraceEq lts lts

/-- Notation for homogeneous trace equivalence. -/
scoped notation s:max " ~tr[" lts "] " s':max => HomTraceEq lts s s'

/-- Homogeneous trace equivalence is reflexive. -/
theorem HomTraceEq.refl (s : State) : s ~tr[lts] s := by
  simp only [TraceEq]

/-- Trace equivalence is symmetric. -/
theorem TraceEq.symm (h : s₁ ~tr[lts₁,lts₂] s₂) : s₂ ~tr[lts₂,lts₁] s₁ := by
  simp only [TraceEq] at h
  simp only [TraceEq]
  rw [h]

/-- Trace equivalence is transitive. -/
theorem TraceEq.trans (h1 : s₁ ~tr[lts₁,lts₂] s₂) (h2 : s₂ ~tr[lts₂,lts₃] s₃) :
    s₁ ~tr[lts₁,lts₃] s₃ := by
  simp only [TraceEq] at *
  rw [h1, h2]

/-- Homogeneous trace equivalence is an equivalence relation. -/
theorem HomTraceEq.eqv : Equivalence (· ~tr[lts] ·) where
  refl := HomTraceEq.refl
  symm := TraceEq.symm
  trans := TraceEq.trans

/-- `calc` support for simulation equivalence. -/
instance : Trans (TraceEq lts₁ lts₂) (TraceEq lts₂ lts₃) (TraceEq lts₁ lts₃) where
  trans := TraceEq.trans

/-- In deterministic LTSs, trace equivalence is a simulation. -/
theorem TraceEq.deterministic_isSimulation {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [hdet₁ : lts₁.Deterministic] [hdet₂ : lts₂.Deterministic] :
    IsSimulation lts₁ lts₂ (TraceEq lts₁ lts₂) := by
  intro s₁ s₂ h μ s₁' htr1
  have hmtr1 := MTr.single lts₁ htr1
  have hin := traces_in hmtr1
  rw [h] at hin
  obtain ⟨s₂', hmtr2⟩ := hin
  exists s₂'
  constructor
  · apply MTr.single_invert lts₂ _ _ _ hmtr2
  · simp only [TraceEq, traces]
    funext μs'
    simp only [eq_iff_iff]
    simp only [setOf]
    constructor
    case mp =>
      intro hmtr1'
      obtain ⟨s₁'', hmtr1'⟩ := hmtr1'
      have hmtr1comp := MTr.comp lts₁ hmtr1 hmtr1'
      have hin := traces_in hmtr1comp
      rw [h] at hin
      obtain ⟨s', hmtr2'⟩ := hin
      cases hmtr2'
      case stepL s₂'' htr2 hmtr2' =>
        exists s'
        have htr2' := MTr.single_invert lts₂ _ _ _ hmtr2
        have hdets₂ := hdet₂.deterministic s₂ μ s₂' s₂'' htr2' htr2
        rw [hdets₂]
        exact hmtr2'
    case mpr =>
      intro hmtr2'
      obtain ⟨s₂'', hmtr2'⟩ := hmtr2'
      have hmtr2comp := MTr.comp lts₂ hmtr2 hmtr2'
      have hin := traces_in hmtr2comp
      rw [← h] at hin
      obtain ⟨s', hmtr1'⟩ := hin
      cases hmtr1'
      case stepL s₁'' htr1 hmtr1' =>
        exists s'
        have htr1' := MTr.single_invert lts₁ _ _ _ hmtr1
        have hdets₁ := hdet₁.deterministic s₁ μ s₁' s₁'' htr1' htr1
        rw [hdets₁]
        exact hmtr1'

end Cslib.LTS
