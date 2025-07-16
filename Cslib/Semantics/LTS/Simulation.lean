/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Semantics.LTS.Basic
import Cslib.Utils.Rel

/-! # Simulation and Similarity

A simulation is a binary relation on the states of an `LTS`: if two states `s1` and `s2` are related by a simulation, then
`s2` can mimic all transitions of `s1`. Furthermore, the derivatives reaches through
these transitions remain related by the simulation.

Similarity is the largest simulation: given an `LTS`, it relates any two states that are related
by a bisimulation for that LTS.

For an introduction to theory of simulation, we refer to [Sangiorgi2011].

## Main definitions

- `Simulation lts r`: the relation `r` on the states of the LTS `lts` is a simulation.
- `Similarity lts` is the binary relation on the states of `lts` that relates any two states
related by some simulation on `lts`.
- `SimulationEquiv lts` is the binary relation on the states of `lts` that relates any two states
similar to each other.

## Notations

- `s1 ≤[lts] s2`: the states `s1` and `s2` are similar in the LTS `lts`.
- `s1 ≤≥[lts] s2`: the states `s1` and `s2` are simulation equivalent in the LTS `lts`.

## Main statements

- `SimulationEquiv.eqv`: simulation equivalence is an equivalence relation.

-/

universe u v

section Simulation

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/-- A relation is a simulation if, whenever it relates two states in an lts,
any transition originating from the first state is mimicked by a transition from the second state
and the reached derivatives are themselves related. -/
def Simulation (lts : LTS State Label) (r : Rel State State) : Prop :=
  ∀ s1 s2, r s1 s2 → ∀ μ s1', lts.Tr s1 μ s1' → ∃ s2', lts.Tr s2 μ s2' ∧ r s1' s2'

/-- Two states are similar if they are related by some simulation. -/
def Similarity (lts : LTS State Label) : Rel State State :=
  fun s1 s2 =>
    ∃ r : Rel State State, r s1 s2 ∧ Simulation lts r

/--
Notation for similarity.

Differently from standard pen-and-paper presentations, we require the lts to be mentioned
explicitly.
-/
notation s:max " ≤[" lts "] " s':max => Similarity lts s s'

/-- Similarity is reflexive. -/
theorem Similarity.refl (s : State) : s ≤[lts] s := by
  exists Rel.Id
  apply And.intro (by constructor)
  simp only [Simulation]
  intro s1 s2 hr μ s1' htr
  cases hr
  exists s1'
  apply And.intro htr (by constructor)

/-- The composition of two simulations is a simulation. -/
theorem Simulation.comp
  (r1 r2 : Rel State State) (h1 : Simulation lts r1) (h2 : Simulation lts r2) :
  Simulation lts (r1.comp r2) := by
  simp_all only [Simulation]
  intro s1 s2 hrc μ s1' htr
  rcases hrc with ⟨sb, hr1, hr2⟩
  specialize h1 s1 sb hr1 μ
  specialize h2 sb s2 hr2 μ
  have h1' := h1 s1' htr
  obtain ⟨s1'', h1'tr, h1'⟩ := h1'
  have h2' := h2 s1'' h1'tr
  obtain ⟨s2'', h2'tr, h2'⟩ := h2'
  exists s2''
  constructor
  · exact h2'tr
  · simp [Rel.comp]
    exists s1''

/-- Similarity is transitive. -/
theorem Similarity.trans (h1 : s1 ≤[lts] s2) (h2 : s2 ≤[lts] s3) : s1 ≤[lts] s3 := by
  obtain ⟨r1, hr1, hr1s⟩ := h1
  obtain ⟨r2, hr2, hr2s⟩ := h2
  exists r1.comp r2
  constructor
  case left =>
    simp only [Rel.comp]
    exists s2
  case right =>
    apply Simulation.comp lts r1 r2 hr1s hr2s

/-- Simulation equivalence relates all states `s1` and `s2` such that `s1 ≤[lts] s2` and
`s2 ≤[lts] s1`. -/
def SimulationEquiv (lts : LTS State Label) : Rel State State :=
  fun s1 s2 =>
    s1 ≤[lts] s2 ∧ s2 ≤[lts] s1

/--
Notation for simulation equivalence.
-/
notation s:max " ≤≥[" lts "] " s':max => SimulationEquiv lts s s'

/-- Simulation equivalence is reflexive. -/
theorem SimulationEquiv.refl (s : State) : s ≤≥[lts] s := by
  simp [SimulationEquiv]
  exists Rel.Id
  constructor; constructor
  simp only [Simulation]
  intro s1 s2 hr μ s1' htr
  cases hr
  exists s1'
  constructor; exact htr
  constructor

/-- Simulation equivalence is symmetric. -/
theorem SimulationEquiv.symm {s1 s2 : State} (h : s1 ≤≥[lts] s2) : s2 ≤≥[lts] s1 := by
  simp only [SimulationEquiv]
  simp only [SimulationEquiv] at h
  simp [h]

/-- Simulation equivalence is transitive. -/
theorem SimulationEquiv.trans {s1 s2 s3 : State} (h1 : s1 ≤≥[lts] s2) (h2 : s2 ≤≥[lts] s3) :
  s1 ≤≥[lts] s3 := by
  simp only [SimulationEquiv] at *
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  constructor
  case left =>
    obtain ⟨r1, hr1, hr1s⟩ := h1l
    obtain ⟨r2, hr2, hr2s⟩ := h2l
    exists r1.comp r2
    constructor
    · simp only [Rel.comp]
      exists s2
    · apply Simulation.comp lts r1 r2 hr1s hr2s
  case right =>
    obtain ⟨r1, hr1, hr1s⟩ := h1r
    obtain ⟨r2, hr2, hr2s⟩ := h2r
    exists r2.comp r1
    constructor
    · simp only [Rel.comp]
      exists s2
    · apply Simulation.comp lts r2 r1 hr2s hr1s

/-- Simulation equivalence is an equivalence relation. -/
theorem SimulationEquiv.eqv (lts : LTS State Label) :
  Equivalence (SimulationEquiv lts) := {
    refl := SimulationEquiv.refl lts
    symm := SimulationEquiv.symm lts
    trans := SimulationEquiv.trans lts
  }

end Simulation
