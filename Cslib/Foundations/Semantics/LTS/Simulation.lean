/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

@[expose] public section

/-! # IsSimulation and Similarity

A simulation is a binary relation on the states of two `LTS`s: if two states `s1` and `s2` are
related by a simulation, then `s2` can mimic all transitions of `s1` in their respective LTSs.
Furthermore, the derivatives reaches through these transitions remain related by the simulation.

Similarity is the largest simulation: given an `LTS`, it relates any two states that are related
by a simulation for that LTS.

The module provides abbreviations for the homogeneous case of comparing states in the same LTS.

For an introduction to theory of simulation, we refer to [Sangiorgi2011].

## Main definitions

- `IsSimulation lts₁ lts₂ r`: the relation `r` on the states of `lts₁` and `lts₂` is a simulation.
- `Similarity lts₁ lts₂` is the binary relation that relates any two states related by some
simulation on `lts₁` and `lts₂`.
- `SimulationEquiv lts₁ lts₂` is the binary relation on the states of `lts₁` and `lts₂` that relates
any two states similar to each other.

## Notations

- `s1 ≤[lts₁, lts₂] s2`: the states `s1` and `s2` are similar under `lts₁` and `lts₂`.
- `s1 ≤≥[lts₁, lts₂] s2`: the states `s1` and `s2` are simulation equivalent under `lts₁` and
`lts₂`.

## Main statements

- `HomSimulationEquiv.eqv`: homogeneous simulation equivalence is an equivalence relation.

-/

namespace Cslib.LTS

universe u v

section Simulation

/-- A relation is a simulation if, whenever it relates two states in an lts,
any transition originating from the first state is mimicked by a transition from the second state
and the reached derivatives are themselves related. -/
def IsSimulation (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) (r : State₁ → State₂ → Prop) :
    Prop :=
  ∀ s1 s2, r s1 s2 → ∀ μ s1', lts₁.Tr s1 μ s1' → ∃ s2', lts₂.Tr s2 μ s2' ∧ r s1' s2'

/-- A homogeneous simulation is a simulation where the underlying LTSs are the same. -/
abbrev IsHomSimulation (lts : LTS State Label) := IsSimulation lts lts

/-- Two states are similar if they are related by some simulation. -/
def Similarity (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) : State₁ → State₂ → Prop :=
  fun s1 s2 =>
    ∃ r : State₁ → State₂ → Prop, r s1 s2 ∧ IsSimulation lts₁ lts₂ r

/--
Notation for similarity.

Differently from standard pen-and-paper presentations, we require the lts to be mentioned
explicitly.
-/
scoped notation s:max " ≤[" lts₁ "," lts₂ "] " s':max => Similarity lts₁ lts₂ s s'

/-- Homogeneous similarity is similarity where the underlying LTSs are the same. -/
abbrev HomSimilarity (lts : LTS State Label) := Similarity lts lts

/-- Notation for homogeneous similarity. -/
scoped notation s:max " ≤[" lts "] " s':max => HomSimilarity lts s s'

/-- Homogeneous similarity is reflexive. -/
theorem HomSimilarity.refl (s : State) : s ≤[lts] s := by
  exists Eq
  grind [IsSimulation]

/-- The composition of two simulations is a simulation. -/
theorem IsSimulation.comp
    (r1 : State₁ → State₂ → Prop)
    (r2 : State₂ → State₃ → Prop)
    (h1 : IsSimulation lts₁ lts₂ r1) (h2 : IsSimulation lts₂ lts₃ r2) :
    IsSimulation lts₁ lts₃ (Relation.Comp r1 r2) := by
  simp_all only [IsSimulation]
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
  · exists s1''

/-- Similarity is transitive. -/
theorem Similarity.trans (h1 : s1 ≤[lts₁,lts₂] s2) (h2 : s2 ≤[lts₂,lts₃] s3) :
    s1 ≤[lts₁,lts₃] s3 := by
  obtain ⟨r1, hr1, hr1s⟩ := h1
  obtain ⟨r2, hr2, hr2s⟩ := h2
  exists Relation.Comp r1 r2
  constructor
  case left =>
    exists s2
  case right =>
    apply IsSimulation.comp r1 r2 hr1s hr2s

/-- Simulation equivalence relates all states `s1` and `s2` such that `s1 ≤[lts₁ lts₂] s2` and
`s2 ≤[lts₂ lts₁] s1`. -/
def SimulationEquiv (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    State₁ → State₂ → Prop :=
  fun s1 s2 =>
    s1 ≤[lts₁, lts₂] s2 ∧ s2 ≤[lts₂, lts₁] s1

/--
Notation for simulation equivalence.
-/
scoped notation s:max " ≤≥[" lts₁ "," lts₂ "] " s':max => SimulationEquiv lts₁ lts₂ s s'

/-- Homogeneous simulation equivalence. -/
abbrev HomSimulationEquiv (lts : LTS State Label) := SimulationEquiv lts lts

/-- Notation for homogeneous simulation equivalence. -/
scoped notation s:max " ≤≥[" lts "] " s':max => HomSimulationEquiv lts s s'

/-- Homogeneous simulation equivalence is reflexive. -/
theorem HomSimulationEquiv.refl (s : State) : s ≤≥[lts] s := by
  grind [SimulationEquiv, HomSimilarity.refl]

/-- Simulation equivalence is symmetric. -/
theorem SimulationEquiv.symm {s1 s2 : State} (h : s1 ≤≥[lts₁,lts₂] s2) : s2 ≤≥[lts₂, lts₁] s1 := by
  grind [SimulationEquiv]

/-- Simulation equivalence is transitive. -/
theorem SimulationEquiv.trans (h1 : s1 ≤≥[lts₁,lts₂] s2) (h2 : s2 ≤≥[lts₂,lts₃] s3) :
    s1 ≤≥[lts₁,lts₃] s3 := by
  grind [SimulationEquiv, Similarity.trans]

/-- Homogeneous simulation equivalence is an equivalence relation. -/
theorem HomSimulationEquiv.eqv : Equivalence (· ≤≥[lts] ·) where
  refl := HomSimulationEquiv.refl
  symm := SimulationEquiv.symm
  trans := SimulationEquiv.trans

/-- `calc` support for simulation equivalence. -/
instance :
  Trans
    (SimulationEquiv lts₁ lts₂)
    (SimulationEquiv lts₂ lts₃)
    (SimulationEquiv lts₁ lts₃) where
  trans := SimulationEquiv.trans

end Simulation

end Cslib.LTS
