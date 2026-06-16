/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.HasTau

/-! # IsSimulation and Similarity

A simulation is a binary relation on the states of two `LTS`s: if two states `s₁` and `s2` are
related by a simulation, then `s2` can mimic all transitions of `s₁` in their respective LTSs.
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

- `s₁ ≤[lts₁, lts₂] s₂`: the states `s₁` and `s2` are similar under `lts₁` and `lts₂`.
- `s₁ ≤≥[lts₁, lts₂] s2`: the states `s₁` and `s2` are simulation equivalent under `lts₁` and
`lts₂`.

## Main statements

- `HomSimulationEquiv.eqv`: homogeneous simulation equivalence is an equivalence relation.

-/

@[expose] public section

namespace Cslib.LTS

universe u v

section Simulation

/-- A relation is a simulation if, whenever it relates two states in an lts,
any transition originating from the first state is mimicked by a transition from the second state
and the reached derivatives are themselves related. -/
def IsSimulation (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) (r : State₁ → State₂ → Prop) :
    Prop :=
  ∀ s₁ s2, r s₁ s2 → ∀ μ s₁', lts₁.Tr s₁ μ s₁' → ∃ s2', lts₂.Tr s2 μ s2' ∧ r s₁' s2'

/-- A homogeneous simulation is a simulation where the underlying LTSs are the same. -/
abbrev IsHomSimulation (lts : LTS State Label) := IsSimulation lts lts

/-- Two states are similar if they are related by some simulation. -/
def Similarity (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) : State₁ → State₂ → Prop :=
  fun s₁ s2 =>
    ∃ r : State₁ → State₂ → Prop, r s₁ s2 ∧ IsSimulation lts₁ lts₂ r

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
  intro s₁ s2 hrc μ s₁' htr
  rcases hrc with ⟨sb, hr1, hr2⟩
  obtain ⟨s₁'', h1'tr, h1'⟩ := h1 s₁ sb hr1 μ s₁' htr
  obtain ⟨s2'', h2'tr, h2'⟩ := h2 sb s2 hr2 μ s₁'' h1'tr
  use s2'', h2'tr, s₁'', h1', h2'

/-- Similarity is transitive. -/
theorem Similarity.trans (h1 : s₁ ≤[lts₁,lts₂] s2) (h2 : s2 ≤[lts₂,lts₃] s₃) :
    s₁ ≤[lts₁,lts₃] s₃ := by
  obtain ⟨r1, hr1, hr1s⟩ := h1
  obtain ⟨r2, hr2, hr2s⟩ := h2
  use! Relation.Comp r1 r2, s2, hr1, hr2, IsSimulation.comp r1 r2 hr1s hr2s

theorem IsSimulation.sup (hr : IsSimulation lts₁ lts₂ r)
    (hs : IsSimulation lts₁ lts₂ s) : IsSimulation lts₁ lts₂ (r ⊔ s) := by
  rintro s₁ s₂ (hrel | hrel) μ s₁' htr
  · obtain ⟨s₂', htr', hrel'⟩ := hr s₁ s₂ hrel μ s₁' htr
    use s₂', htr', Or.inl hrel'
  · obtain ⟨s₂', htr', hrel'⟩ := hs s₁ s₂ hrel μ s₁' htr
    use s₂', htr', Or.inr hrel'

theorem IsSimulation.sim_trace (hr : IsSimulation lts₁ lts₂ r) (hrel : r s₁ s₂) :
    ∀ μs s₁', lts₁.MTr s₁ μs s₁' → ∃ s₂', lts₂.MTr s₂ μs s₂' ∧ r s₁' s₂' := by
  intro μs s₁' hmtr
  induction μs generalizing s₁ s₂ with
  | nil =>
    obtain rfl := hmtr.nil_eq
    exact ⟨s₂, MTr.refl, hrel⟩
  | cons μ μs ih =>
    cases hmtr
    case stepL s₁'' htr hmtr =>
      obtain ⟨s₂'', htr₂, hrel'⟩: ∃ s2', lts₂.Tr s₂ μ s2' ∧ r s₁'' s2' := hr _ _ hrel μ s₁'' htr
      obtain ⟨s₂', hmtr₂, hrel'⟩ := ih hrel' hmtr
      use s₂', hmtr₂.stepL htr₂, hrel'

/-- Simulation equivalence relates all states `s₁` and `s2` such that `s₁ ≤[lts₁ lts₂] s2` and
`s2 ≤[lts₂ lts₁] s₁`. -/
def SimulationEquiv (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    State₁ → State₂ → Prop :=
  fun s₁ s2 =>
    s₁ ≤[lts₁, lts₂] s2 ∧ s2 ≤[lts₂, lts₁] s₁

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
theorem SimulationEquiv.symm {s₁ s2 : State} (h : s₁ ≤≥[lts₁,lts₂] s2) : s2 ≤≥[lts₂, lts₁] s₁ := by
  grind [SimulationEquiv]

/-- Simulation equivalence is transitive. -/
theorem SimulationEquiv.trans (h1 : s₁ ≤≥[lts₁,lts₂] s2) (h2 : s2 ≤≥[lts₂,lts₃] s₃) :
    s₁ ≤≥[lts₁,lts₃] s₃ := by
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

/-- Utility theorem for following internal transitions along a saturated lts. -/
lemma IsSimulation.follow_internal [HasTau Label] {lts₁ : LTS State₁ Label}
    {lts₂ : LTS State₂ Label} (h : IsSimulation lts₁ lts₂.saturate r) (hr : r s₁ s₂)
    (hstr : lts₁.τSTr s₁ s₁') : ∃ s₂', lts₂.τSTr s₂ s₂' ∧ r s₁' s₂' := by
  induction hstr
  case refl =>
    use s₂, .refl
  case tail sb hrsb htrsb ih1 ih2 =>
    obtain ⟨sb2, htrsb2, hrb⟩ := ih2
    have ⟨sb2', htrsb2', hrb'⟩ := h _ _ hrb HasTau.τ _ ih1
    use sb2', htrsb2.trans (lts₂.sTr_τSTr.mp htrsb2')

/-- If the right-hand lts is saturated, a simulation lifts along saturating the left-hand lts. -/
theorem IsSimulation.isSimulation_saturate_left [HasTau Label] {lts₁ : LTS State₁ Label}
    {lts₂ : LTS State₂ Label} (h : IsSimulation lts₁ lts₂.saturate r) :
    IsSimulation lts₁.saturate lts₂.saturate r := by
  intro s₁ s₂ hr μ s₁' h
  cases h
  case refl =>
    use s₂, .refl, hr
  case tr sb sb' hstr1 htr hstr2 =>
    obtain ⟨sb1, hstr1b, hrb⟩ := IsSimulation.follow_internal h hr hstr1
    obtain ⟨sb2', hstr1b', hrb'⟩ := h _ _ hrb μ _ htr
    obtain ⟨s₁', hstr1', hrb2⟩ := IsSimulation.follow_internal h hrb' hstr2
    rw [←sTr_τSTr] at hstr1' hstr1b
    use s₁', STr.comp lts₂ hstr1b hstr1b' hstr1', hrb2

/-- Simulation is preserved by removing transitions on the left, and adding transitions on the
right. -/
theorem IsSimulation.mono (h₁ : lts₁'.Tr ≤ lts₁.Tr) (h₂ : lts₂.Tr ≤ lts₂'.Tr)
    (h : IsSimulation lts₁ lts₂ r) : IsSimulation lts₁' lts₂' r := by
  intro s₁ s₂ hr μ s₁' htr
  obtain ⟨s₂', htr', hr'⟩ := h s₁ s₂ hr μ s₁' (h₁ _ _ _ htr)
  use s₂', h₂ _ _ _ htr', hr'

end Simulation

end Cslib.LTS
