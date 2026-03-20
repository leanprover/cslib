/-
Copyright (c) 2026 Ayberk Tosun (Zeroth Research). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayberk Tosun
-/

module

public import Mathlib.CategoryTheory.Category.Basic
public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Control.Basic

@[expose] public section

namespace Cslib

universe u v

variable {State : Type u} {Label : Type v}

/-! # Category of Labelled Transition Systems

This file contains the definition of the category of labelled transition systems
as defined in Winskel and Nielsen's handbook chapter [WinskelNielsen1995].

## References

* [N. Winskel and M. Nielsen, *Models for concurrency*][WinskelNielsen1995]
-/

/--
We first define what is denoted Tran* in [WinskelNielsen1995]: the extension of
a transition relation with idle transitions.
-/
def lift (trans : State → Label → State → Prop) : State → (Option Label) → State → Prop :=
  fun s l s' => l.elim (s = s') (trans s · s')

/-! ## LTSs and LTS morphisms form a category -/

/--
The definition of labelled transition system (with the type of states and the
type of labels as part of the structure).
-/
structure LTSCat : Type (max u v + 1) where
  /-- Type of states of an LTS -/
  State : Type u
  /-- Type of labels of an LTS -/
  Label : Type v
  /-- Transition relation of an LTS -/
  lts : LTS State Label

/--
A morphism between two labelled transition systems consists of (1) a function on
states, (2) a partial function on labels, and a proof that (1) preserves each
transition along (2).
-/
structure LTS.Morphism (lts₁ lts₂ : LTSCat) : Type where
  /-- Mapping of states of `lts₁` to states of `lts₂` -/
  stateMap : lts₁.State → lts₂.State
  /-- Mapping of labels of `lts₁` to labels of `lts₂` -/
  labelMap : lts₁.Label → Option lts₂.Label
  /-- Stipulation that `stateMap` preserve transitions -/
  labelMap_tr (s s' : lts₁.State) (l : lts₁.Label) :
    lts₁.lts.Tr s l s' → lift lts₂.lts.Tr (stateMap s) (labelMap l) (stateMap s')

/-- The identity LTS morphism. -/
def LTS.Morphism.id (lts : LTSCat) : LTS.Morphism lts lts where
  stateMap := _root_.id
  labelMap := pure
  labelMap_tr := fun _ _ _ h => h

/-- Composition of LTS morphisms.

We use Kleisli composition to define this.
-/
def LTS.Morphism.comp {lts₁ lts₂ lts₃} (f : LTS.Morphism lts₁ lts₂) (g : LTS.Morphism lts₂ lts₃) :
    LTS.Morphism lts₁ lts₃ where
  stateMap := g.stateMap ∘ f.stateMap
  labelMap := f.labelMap >=> g.labelMap
  labelMap_tr s s' l h := by
    obtain ⟨f, μ, p⟩ := f
    obtain ⟨g, ν, q⟩ := g
    change ((μ l).bind ν).elim (g (f s) = g (f s')) _
    cases hμ : μ l with grind [lift]

/-- Finally, we prove that these form a category. -/
instance : CategoryTheory.Category LTSCat where
  Hom := LTS.Morphism
  id := LTS.Morphism.id
  comp := LTS.Morphism.comp
  comp_id _ := by
    simp only [LTS.Morphism.comp, LTS.Morphism.id]
    congr 1
    rw [fish_pure]
  assoc _ _ _ := by
    simp only [LTS.Morphism.comp]
    congr 1
    rw [fish_assoc]

end Cslib
