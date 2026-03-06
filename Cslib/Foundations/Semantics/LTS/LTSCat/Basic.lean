/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayberk Tosun
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.CategoryTheory.Category.Basic
open Cslib

universe u v

@[expose] public section

variable {State : Type u} {Label : Type v}

/-! # Category of Labelled Transition Systems

This file contains the definition of the category of labelled transition
systems, as defined in

## References

* [N. Winskel and M. Nielsen, *Models for concurrency*][WinskelNielsen1995]
-/

/--
We first define what Winskel and Nielsen denote Tran*: the extension
of an LTS with idle transitions.
-/
def lift (trans : State → Label → State → Prop) :
  State → (Option Label) → State → Prop :=
  fun s l s' => l.elim True (trans s · s')

/-! ## LTSs and LTS morphisms form a category -/

/-- The notion of labelled transition system -/
structure LTSCat : Type (max u v + 1) where
  State : Type u
  Label : Type v
  lts : LTS State Label

/-! ## Definition of LTS morphism -/

/--
A morphism between two labelled transition systems consists of a function on
states, a function on labels, and a proof that transitions are preserved.
-/
structure LTS.Morphism (lts₁ lts₂ : LTSCat) : Type where
  stateMap : lts₁.State → lts₂.State
  labelMap : lts₁.Label → Option lts₂.Label
  labelMap_tr (s s' : lts₁.State) (l : lts₁.Label) :
    lts₁.lts.Tr s l s' → lift lts₂.lts.Tr (stateMap s) (labelMap l) (stateMap s')

/-- The identity LTS morphism. -/
def LTS.Morphism.id (lts : LTSCat) : LTS.Morphism lts lts where
  stateMap := _root_.id
  labelMap := pure
  labelMap_tr := fun _ _ _ h => h

/-- Composition of LTS morphisms. -/
def LTS.Morphism.comp {lts₁ lts₂ lts₃ : LTSCat} :
    LTS.Morphism lts₁ lts₂ → LTS.Morphism lts₂ lts₃ → LTS.Morphism lts₁ lts₃ :=
  fun ⟨f, μ, p⟩ ⟨g, ν, q⟩ =>
    let r := by
      intro s s' l h
      have hp := p s s' l h
      change ((μ l).bind ν).elim True _
      cases hμ : μ l with
      | none => trivial
      | some m =>
        rw [hμ] at hp
        exact q (f s) (f s') m hp
    ⟨g ∘ f, μ >=> ν, r⟩

/-- Proof that the above structure actually forms a category. -/
instance : CategoryTheory.Category LTSCat where
  Hom lts₁ lts₂ := LTS.Morphism lts₁ lts₂
  id lts := LTS.Morphism.id lts
  comp {lts₁} {lts₂} {lts₃} f g := @LTS.Morphism.comp lts₁ lts₂ lts₃ f g
  id_comp := by
    intro _ _ f
    cases f
    rfl
  comp_id := by
    intro _ _ ⟨f, μ, p⟩
    simp only [LTS.Morphism.comp, LTS.Morphism.id]
    congr 1
    funext x
    change (μ x).bind pure = μ x
    cases μ x <;> rfl
  assoc := by
    intro _ _ _ _ ⟨f₁, μ₁, p₁⟩ ⟨f₂, μ₂, p₂⟩ ⟨f₃, μ₃, p₃⟩
    simp only [LTS.Morphism.comp]
    congr 1
    funext x
    change ((μ₁ x).bind μ₂).bind μ₃ = (μ₁ x).bind fun a => (μ₂ a).bind μ₃
    cases μ₁ x <;> rfl
