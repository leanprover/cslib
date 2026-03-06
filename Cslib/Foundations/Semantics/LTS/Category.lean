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

/-!
# Category of Labelled Transition Systems
-/

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
  labelMap : lts₁.Label → lts₂.Label
  labelMap_tr : (s s' : lts₁.State)
                            → (l : lts₁.Label)
                            → lts₁.lts.Tr s l s'
                            → lts₂.lts.Tr (stateMap s) (labelMap l) (stateMap s')

/-- The identity LTS morphism. -/
def LTS.Morphism.id (lts : LTSCat) : LTS.Morphism lts lts where
  stateMap := _root_.id
  labelMap := _root_.id
  labelMap_tr := fun _ _ _ h => h

/-- Composition of LTS morphisms. -/
def LTS.Morphism.comp {lts₁ lts₂ lts₃ : LTSCat} :
    LTS.Morphism lts₁ lts₂ → LTS.Morphism lts₂ lts₃ → LTS.Morphism lts₁ lts₃ :=
  fun ⟨f, μ, p⟩ ⟨g, ν, q⟩ =>
    let r := by
      intros _ _ _ h
      apply q
      apply p
      exact h
    ⟨g ∘ f, ν ∘ μ, r⟩

/-- Proof that the above structure actually forms a category. -/
instance : CategoryTheory.Category LTSCat where
  Hom lts₁ lts₂ := LTS.Morphism lts₁ lts₂
  id lts := LTS.Morphism.id lts
  comp {lts₁} {lts₂} {lts₃} f g := @LTS.Morphism.comp lts₁ lts₂ lts₃ f g
  id_comp := by intro _ _ f
                cases f
                rfl
  comp_id := by intro _ _ f
                cases f
                rfl
  assoc := by intro _ _ _ _ f g h
              cases f
              cases g
              cases h
              rfl
