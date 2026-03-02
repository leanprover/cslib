/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayberk Tosun
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.CategoryTheory.Category.Basic
open Cslib

@[expose] public section

variable {State Label State₃ Label₃ State₁ State₂ Label₁ Label₂ : Type}
variable (lts₁ : LTS State₁ Label₁)
variable (lts₂ : LTS State₂ Label₂)
variable (lts₃ : LTS State₃ Label₃)

/-!
# Category of Labelled Transition Systems
-/

/-- A morphism between two labelled transition systems, consisting of a function on states, a
function on labels, and a proof that transitions are preserved. -/
structure LTSMorphism (lts₁ : LTS State₁ Label₁) (lts₂ : LTS State₂ Label₂) : Type where
  toFun : State₁ → State₂
  lam   : Label₁ → Label₂
  fun_preserves_transitions : (s s' : State₁)
                            → (l : Label₁)
                            → lts₁.Tr s l s'
                            → lts₂.Tr (toFun s) (lam l) (toFun s')

/-- The identity LTS morphism. -/
def LTSMorphism.id (lts : LTS State Label) : LTSMorphism lts lts :=
  { toFun                     := _root_.id
  , lam                       := _root_.id
  , fun_preserves_transitions := fun _ _ _ h => h
  }

/-- Composition of LTS morphisms. -/
def LTSMorphism.comp : LTSMorphism lts₁ lts₂ → LTSMorphism lts₂ lts₃ → LTSMorphism lts₁ lts₃ :=
  fun ⟨f, μ, p⟩ ⟨g, ν, q⟩ =>
    let r := by intros _ _ _ h
                apply q
                apply p
                exact h
    ⟨g ∘ f, ν ∘ μ, r⟩

/-- `LTSMorphism` provides a category structure on the `LTS` type. -/
instance {State Label : Type} : CategoryTheory.CategoryStruct (LTS State Label) :=
  { Hom                       := LTSMorphism
  , id                        := LTSMorphism.id
  , comp {lts₁} {lts₂} {lts₃} := LTSMorphism.comp lts₁ lts₂ lts₃
  }

instance {State Label : Type} : CategoryTheory.Category (LTS State Label) where
  id_comp := by
    intro _ _ f
    cases f
    rfl
  comp_id := by
    intro _ _ f
    cases f
    rfl
  assoc := by
    intro _ _ _ _ f g h
    cases f
    cases g
    cases h
    rfl
