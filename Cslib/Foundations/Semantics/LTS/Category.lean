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

variable {State Label State₁ State₂ State₃ Label₁ Label₂ Label₃ : Type}
variable (lts₁ : LTS State₁ Label₁)
variable (lts₂ : LTS State₂ Label₂)
variable (lts₃ : LTS State₃ Label₃)

/-!
# Category of Labelled Transition Systems
-/

/-! ## Definition of LTS morphism -/

/-- A morphism between two labelled transition systems, consisting of a function on states, a
function on labels, and a proof that transitions are preserved. -/
structure LTS.Morphism (lts₁ : LTS State₁ Label₁) (lts₂ : LTS State₂ Label₂) : Type where
  toFun : State₁ → State₂
  labelMap : Label₁ → Label₂
  fun_preserves_transitions : (s s' : State₁)
                            → (l : Label₁)
                            → lts₁.Tr s l s'
                            → lts₂.Tr (toFun s) (labelMap l) (toFun s')

/-- The identity LTS morphism. -/
def LTS.Morphism.id (lts : LTS State Label) : LTS.Morphism lts lts :=
  { toFun                     := _root_.id
  , labelMap                  := _root_.id
  , fun_preserves_transitions := fun _ _ _ h => h
  }

/-- Composition of LTS morphisms. -/
def LTS.Morphism.comp :
    LTS.Morphism lts₁ lts₂ → LTS.Morphism lts₂ lts₃ → LTS.Morphism lts₁ lts₃ :=
  fun ⟨f, μ, p⟩ ⟨g, ν, q⟩ =>
    let r := by intros _ _ _ h
                apply q
                apply p
                exact h
    ⟨g ∘ f, ν ∘ μ, r⟩

/-! ## LTSs and LTS morphisms form a category -/

/-- The notion of labelled transition system -/
structure BundledLTS where
  State : Type u
  Label : Type v
  lts : LTS State Label

/- Remark: I do not like the name 'bundled LTS'; and LTS is already the bundled notion.
   The name `LTS` for the transition relation on a fixed set of states and
   labels is what is confusing here. I propose to change that to `LTS-Structure`.
-/

/-- `LTS.Morphism` provides a category structure on bundled LTSs. -/
instance : CategoryTheory.CategoryStruct BundledLTS where
  Hom X Y               := LTS.Morphism X.lts Y.lts
  id X                  := LTS.Morphism.id X.lts
  comp {X} {Y} {Z} f g  := LTS.Morphism.comp X.lts Y.lts Z.lts f g

/-- Proof that the above structure actually forms a category. -/
instance : CategoryTheory.Category BundledLTS where
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
