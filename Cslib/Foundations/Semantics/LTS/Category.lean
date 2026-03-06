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

variable {State Label : Type}

/-!
# Category of Labelled Transition Systems
-/

/-! ## LTSs and LTS morphisms form a category -/

/-- The notion of labelled transition system -/
structure LTSCat where
  State : Type u
  Label : Type v
  lts : LTS State Label

/- Remark: I do not like the name 'bundled LTS'; and LTS is already the bundled notion. The name
   `LTS` for the transition relation on a fixed set of states and labels is what is confusing here.
    I propose to change that to `LTS-Structure` and call the above `LTS`.
-/

/-! ## Definition of LTS morphism -/

/--
A morphism between two labelled transition systems consists of a function on
states, a function on labels, and a proof that transitions are preserved.
-/
structure LTS.Morphism (lts₁ lts₂ : LTSCat) : Type where
  toFun : lts₁.State → lts₂.State
  labelMap : lts₁.Label → lts₂.Label
  fun_preserves_transitions : (s s' : lts₁.State)
                            → (l : lts₁.Label)
                            → lts₁.lts.Tr s l s'
                            → lts₂.lts.Tr (toFun s) (labelMap l) (toFun s')

/-- The identity LTS morphism. -/
def LTS.Morphism.id (lts : LTSCat) : LTS.Morphism lts lts :=
  { toFun                     := _root_.id
  , labelMap                  := _root_.id
  , fun_preserves_transitions := fun _ _ _ h => h
  }

/-- Composition of LTS morphisms. -/
def LTS.Morphism.comp {lts₁ lts₂ lts₃ : LTSCat} :
    LTS.Morphism lts₁ lts₂ → LTS.Morphism lts₂ lts₃ → LTS.Morphism lts₁ lts₃ :=
  fun ⟨f, μ, p⟩ ⟨g, ν, q⟩ =>
    let r := by intros _ _ _ h
                apply q
                apply p
                exact h
    ⟨g ∘ f, ν ∘ μ, r⟩

/-- `LTS.Morphism` provides a category structure on bundled LTSs. -/
instance : CategoryTheory.CategoryStruct LTSCat where
  Hom lts₁ lts₂         := LTS.Morphism lts₁ lts₂
  id lts                := LTS.Morphism.id lts
  comp {lts₁} {lts₂} {lts₃} f g := @LTS.Morphism.comp lts₁ lts₂ lts₃ f g

/-- Proof that the above structure actually forms a category. -/
instance : CategoryTheory.Category LTSCat where
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
