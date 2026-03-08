/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayberk Tosun
-/

module

public import Mathlib.CategoryTheory.Category.Basic
public import Cslib.Foundations.Semantics.LTS.Basic
open Cslib

universe u v

@[expose] public section

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
def lift (trans : State → Label → State → Prop) :
  State → (Option Label) → State → Prop :=
  fun s l s' => l.elim (s = s') (trans s · s')

/-! ## LTSs and LTS morphisms form a category -/

/--
The definition of labelled transition system (with the type of states and the
type of states as part of the structure).
-/
structure LTSCat : Type (max u v + 1) where
  State : Type u
  Label : Type v
  lts : LTS State Label

/--
A morphism between two labelled transition systems consists of (1) a function on
states, (1) a partial function on labels, and a proof that (1) preserves each
transition along (2).
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

/-- Composition of LTS morphisms.

We use Kleisli composition to define this.
-/
def LTS.Morphism.comp {lts₁ lts₂ lts₃ : LTSCat} :
    LTS.Morphism lts₁ lts₂ → LTS.Morphism lts₂ lts₃ → LTS.Morphism lts₁ lts₃ :=
  fun ⟨f, μ, p⟩ ⟨g, ν, q⟩ =>
    let r := by
      intro s s' l h
      have hp := p s s' l h
      change ((μ l).bind ν).elim (g (f s) = g (f s')) _
      cases hμ : μ l with
      | none =>
        rw [hμ] at hp
        exact congrArg g hp
      | some m =>
        rw [hμ] at hp
        exact q (f s) (f s') m hp
    ⟨g ∘ f, μ >=> ν, r⟩

/-- Finally, we prove that these form a category. -/
instance : CategoryTheory.Category LTSCat where
  Hom lts₁ lts₂ := LTS.Morphism lts₁ lts₂
  id lts := LTS.Morphism.id lts
  comp {lts₁} {lts₂} {lts₃} f g := @LTS.Morphism.comp lts₁ lts₂ lts₃ f g
  id_comp := by
    intro _ _ f
    cases f
    simp only [LTS.Morphism.comp, LTS.Morphism.id, Function.comp_id]
    congr 1
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
