/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.Propositional.NaturalDeduction.Lemmas
import Mathlib.Order.Heyting.Basic
import Mathlib.Data.Finset.Lattice.Fold


/-! # Heyting algebra semantics -/

namespace PL

namespace NJ

open Proposition Theory Derivation

variable {Atom : Type _} [DecidableEq Atom] {T : Theory Atom}

def Valuation (Atom : Type _) (H : Type _) := Atom → H

/-- Extend a valuation to propositions using the Heyting algebra operations. -/
def Valuation.pInterpret {H : Type _} [GeneralizedHeytingAlgebra H] (v : Valuation Atom H) :
    Proposition Atom → H
  | atom x => v x
  | conj A B => (v.pInterpret A) ⊓ (v.pInterpret B)
  | disj A B => (v.pInterpret A) ⊔ (v.pInterpret B)
  | impl A B => (v.pInterpret A) ⇨ (v.pInterpret B)

/-- TODO: this coercion doesn't work without explicit type annotation eg:
(↑v : Proposition Atom → H) A because lean defaults to v : Atom → H. There should be some way to
override this especially since v x = ↑v (atom x). -/
instance {H : Type _} [GeneralizedHeytingAlgebra H] :
    CoeFun (Valuation Atom H) (fun _ => Proposition Atom → H) where
  coe := Valuation.pInterpret

/-- Extend a valuation to contexts using conjunction. -/
def Valuation.ctxInterpret {H : Type _} [GeneralizedHeytingAlgebra H] (v : Valuation Atom H)
    (Γ : Ctx Atom) : H := Γ.inf (v.pInterpret)

@[inherit_doc]
scoped notation v "⟦" A "⟧" => Valuation.pInterpret v A

@[inherit_doc]
scoped notation v "⟦" Γ "⟧" => Valuation.ctxInterpret v Γ

open Valuation

variable {H : Type _} [iH : GeneralizedHeytingAlgebra H] (v : Valuation Atom H)

/-- A valuation models a proposition if its interpretation is the top element. -/
@[reducible]
def Valuation.PValid (A : Proposition Atom) : Prop := v⟦A⟧ = ⊤

/-- A valuation models a sequent if the interpretation of the context is ≤ the interpretation of
the conclusion. -/
@[reducible]
def Valuation.SValid (S : Sequent Atom) : Prop := v⟦S.1⟧ ≤ v⟦S.2⟧

/-- A valuation models a theory if it models every axiom. -/
@[reducible]
def Valuation.TValid (T : Theory Atom) : Prop := ∀ A ∈ T, v.PValid A

@[inherit_doc]
scoped notation v' " ⊨ " A => Valuation.PValid v' A

@[inherit_doc]
scoped notation v' " ⊨ " S => Valuation.SValid v' S

@[inherit_doc]
scoped notation v' " ⊨ " T => Valuation.TValid v' T

theorem sound_of_derivation {Γ : Ctx Atom} {B : Proposition Atom} :
    T.Derivation ⟨Γ, B⟩ → ∀ {v : Valuation Atom H}, (v ⊨ T) → v ⊨ ⟨Γ, B⟩
  | Theory.Derivation.ax hB, v, _ => by have : v⟦Γ⟧ ≤ ⊤ := iH.le_top _; grind
  | Theory.Derivation.ass hB, _, _ => Finset.inf_le hB
  | Theory.Derivation.conjI D E, v, hT =>
    iH.le_inf _ _ _ (sound_of_derivation D hT) (sound_of_derivation E hT)
  | Theory.Derivation.conjE₁ D, v, hT =>
    iH.le_trans _ _ _ (sound_of_derivation D hT) (iH.inf_le_left _ _)
  | Theory.Derivation.conjE₂ D, v, hT =>
    iH.le_trans _ _ _ (sound_of_derivation D hT) (iH.inf_le_right _ _)
  | Theory.Derivation.disjI₁ D, v, hT =>
    iH.le_trans _ _ _ (sound_of_derivation D hT) (iH.le_sup_left _ _)
  | Theory.Derivation.disjI₂ D, v, hT =>
    iH.le_trans _ _ _ (sound_of_derivation D hT) (iH.le_sup_right _ _)
  | @Theory.Derivation.disjE _ _ _ Γ A B C D E E', v, hT => by
    change v⟦Γ⟧ ≤ v⟦C⟧
    trans v⟦insert A Γ⟧ ⊔ v⟦insert B Γ⟧
    · simp_rw [Valuation.ctxInterpret, Finset.inf_insert, ←inf_sup_right]
      apply iH.le_inf
      · exact sound_of_derivation D hT
      · rfl
    · exact iH.sup_le _ _ _ (sound_of_derivation E hT) (sound_of_derivation E' hT)
  | @Theory.Derivation.implI _ _ _ A B _ D, v, hT => by
    refine (iH.le_himp_iff _ _ _).mpr ?_
    have : v⟦insert A Γ⟧ ≤ v⟦B⟧ := sound_of_derivation D hT
    rwa [Valuation.ctxInterpret, Finset.inf_insert, inf_comm] at this
  | @Theory.Derivation.implE _ _ _ _ A B D E, v, hT => by
    change v⟦Γ⟧ ≤ v⟦B⟧
    trans (v⟦A⟧ ⇨ v⟦B⟧) ⊓ v⟦A⟧
    · exact iH.le_inf _ _ _ (sound_of_derivation D hT) (sound_of_derivation E hT)
    · exact himp_inf_le

theorem sound {Γ : Ctx Atom} {B : Proposition Atom} :
    Γ ⊢[T] B → ∀ {v : Valuation Atom H}, (v ⊨ T) → v ⊨ ⟨Γ, B⟩
  | ⟨D⟩ => sound_of_derivation D

end NJ

end PL
