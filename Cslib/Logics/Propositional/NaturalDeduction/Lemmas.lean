/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Auxilliary results on natural deduction

In this file we prove the expected results that `ND₁ T` is always intuitionistic, and that various
axiomatisations of classical logic (`CPL Atom` using double-negation elimination, `LEM Atom` using
the law of excluded middle, and `Pierce Atom` using Pierce's law) are classical inference systems.
We provide derived rules for common intuitionistic and classical proof patterns.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition InferenceSystem DerivableIn NaturalDeduction Derivation
  IsIntuitionistic IsClassical

variable {Atom : Type u} [DecidableEq Atom] {T : Set (Proposition Atom)}

instance instIsIntuitionisticND₁ : IsIntuitionistic Atom (ND₁ T) where
  derBotImp A := ass (Finset.mem_insert_self ⊥ ∅) |>.efq A |>.impI

/-- Derivation of efq in an arbitrary context. -/
def IsIntuitionistic.derBotImpCtx [IsIntuitionistic Atom (ND₁ T)] (Γ : Ctx Atom)
    (A : Proposition Atom) : (ND T)⇓(Γ ⊢ ⊥ → A) :=
  (derBotImp A : (ND₁ T)⇓(⊥ → A)).weakCtx (Finset.empty_subset Γ)

/-- Efq as a derived rule. -/
def IsIntuitionistic.efqRule [IsIntuitionistic Atom (ND₁ T)] (Γ : Ctx Atom) (A : Proposition Atom)
    (D : (ND T)⇓(Γ ⊢ ⊥)) : (ND T)⇓(Γ ⊢ A) :=
  impE (A := ⊥) (derBotImpCtx Γ A) D

/-- Prove any proposition from contradictory hypotheses. -/
def IsIntuitionistic.contra [IsIntuitionistic Atom (ND₁ T)] {Γ : Ctx Atom} (A B : Proposition Atom)
    (hΓ : A ∈ Γ) (hΓ' : (¬A) ∈ Γ) : (ND T)⇓(Γ ⊢ B) :=
  efqRule Γ B <| impE (ass hΓ') (ass hΓ)

instance instIsClassicalCPL : IsClassical Atom (ND₁ <| CPL Atom) where
  dne A := ax (dne_mem_cpl A)

/-- Proof by contradiction as a derived rule. -/
def IsClassical.byContra [IsClassical Atom (ND₁ T)] {Γ : Ctx Atom} {A : Proposition Atom}
    (D : (ND T)⇓(insert (¬ A) Γ ⊢ ⊥)) : (ND T)⇓(Γ ⊢ A) :=
  impE (A := ¬¬A) ((dne A : (ND₁ T)⇓(¬¬A → A)) |>.weakCtx <| Finset.empty_subset ..) D.impI

/-- Law of excluded middle in a classical theory. -/
def IsClassical.lem [IsClassical Atom (ND₁ T)] (A : Proposition Atom) : (ND₁ T)⇓(A ∨ ¬ A) := by
  apply byContra
  apply impE (ass <| Finset.mem_insert_self ..)
  apply orI₂; apply impI
  apply impE (A := A ∨ ¬ A) (ass <| by grind)
  exact orI₁ <| ass <| Finset.mem_insert_self ..

/-- Pierce's law in a classical theory. -/
def IsClassical.pierce [IsClassical Atom (ND₁ T)] (A B : Proposition Atom) :
    (ND₁ T)⇓(((A → B) → A) → A) := by
  apply impI; apply byContra
  apply impE (ass <| Finset.mem_insert_self ..)
  apply impE (A := A → B) (ass <| by grind); apply impI
  apply contra A B <;> grind

/-- The axiom system consisting of instances of LEM. -/
def LEM (Atom : Type u) : Set (Proposition Atom) := {A ∨ ¬ A | A : Proposition Atom}

omit [DecidableEq Atom] in
lemma lem_mem_lem (A : Proposition Atom) : (A ∨ ¬ A) ∈ LEM Atom := ⟨A, rfl⟩

/-- The axiom system consisting of instances of Pierce's law. -/
def Pierce (Atom : Type u) : Set (Proposition Atom) :=
  {((A → B) → A) → A | (A : Proposition Atom) (B : Proposition Atom)}

omit [DecidableEq Atom] in
lemma pierce_mem_pierce (A B : Proposition Atom) : (((A → B) → A) → A) ∈ Pierce Atom := ⟨A, B, rfl⟩

instance instIsClassicalLEM : IsClassical Atom (ND₁ <| LEM Atom) where
  dne A := by
    apply impI
    apply orE (ax <| lem_mem_lem A)
    · exact ass (Finset.mem_insert_self A _)
    · apply impE (A := ⊥) (derBotImpCtx _ A)
      apply impE (A := ¬ A) <;> exact ass (by grind)

instance instIsClassicalPierce : IsClassical Atom (ND₁ <| Pierce Atom) where
  dne A := by
    apply impI
    apply impE (A := (A → ⊥) → A) (ax <| pierce_mem_pierce A ⊥)
    apply impI
    apply impE (A := ⊥) (derBotImpCtx _ A)
    apply impE (A := ¬ A) <;> exact ass (by grind)

end Cslib.Logic.PL
