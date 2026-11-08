/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Lemmas

/-! # Results on propositional theories

In this file we prove the expected results that all theories are intuitionistic, and that various
axiomatisations of classical logic (`CPL Atom` using double-negation elimination, `LEM Atom` using
the law of excluded middle, and `Pierce Atom` using Pierce's law) are classical theories. We
provide derived rules for common intuitionistic and classical proof patterns.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn Derivation IsIntuitionistic IsClassical

variable {Atom Atom' Atom'' : Type*} [DecidableEq Atom] [DecidableEq Atom'] [DecidableEq Atom'']
  {T : Theory Atom} {T' : Theory Atom'} {T'' : Theory Atom''}

namespace Theory

instance instIsIntuitionisticTheory : IsIntuitionistic Atom T where
  derBotImp A := (ass (Finset.mem_insert_self ⊥ ∅)).efq A |>.implI

/-- Derivation of efq in an arbitrary context. -/
def IsIntuitionistic.derBotImpCtx [IsIntuitionistic Atom T] (Γ : Ctx Atom) (A : Proposition Atom)
    : T⇓(Γ ⊢ ⊥ → A) := (derBotImp A : T⇓(⊥ → A)).weakCtx (Finset.empty_subset Γ)

/-- Efq as a derived rule. -/
def IsIntuitionistic.efqRule [IsIntuitionistic Atom T] (Γ : Ctx Atom) (A : Proposition Atom)
    (D : T⇓(Γ ⊢ ⊥)) : T⇓(Γ ⊢ A) :=
  implE (A := ⊥) (derBotImpCtx Γ A) D

/-- Prove any proposition from contradictory hypotheses. -/
def IsIntuitionistic.contra [IsIntuitionistic Atom T] {Γ : Ctx Atom} (A B : Proposition Atom)
    (hΓ : A ∈ Γ) (hΓ' : (¬A) ∈ Γ) : T⇓(Γ ⊢ B) :=
  efqRule Γ B <| implE (ass hΓ') (ass hΓ)

theorem IsIntuitionistic.isInconsistent_iff_derivableIn_bot [IsIntuitionistic Atom T] :
    IsInconsistent Atom T ↔ DerivableIn T (⊥ : Proposition Atom) :=
  ⟨fun h ↦ h.forall_derivableIn ⊥, fun ⟨D⟩ ↦ ⟨fun A ↦ efqRule ∅ A D⟩⟩

theorem IsIntuitionistic.isConsistent_iff_not_derivableIn_bot [IsIntuitionistic Atom T] :
    IsConsistent Atom T ↔ ¬ DerivableIn T (⊥ : Proposition Atom) := by
  simp [← isInconsistent_iff_derivableIn_bot, isInconsistent_iff_not_isConsistent]

instance instIsClassicalCPL : IsClassical Atom (CPL Atom) where
  dne A := ax (dne_mem_cpl A)

/-- Proof by contradiction as a derived rule. -/
def IsClassical.byContra [IsClassical Atom T] {Γ : Ctx Atom} {A : Proposition Atom}
    (D : T⇓(insert (¬ A) Γ ⊢ ⊥)) : T⇓(Γ ⊢ A) :=
  implE (A := ¬¬A) ((dne A : T⇓(¬¬A → A)) |>.weakCtx <| Finset.empty_subset ..) D.implI

/-- Law of excluded middle in a classical theory. -/
def IsClassical.lem [IsClassical Atom T] (A : Proposition Atom) : T⇓(A ∨ ¬ A) := by
  apply byContra
  apply implE (ass <| Finset.mem_insert_self ..)
  apply orI₂; apply implI
  apply implE (A := A ∨ ¬ A) (ass <| by grind)
  exact orI₁ <| ass <| Finset.mem_insert_self ..

def IsClassical.byCases [hT : IsClassical Atom T] {Γ : Ctx Atom} {A B : Proposition Atom}
    (D : T⇓(insert A Γ ⊢ B)) (D' : T⇓(insert (¬A) Γ ⊢ B)) : T⇓(Γ ⊢ B) :=
  (hT.lem A).weakCtx (Finset.empty_subset Γ) |>.orE D D'

/-- Pierce's law in a classical theory. -/
def IsClassical.pierce [IsClassical Atom T] (A B : Proposition Atom) : T⇓(((A → B) → A) → A) := by
  apply implI; apply byContra
  apply implE (ass <| Finset.mem_insert_self ..)
  apply implE (A := A → B) (ass <| by grind); apply implI
  apply contra A B <;> grind

def IsClassical.imp_equiv_or_not [IsClassical Atom T] (A B : Proposition Atom) :
    T.equiv (A → B) (B ∨ ¬ A) where
  mp := by
    apply byCases (A := A)
    · refine orI₁ <| implE (A := A) ?_ ?_
      all_goals exact (ass <| by grind)
    · exact orI₂ <| ass (by grind)
  mpr := imp_of_or_not (Γ := ∅)

/-- The axiom system consisting of instances of LEM. -/
def LEM (Atom : Type u) : Theory Atom := {A ∨ ¬ A | A : Proposition Atom}

omit [DecidableEq Atom] in
lemma lem_mem_lem (A : Proposition Atom) : (A ∨ ¬ A) ∈ LEM Atom := ⟨A, rfl⟩

/-- The axiom system consisting of instances of Pierce's law. -/
def Pierce (Atom : Type u) : Theory Atom :=
  {((A → B) → A) → A | (A : Proposition Atom) (B : Proposition Atom)}

omit [DecidableEq Atom] in
lemma pierce_mem_pierce (A B : Proposition Atom) : (((A → B) → A) → A) ∈ Pierce Atom := ⟨A, B, rfl⟩

instance instIsClassicalLEM : IsClassical Atom (LEM Atom : Theory Atom) where
  dne A := by
    apply implI
    apply orE (ax <| lem_mem_lem A)
    · exact ass (Finset.mem_insert_self A _)
    · apply implE (A := ⊥) (derBotImpCtx _ A)
      apply implE (A := ¬ A) <;> exact ass (by grind)

instance instIsClassicalPierce : IsClassical Atom (Pierce Atom : Theory Atom) where
  dne A := by
    apply implI
    apply implE (A := (A → ⊥) → A) (ax <| pierce_mem_pierce A ⊥)
    apply implI
    apply implE (A := ⊥) (derBotImpCtx _ A)
    apply implE (A := ¬ A) <;> exact ass (by grind)

structure Embedding (T : Theory Atom) (T' : Theory Atom') : Type _ where
  f : Atom → Proposition Atom'
  derSubstOfMem {A : Proposition Atom} (hA : A ∈ T) : T'⇓(A.subst f)

def Derivation.mapEmbedding (e : T.Embedding T') {Γ : Ctx Atom} {A : Proposition Atom} :
    T.Derivation Γ A → T'.Derivation (Γ.subst e.f) (A.subst e.f)
  | ax hA => (e.derSubstOfMem hA).weakCtx (by simp)
  | ass hA => ass <| Finset.mem_image_of_mem _ hA
  | efq _ D => (D.mapEmbedding e).efq (A.subst e.f)
  | andI D D' => (D.mapEmbedding e).andI (D'.mapEmbedding e)
  | andE₁ D => (D.mapEmbedding e).andE₁
  | andE₂ D => (D.mapEmbedding e).andE₂
  | orI₁ D => (D.mapEmbedding e).orI₁
  | orI₂ D => (D.mapEmbedding e).orI₂
  | @orE _ _ _ Γ A B C D DA DB =>
    (D.mapEmbedding e).orE
      ((DA.mapEmbedding e).weakCtx (Finset.image_insert (·.subst e.f) A Γ).subset)
      ((DB.mapEmbedding e).weakCtx (Finset.image_insert (·.subst e.f) B Γ).subset)
  | @implI _ _ _ A B Γ D =>
      implI (Γ.subst e.f) <| (D.mapEmbedding e).weakCtx <|
        (Finset.image_insert (·.subst e.f) A Γ).subset
  | implE D D' => (D.mapEmbedding e).implE (D'.mapEmbedding e)

theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.map_embedding (e : T.Embedding T')
    {Γ : Ctx Atom} {A : Proposition Atom} (h : DerivableIn T (Γ ⊢ A)) :
    DerivableIn T' (Γ.subst e.f ⊢ A.subst e.f) :=
  ⟨h.some.mapEmbedding e⟩

def Embedding.refl (T : Theory Atom) : T.Embedding T where
  f := atom
  derSubstOfMem hA := ax (by simpa)

def Embedding.trans (e : T.Embedding T') (e' : T'.Embedding T'') : T.Embedding T'' where
  f x := (e.f x).subst e'.f
  derSubstOfMem hA := subst_assoc ▸ ((e.derSubstOfMem hA).mapEmbedding e')

end Cslib.Logic.PL.Theory
