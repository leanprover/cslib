/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Lemmas
public import Mathlib.Order.Antisymmetrization

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

structure Encoding (T : Theory Atom) (T' : Theory Atom') : Type _ where
  f : Atom → Proposition Atom'
  derSubstOfMem {A : Proposition Atom} (hA : A ∈ T) : T'⇓(A.subst f)

def Derivation.mapEncoding (e : T.Encoding T') {Γ : Ctx Atom} {A : Proposition Atom} :
    T.Derivation Γ A → T'.Derivation (Γ.subst e.f) (A.subst e.f)
  | ax hA => (e.derSubstOfMem hA).weakCtx (by simp)
  | ass hA => ass <| Finset.mem_image_of_mem _ hA
  | efq _ D => (D.mapEncoding e).efq (A.subst e.f)
  | andI D D' => (D.mapEncoding e).andI (D'.mapEncoding e)
  | andE₁ D => (D.mapEncoding e).andE₁
  | andE₂ D => (D.mapEncoding e).andE₂
  | orI₁ D => (D.mapEncoding e).orI₁
  | orI₂ D => (D.mapEncoding e).orI₂
  | @orE _ _ _ Γ A B C D DA DB =>
    (D.mapEncoding e).orE
      ((DA.mapEncoding e).weakCtx (Finset.image_insert (·.subst e.f) A Γ).subset)
      ((DB.mapEncoding e).weakCtx (Finset.image_insert (·.subst e.f) B Γ).subset)
  | @implI _ _ _ A B Γ D =>
      implI (Γ.subst e.f) <| (D.mapEncoding e).weakCtx <|
        (Finset.image_insert (·.subst e.f) A Γ).subset
  | implE D D' => (D.mapEncoding e).implE (D'.mapEncoding e)

theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.map_encoding (e : T.Encoding T')
    {Γ : Ctx Atom} {A : Proposition Atom} (h : DerivableIn T (Γ ⊢ A)) :
    DerivableIn T' (Γ.subst e.f ⊢ A.subst e.f) :=
  ⟨h.some.mapEncoding e⟩

def Encoding.refl (T : Theory Atom) : T.Encoding T where
  f := atom
  derSubstOfMem hA := ax (by simpa)

def Encoding.trans (e : T.Encoding T') (e' : T'.Encoding T'') : T.Encoding T'' where
  f x := (e.f x).subst e'.f
  derSubstOfMem hA := subst_assoc ▸ (e.derSubstOfMem hA).mapEncoding e'

def Encoding.ofSubset {T₁ T₂ : Theory Atom} (h : T₁ ⊆ T₂) : T₁.Encoding T₂ where
  f := atom
  derSubstOfMem hA := ax <| by simpa using h hA

variable {T₁ T₂ : Theory Atom} {A : Proposition Atom}

def WeakerThan (T₁ T₂ : Theory Atom) : Prop := ∀ A ∈ T₁, DerivableIn T₂ A

noncomputable def WeakerThan.toEncoding (h : T₁.WeakerThan T₂) : T₁.Encoding T₂ where
  f := atom
  derSubstOfMem {A} hA := (subst_atom A).symm ▸ (h _ hA).some

@[simp] lemma WeakerThan.toEncoding_f (h : T₁.WeakerThan T₂) : h.toEncoding.f = atom := rfl

theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.of_weakerThan (h : T₁.WeakerThan T₂)
    (hA : DerivableIn T₁ A) : DerivableIn T₂ A := by
  convert Nonempty.intro <| hA.some.mapEncoding h.toEncoding
  simp [Ctx.subst]
  rfl

alias WeakerThan.map_derivableIn := DerivableIn.of_weakerThan

theorem weakerThan_iff_forall_derivableIn :
    T₁.WeakerThan T₂ ↔ ∀ A : Proposition Atom, DerivableIn T₁ A → DerivableIn T₂ A :=
  ⟨fun h _ hA ↦ h.map_derivableIn hA, fun h A hA ↦ h A ⟨ax hA⟩⟩

instance : IsPreorder (Theory Atom) WeakerThan where
  refl _ _ hA := ⟨ax hA⟩
  trans _ _ _ h h' A hA := (h A hA).of_weakerThan h'

lemma WeakerThan.of_subset {T₁ T₂ : Theory Atom} (h : T₁ ⊆ T₂) : T₁.WeakerThan T₂ :=
  fun _ hA ↦ ⟨ax <| h hA⟩

instance : Setoid (Theory Atom) := AntisymmRel.setoid _ WeakerThan

@[simp] lemma equiv_theory_iff :
    T₁ ≈ T₂ ↔ ∀ A : Proposition Atom, DerivableIn T₁ A ↔ DerivableIn T₂ A := by
  simp [AntisymmRel, weakerThan_iff_forall_derivableIn]
  grind

alias ⟨_root_.HasEquiv.Equiv.derivableIn_iff, _⟩ :=
  equiv_theory_iff

def Saturated (T : Theory Atom) : Prop := ∀ A : Proposition Atom, DerivableIn T A → A ∈ T

lemma Saturated.mem_of_derivableIn (h : T.Saturated) (hA : DerivableIn T A) : A ∈ T := h A hA

lemma saturated_iff_derivableIn_iff : T.Saturated ↔ ∀ A, DerivableIn T A ↔ A ∈ T :=
  ⟨fun h A ↦ ⟨h A, (⟨ax ·⟩)⟩, fun h A hA ↦ (h A).mp hA⟩

@[simp] alias ⟨Saturated.derivableIn_iff, _⟩ := saturated_iff_derivableIn_iff

def saturation (T : Theory Atom) : Theory Atom := {A : Proposition Atom | DerivableIn T A}

@[simp] lemma mem_saturation_iff : A ∈ T.saturation ↔ DerivableIn T A := .rfl

lemma self_subset_saturation : T ⊆ T.saturation := fun _ hA ↦ ⟨ax hA⟩

lemma saturation_weakerThan_self : T.saturation.WeakerThan T := fun _ hA ↦ hA

lemma self_equiv_saturation (T : Theory Atom) : T ≈ T.saturation :=
  ⟨.of_subset self_subset_saturation, saturation_weakerThan_self⟩

@[simp] lemma derivableIn_saturation_iff : DerivableIn T.saturation A ↔ DerivableIn T A :=
    (self_equiv_saturation T).derivableIn_iff A |>.symm

lemma saturated_saturation : T.saturation.Saturated := by simp [Saturated, mem_saturation_iff]

lemma Saturated.saturation_eq (h : T.Saturated) : T.saturation = T := by
  ext; simp [h.derivableIn_iff]

lemma saturation_idem : T.saturation.saturation = T.saturation := saturated_saturation.saturation_eq

end Cslib.Logic.PL.Theory
