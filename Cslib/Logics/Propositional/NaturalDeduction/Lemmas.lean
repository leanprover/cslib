/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Theory

/-!-/

@[expose] public section

namespace Cslib.Logic.PL.Theory

open Proposition Theory InferenceSystem DerivableIn Derivation IsIntuitionistic IsClassical

variable {Atom : Type*} [DecidableEq Atom] {T : Theory Atom} {Γ : Ctx Atom}
  {A A' B B' C : Proposition Atom}

def Derivation.refl (A : Proposition Atom) : T⇓({A} ⊢ A) := ass <| Finset.mem_insert_self _ ∅

lemma _root_.Cslib.Logic.InferenceSystem.DerivableIn.refl (A : Proposition Atom) :
    DerivableIn T ({A} ⊢ A) := ⟨.refl A⟩

def Derivation.trans (D : T⇓({A} ⊢ B)) (D' : T⇓({B} ⊢ C)) : T⇓({A} ⊢ C) := D.cut (Δ := ∅) D'

lemma _root_.Cslib.Logic.InferenceSystem.DerivableIn.trans (h : DerivableIn T ({A} ⊢ B))
    (h' : DerivableIn T ({B} ⊢ C)) : DerivableIn T ({A} ⊢ C) := ⟨h.some.trans h'.some⟩

def Derivation.leftOfAnd (A B : Proposition Atom) :
  T⇓({A ∧ B} ⊢ A) := andE₁ <| refl (A ∧ B)
def Derivation.rightOfAnd (A B : Proposition Atom) :
  T⇓({A ∧ B} ⊢ B) := andE₂ <| refl (A ∧ B)

lemma _root_.Cslib.Logic.InferenceSystem.DerivableIn.left_of_and (A B : Proposition Atom) :
    DerivableIn T ({A ∧ B} ⊢ A) := ⟨.leftOfAnd A B⟩
lemma _root_.Cslib.Logic.InferenceSystem.DerivableIn.right_of_and (A B : Proposition Atom) :
    DerivableIn T ({A ∧ B} ⊢ B) := ⟨.rightOfAnd A B⟩

def Derivation.mapAnd (DA : T⇓({A} ⊢ A')) (DB : T⇓({B} ⊢ B')) : T⇓({A ∧ B} ⊢ A' ∧ B') :=
  ((leftOfAnd A B).cut (Δ := ∅) DA).andI <| (rightOfAnd A B).cut (Δ := ∅) DB

lemma _root_.Cslib.Logic.InferenceSystem.DerivableIn.map_and (hA : DerivableIn T ({A} ⊢ A'))
    (hB : DerivableIn T ({B} ⊢ B')) : DerivableIn T ({A ∧ B} ⊢ A' ∧ B') :=
  ⟨hA.some.mapAnd hB.some⟩

def equiv.and (eA : T.equiv A A') (eB : T.equiv B B') : T.equiv (A ∧ B) (A' ∧ B') where
  mp := eA.mp.mapAnd eB.mp
  mpr := eA.mpr.mapAnd eB.mpr

theorem Equiv.and (hA : A ≡[T] A') (hB : B ≡[T] B') : (A ∧ B) ≡[T] (A' ∧ B') :=
  ⟨hA.some.and hB.some⟩

def Derivation.orOfLeft (A B : Proposition Atom) :
  T⇓({A} ⊢ A ∨ B) := orI₁ <| refl A
def Derivation.orOfRight (A B : Proposition Atom) :
  T⇓({B} ⊢ A ∨ B) := orI₂ <| refl B

lemma _root_.Cslib.Logic.InferenceSystem.DerivableIn.or_of_left (A B : Proposition Atom) :
    DerivableIn T ({A} ⊢ A ∨ B) := ⟨.orOfLeft A B⟩
lemma _root_.Cslib.Logic.InferenceSystem.DerivableIn.or_of_right (A B : Proposition Atom) :
    DerivableIn T ({B} ⊢ A ∨ B) := ⟨.orOfRight A B⟩

def Derivation.mapOr (DA : T⇓({A} ⊢ A')) (DB : T⇓({B} ⊢ B')) : T⇓({A ∨ B} ⊢ A' ∨ B') :=
  (refl (A ∨ B)).orE (DA.weakCtx (by grind)).orI₁ (DB.weakCtx (by grind)).orI₂

lemma _root_.Cslib.Logic.InferenceSystem.DerivableIn.map_or (hA : DerivableIn T ({A} ⊢ A'))
    (hB : DerivableIn T ({B} ⊢ B')) : DerivableIn T ({A ∨ B} ⊢ A' ∨ B') :=
  ⟨hA.some.mapOr hB.some⟩

def equiv.or (eA : T.equiv A A') (eB : T.equiv B B') : T.equiv (A ∨ B) (A' ∨ B') where
  mp := eA.mp.mapOr eB.mp
  mpr := eA.mpr.mapOr eB.mpr

theorem Equiv.or (hA : A ≡[T] A') (hB : B ≡[T] B') : (A ∨ B) ≡[T] (A' ∨ B') :=
  ⟨hA.some.or hB.some⟩

def Derivation.mapImp (DA : T⇓({A'} ⊢ A)) (DB : T⇓({B} ⊢ B')) : T⇓({A → B} ⊢ A' → B') :=
  implI {A → B} <| ((DB.implI ∅).weakCtx <| Finset.empty_subset _).implE <|
    implE (A := A) (ass <| by grind) (DA.weakCtx (by grind))

lemma _root_.Cslib.Logic.InferenceSystem.DerivableIn.map_imp (hA : DerivableIn T ({A'} ⊢ A))
    (hB : DerivableIn T ({B} ⊢ B')) : DerivableIn T ({A → B} ⊢ A' → B') :=
  ⟨hA.some.mapImp hB.some⟩

def equiv.imp (eA : T.equiv A A') (eB : T.equiv B B') : T.equiv (A → B) (A' → B') where
  mp := eA.mpr.mapImp eB.mp
  mpr := eA.mp.mapImp eB.mpr

theorem Equiv.imp (hA : A ≡[T] A') (hB : B ≡[T] B') : (A → B) ≡[T] (A' → B') :=
  ⟨hA.some.imp hB.some⟩

def mapNot (D : T⇓({A} ⊢ A')) : T⇓({¬A'} ⊢ ¬A) := D.mapImp (refl ⊥)

def equiv.not (e : T.equiv A A') : T.equiv (¬A) (¬A') := e.imp (refl ⊥)

theorem Equiv.not (hA : A ≡[T] A') : (¬A) ≡[T] (¬A') :=
  ⟨hA.some.not⟩

def Derivation.curry (D : T⇓(insert A Γ ⊢ B → C)) : T⇓(insert (A ∧ B) Γ ⊢ C) :=
  ((leftOfAnd A B).cut D).implE <| andE₂ <| ass <| Finset.mem_insert_self ..

def Derivation.uncurry (D : T⇓(insert (A ∧ B) Γ ⊢ C)) : T⇓(insert A Γ ⊢ B → C) := by
  apply implI
  refine (D.subs fun D h ↦ ?_).weakCtx
    (show insert (A ∧ B) Γ \ {A ∧ B} ∪ {A, B} ⊆ insert B (insert A Γ) by grind)
  obtain rfl : D = (A ∧ B) := Finset.mem_singleton.mp h
  exact (ass <| by grind).andI (ass <| by grind)

theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.imp_iff_insert_and :
    DerivableIn T (insert A Γ ⊢ B → C) ↔ DerivableIn T (insert (A ∧ B) Γ ⊢ C) :=
  ⟨fun ⟨D⟩ ↦ ⟨D.curry⟩, fun ⟨D⟩ ↦ ⟨D.uncurry⟩⟩

def Derivation.curryList {Γ : List (Proposition Atom)} {Δ : Ctx Atom} {A : Proposition Atom}
    (D : T⇓((Γ.toFinset ∪ Δ) ⊢ A)) : T⇓(Δ ⊢ Γ.foldl (fun B C ↦ C → B) A) :=
  match Γ with
  | [] => D.weakCtx <| by simp
  | B :: Γ => (D.weakCtx (by simp) |>.implI _).curryList (A := B → A)

def Derivation.uncurryList {Γ : List (Proposition Atom)} {Δ : Ctx Atom} {A : Proposition Atom}
    (D : T⇓(Δ ⊢ Γ.foldl (fun B C ↦ C → B) A)) : T⇓((Γ.toFinset ∪ Δ) ⊢ A) :=
  match Γ with
  | [] => D.weakCtx <| by simp
  | B :: Γ => (D.uncurryList (A := B → A)).weakCtx (by simp) |>.implE (ass <| by simp)

theorem _root_.Cslib.Logic.InferenceSystem.DerivableIn.toFinset_union_iff
    {Γ : List (Proposition Atom)} {Δ : Ctx Atom} {A : Proposition Atom} :
    DerivableIn T ((Γ.toFinset ∪ Δ) ⊢ A) ↔ DerivableIn T (Δ ⊢ Γ.foldl (fun B C ↦ C → B) A) :=
  ⟨fun h ↦ h.some.curryList, fun h ↦ h.some.uncurryList⟩


end Cslib.Logic.PL.Theory
