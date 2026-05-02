/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Results on propositional theories -/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn Derivation IsIntuitionistic IsClassical

variable {Atom : Type u} [DecidableEq Atom] [Bot Atom] {T : Theory Atom}

namespace Theory

instance instIsIntuitionisticIPL : IsIntuitionistic Atom (IPL Atom) where
  efq A := ax (efq_mem_ipl A)

def IsIntuitionistic.efqCtx [IsIntuitionistic Atom T] (Γ : Ctx Atom) (A : Proposition Atom)
    : T⇓(Γ ⊢ ⊥ → A) := (efq A : T⇓(⊥ → A)).weak_ctx (Finset.empty_subset Γ)

def IsIntuitionistic.efqRule [IsIntuitionistic Atom T] (Γ : Ctx Atom) (A : Proposition Atom)
    (D : T⇓(Γ ⊢ ⊥)) : T⇓(Γ ⊢ A) :=
  implE (A := ⊥) (efqCtx Γ A) D

def IsIntuitionistic.contra [IsIntuitionistic Atom T] {Γ : Ctx Atom} (A B : Proposition Atom)
    (hΓ : A ∈ Γ) (hΓ' : (¬A) ∈ Γ) : T⇓(Γ ⊢ B) :=
  efqRule Γ B <| implE (ass hΓ') (ass hΓ)

instance instIsClassicalCPL : IsClassical Atom (CPL Atom) where
  dne A := ax (dne_mem_cpl A)

def IsClassical.byContra [IsClassical Atom T] {Γ : Ctx Atom} {A : Proposition Atom}
    (D : T⇓(insert (¬ A) Γ ⊢ ⊥)) : T⇓(Γ ⊢ A) :=
  implE (A := ¬¬A) ((dne A : T⇓(¬¬A → A)) |>.weak_ctx <| Finset.empty_subset ..) D.implI

instance instIsIntuitionisticOfIsClassical [IsClassical Atom T] : IsIntuitionistic Atom T where
  efq A := implI _ <| byContra <| ass (by grind)

def IsClassical.lem [IsClassical Atom T] (A : Proposition Atom) : T⇓(A ∨ ¬ A) := by
  apply byContra
  apply implE (ass <| Finset.mem_insert_self ..)
  apply orI₂; apply implI
  apply implE (A := A ∨ ¬ A) (ass <| by grind)
  exact orI₁ <| ass <| Finset.mem_insert_self ..

def IsClassical.pierce [IsClassical Atom T] (A B : Proposition Atom) : T⇓(((A → B) → A) → A) := by
  apply implI; apply byContra
  apply implE (ass <| Finset.mem_insert_self ..)
  apply implE (A := A → B) (ass <| by grind); apply implI
  apply contra A B <;> grind

def LEM (Atom : Type u) [Bot Atom] : Theory Atom := {A ∨ ¬ A | A : Proposition Atom}

omit [DecidableEq Atom] in
lemma lem_mem_lem (A : Proposition Atom) : (A ∨ ¬ A) ∈ LEM Atom := ⟨A, rfl⟩

def Pierce (Atom : Type u) [Bot Atom] : Theory Atom :=
  {((A → B) → A) → A | (A : Proposition Atom) (B : Proposition Atom)}

omit [DecidableEq Atom] in
lemma pierce_mem_pierce (A B : Proposition Atom) : (((A → B) → A) → A) ∈ Pierce Atom := ⟨A, B, rfl⟩

instance instIsClassicalLEM : IsClassical Atom (LEM Atom ∪ IPL Atom : Theory Atom) where
  dne A := by
    apply implI
    apply orE (ax <| Set.mem_union_left _ <| lem_mem_lem A)
    · exact ass (Finset.mem_insert_self A _)
    · apply implE (A := ⊥) (ax <| Set.mem_union_right _ (efq_mem_ipl A))
      apply implE (A := ¬ A) <;> exact ass (by grind)

instance instIsClassicalPierce : IsClassical Atom (Pierce Atom ∪ IPL Atom : Theory Atom) where
  dne A := by
    apply implI
    apply implE (A := (A → ⊥) → A) (ax <| Set.mem_union_left _ <| pierce_mem_pierce A ⊥)
    apply implI
    apply implE (A := ⊥) (ax <| Set.mem_union_right _ (efq_mem_ipl A))
    apply implE (A := ¬ A) <;> exact ass (by grind)

end Cslib.Logic.PL.Theory
