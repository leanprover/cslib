/-
Copyright (c) 2025 Thomas Waring, 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring, Benjamin Brast-McKie
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Results on propositional theories

In this file we prove the expected results that `IPL` is an intuitionistic theory, and
`CPL` is a classical theory. We provide derived rules for common intuitionistic and classical
proof patterns.

Since `Proposition` has `bot` as a primitive constructor, no `[Bot Atom]` constraint is needed:
`⊥ : Proposition Atom` is always available as `.bot`.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn Derivation IsIntuitionistic IsClassical

variable {Atom : Type u} [DecidableEq Atom] {T : Theory Atom}

namespace Theory

/-- `IPL` is intuitionistic: it contains `⊥ → A` for all `A`. -/
instance instIsIntuitionisticIPL : IsIntuitionistic Atom (IPL (Atom := Atom)) where
  efq A := ax (efq_mem_ipl A)

/-- `CPL` is classical: it contains `¬¬A → A` for all `A`. -/
instance instIsClassicalCPL : IsClassical Atom (CPL (Atom := Atom)) where
  dne A := ax (dne_mem_cpl A)

/-- The intuitionistic completion of any theory is intuitionistic. -/
instance instIsIntuitionisticIntuitionisticCompletion [DecidableEq (WithBot Atom)]
    (T : Theory Atom) :
    IsIntuitionistic (WithBot Atom) T.intuitionisticCompletion where
  efq A := ax (Set.mem_union_right _ (efq_mem_ipl A))

/-- Derivation of efq in an arbitrary context. -/
def IsIntuitionistic.efqCtx [IsIntuitionistic Atom T] (Γ : Ctx Atom) (A : Proposition Atom)
    : T⇓(Γ ⊢ ⊥ → A) := (efq A : T⇓(⊥ → A)).weakCtx (Finset.empty_subset Γ)

/-- Efq as a derived rule. -/
def IsIntuitionistic.efqRule [IsIntuitionistic Atom T] (Γ : Ctx Atom) (A : Proposition Atom)
    (D : T⇓(Γ ⊢ ⊥)) : T⇓(Γ ⊢ A) :=
  impE (A := ⊥) (efqCtx Γ A) D

/-- Prove any proposition from contradictory hypotheses. -/
def IsIntuitionistic.contra [IsIntuitionistic Atom T] {Γ : Ctx Atom} (A B : Proposition Atom)
    (hΓ : A ∈ Γ) (hΓ' : (¬A) ∈ Γ) : T⇓(Γ ⊢ B) :=
  efqRule Γ B <| impE (ass hΓ') (ass hΓ)

/-- Proof by contradiction as a derived rule. -/
def IsClassical.byContra [IsClassical Atom T] {Γ : Ctx Atom} {A : Proposition Atom}
    (D : T⇓(insert (¬ A) Γ ⊢ ⊥)) : T⇓(Γ ⊢ A) :=
  impE (A := ¬¬A) ((dne A : T⇓(¬¬A → A)) |>.weakCtx <| Finset.empty_subset ..) D.impI

instance instIsIntuitionisticOfIsClassical [IsClassical Atom T] : IsIntuitionistic Atom T where
  efq A := impI _ <| byContra <| ass (by grind)

/-- Law of excluded middle in a classical theory. -/
def IsClassical.lem [IsClassical Atom T] (A : Proposition Atom) : T⇓(A ∨ ¬ A) := by
  apply byContra
  apply impE (ass <| Finset.mem_insert_self ..)
  apply orI2
  apply impI
  apply impE (A := A ∨ ¬ A) (ass <| by grind)
  apply orI1
  exact ass <| Finset.mem_insert_self ..

/-- Pierce's law in a classical theory. -/
def IsClassical.pierce [IsClassical Atom T] (A B : Proposition Atom) : T⇓(((A → B) → A) → A) := by
  apply impI; apply byContra
  apply impE (ass <| Finset.mem_insert_self ..)
  apply impE (A := A → B) (ass <| by grind); apply impI
  apply contra A B <;> grind

/-- The axiom system consisting of instances of LEM. -/
def LEM : Theory Atom := {A ∨ ¬ A | A : Proposition Atom}

omit [DecidableEq Atom] in
lemma lem_mem_lem (A : Proposition Atom) : (A ∨ ¬ A) ∈ LEM (Atom := Atom) := ⟨A, rfl⟩

/-- The axiom system consisting of instances of Pierce's law. -/
def Pierce : Theory Atom :=
  {((A → B) → A) → A | (A : Proposition Atom) (B : Proposition Atom)}

omit [DecidableEq Atom] in
lemma pierce_mem_pierce (A B : Proposition Atom) :
    (((A → B) → A) → A) ∈ Pierce (Atom := Atom) := ⟨A, B, rfl⟩

instance instIsClassicalLEM : IsClassical Atom (LEM ∪ IPL : Theory Atom) where
  dne A := by
    apply impI
    apply orE
    · exact ax <| Set.mem_union_left _ <| lem_mem_lem A
    · exact ass (Finset.mem_insert_self A _)
    · apply impE (A := ⊥) (ax <| Set.mem_union_right _ (efq_mem_ipl A))
      apply impE (A := ¬ A)
      · exact ass (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _)))
      · exact ass (Finset.mem_insert_self _ _)

instance instIsClassicalPierce : IsClassical Atom (Pierce ∪ IPL : Theory Atom) where
  dne A := by
    apply impI
    apply impE (A := (A → ⊥) → A) (ax <| Set.mem_union_left _ <| pierce_mem_pierce A ⊥)
    apply impI
    apply impE (A := ⊥) (ax <| Set.mem_union_right _ (efq_mem_ipl A))
    apply impE (A := ¬ A)
    · exact ass (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _)))
    · exact ass (Finset.mem_insert_self _ _)

end Cslib.Logic.PL.Theory
