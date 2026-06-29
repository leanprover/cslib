/-
Copyright (c) 2025 Thomas Waring, 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring, Benjamin Brast-McKie
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Results on propositional theories

In this file we prove that `CPL` is a classical theory. We provide derived rules for common
classical proof patterns.

Since `Proposition` has `bot` as a primitive constructor, no `[Bot Atom]` constraint is needed:
`⊥ : Proposition Atom` is always available as `.bot`.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn Derivation IsClassical

variable {Atom : Type u} [DecidableEq Atom] {T : Theory Atom}

namespace Theory

/-- `CPL` is classical: it contains `¬¬A → A` for all `A`. -/
instance instIsClassicalCPL : IsClassical Atom (CPL (Atom := Atom)) where
  dne A := ax (dne_mem_cpl A)

/-- Proof by contradiction as a derived rule. -/
def IsClassical.byContra [IsClassical Atom T] {Γ : Ctx Atom} {A : Proposition Atom}
    (D : T⇓(insert (¬ A) Γ ⊢ ⊥)) : T⇓(Γ ⊢ A) :=
  impE (A := ¬¬A) ((dne A : T⇓(¬¬A → A)) |>.weakCtx <| Finset.empty_subset ..) D.impI

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
  exact efq (impE (ass <| Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _)))
                  (ass <| Finset.mem_insert_self _ _))

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

instance instIsClassicalLEM : IsClassical Atom (LEM : Theory Atom) where
  dne A := by
    apply impI
    apply orE
    · exact ax (lem_mem_lem A)
    · exact ass (Finset.mem_insert_self A _)
    · apply efq
      apply impE (A := ¬ A)
      · exact ass (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _)))
      · exact ass (Finset.mem_insert_self _ _)

instance instIsClassicalPierce : IsClassical Atom (Pierce : Theory Atom) where
  dne A := by
    apply impI
    apply impE (A := (A → ⊥) → A) (ax <| pierce_mem_pierce A ⊥)
    apply impI
    apply efq
    apply impE (A := ¬ A)
    · exact ass (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _)))
    · exact ass (Finset.mem_insert_self _ _)

end Cslib.Logic.PL.Theory
