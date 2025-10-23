/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Miscellaneous natural-deduction derivations

Rather than endeavouring to be exhaustive, we prove results as they are needed for applications.

## Main results

- Order theory: the fact that, modulo equivalence, the order `⊢[T]` and the logical operations give
a well-defined generalized Heyting algebra structure on the collection of propositions. If `T` is
intuitionistic, this is a bona-fide Heyting algebra, and if `T` is classical it is a Boolean
algebra.
-/

/-! ### Order theoretic results

The following amount to showing that "Propositions modulo equivalence" form a Heyting algebra: that
the operations are well-defined on equivalence classes, and the validity of the axioms.
-/

namespace PL

open Proposition Theory Derivation

variable {Atom : Type _} [DecidableEq Atom] {T : Theory Atom}

theorem Theory.le_wd (A B A' B' : Proposition Atom) (hA : A ≡[T] A') (hB : B ≡[T] B') :
    {A} ⊢[T] B ↔ {A'} ⊢[T] B' := by
  trans {A'} ⊢[T] B
  · exact T.equiv_iff_equiv_hypothesis.mp hA ∅ B
  · exact T.equiv_iff_equiv_conclusion.mp hB {A'}

theorem Theory.le_refl {A : Proposition Atom} : {A} ⊢[T] A := ⟨ass <| by grind⟩

theorem Theory.le_trans {A B C : Proposition Atom} (hAB : {A} ⊢[T] B)
    (hBC : {B} ⊢[T] C) : {A} ⊢[T] C := hAB.cut (Δ := ∅) hBC

theorem Theory.le_antisymm {A B : Proposition Atom} (hAB : {A} ⊢[T] B)
    (hBA : {B} ⊢[T] A) : A ≡[T] B := by grind

theorem Theory.inf_wd (A B A' B' : Proposition Atom) :
    A ≡[T] A' → B ≡[T] B' → (A ⋏ B) ≡[T] (A' ⋏ B')
  | ⟨D,D'⟩, ⟨E,E'⟩ => by
    constructor; constructor
    · apply conjI
      · refine Theory.Derivation.cut (Γ := {A ⋏ B}) (Δ := ∅) ?_ D
        exact conjE₁ (B := B) <| ass <| by grind
      · refine Theory.Derivation.cut (Γ := {A ⋏ B}) (Δ := ∅) ?_ E
        exact conjE₂ (A := A) <| ass <| by grind
    · apply conjI
      · refine Theory.Derivation.cut (Γ := {A' ⋏ B'}) (Δ := ∅) ?_ D'
        exact conjE₁ (B := B') <| ass <| by grind
      · refine Theory.Derivation.cut (Γ := {A' ⋏ B'}) (Δ := ∅) ?_ E'
        exact conjE₂ (A := A') <| ass <| by grind

theorem Theory.sup_wd (A B A' B' : Proposition Atom) :
    A ≡[T] A' → B ≡[T] B' → (A ⋎ B) ≡[T] (A' ⋎ B')
  | ⟨D,D'⟩, ⟨E,E'⟩ => by
    constructor; constructor
    · apply disjE (A := A) (B := B) (ass <| by grind)
      · apply disjI₁
        exact D.weak_ctx (by grind)
      · apply disjI₂
        exact E.weak_ctx (by grind)
    · apply disjE (A := A') (B := B') (ass <| by grind)
      · apply disjI₁
        exact D'.weak_ctx (by grind)
      · apply disjI₂
        exact E'.weak_ctx (by grind)

theorem Theory.inf_le_left {A B : Proposition Atom} : {A ⋏ B} ⊢[T] A :=
  ⟨conjE₁ (B := B) <| ass <| by grind⟩

theorem Theory.inf_le_right {A B : Proposition Atom} : {A ⋏ B} ⊢[T] B :=
  ⟨conjE₂ (A := A) <| ass <| by grind⟩

theorem Theory.le_inf {A B C : Proposition Atom} :
    {A} ⊢[T] B → {A} ⊢[T] C → {A} ⊢[T] (B ⋏ C)
  | ⟨D⟩, ⟨E⟩ => ⟨conjI (D.weak_ctx <| by grind) (E.weak_ctx <| by grind)⟩

theorem Theory.le_sup_left {A B : Proposition Atom} : {A} ⊢[T] (A ⋎ B) :=
  ⟨disjI₁ <| ass <| by grind⟩

theorem Theory.le_sup_right {A B : Proposition Atom} : {B} ⊢[T] (A ⋎ B) :=
  ⟨disjI₂ <| ass <| by grind⟩

theorem Theory.sup_le {A B C : Proposition Atom} :
    {A} ⊢[T] C → {B} ⊢[T] C → {A ⋎ B} ⊢[T] C
  | ⟨D⟩, ⟨E⟩ =>
    ⟨disjE (A := A) (B := B) (ass <| by grind) (D.weak_ctx <| by grind) (E.weak_ctx <| by grind)⟩

theorem Theory.le_top [Inhabited Atom] {A : Proposition Atom} : {A} ⊢[T] ⊤ :=
  ⟨derivationTop.weak_ctx (by grind)⟩

theorem Theory.bot_le [Bot Atom] {A : Proposition Atom} [IsIntuitionistic T] :
    {⊥} ⊢[T] A := ⟨implE (A := ⊥) (ax <| by grind) (ass <| by grind)⟩

theorem Theory.himp_wd (A B A' B' : Proposition Atom) :
    A ≡[T] A' → B ≡[T] B' → (A ⟶ B) ≡[T] (A' ⟶ B')
  | ⟨eA⟩, ⟨eB⟩ => by
    constructor; constructor
    · apply implI
      apply mapEquivConclusion _ eB
      apply implE (A := A)
      · exact ass <| by grind
      · apply mapEquivConclusion _ (commEquiv eA)
        exact ass <| by grind
    · apply implI
      apply mapEquivConclusion _ (commEquiv eB)
      apply implE (A := A')
      · exact ass <| by grind
      · apply mapEquivConclusion _ eA
        exact ass <| by grind

theorem Theory.le_himp_iff {A B C : Proposition Atom} :
    {A} ⊢[T] (B ⟶ C) ↔ {A ⋏ B} ⊢[T] C := by
  constructor <;> intro ⟨D⟩ <;> constructor
  · apply implE (A := B)
    · refine Theory.Derivation.cut (Γ := {A ⋏ B}) (Δ := ∅) ?_ D
      exact conjE₁ (B := B) <| ass <| by grind
    · exact conjE₂ (A := A) <| ass <| by grind
  · apply implI
    rw [← show ({B,A} : Ctx Atom) ∪ ∅ = {B,A} by grind]
    refine Theory.Derivation.cut (Γ := {B,A}) (Δ := ∅) ?_ D
    apply conjI <;> exact ass <| by grind

theorem Theory.compl_wd [Bot Atom] (A A' : Proposition Atom) :
    A ≡[T] A' → (~A) ≡[T] (~A') := (Theory.himp_wd A ⊥ A' ⊥ · (equivalent_refl ⊥))

theorem lem [Bot Atom] [IsClassical T] {A : Proposition Atom} : ⊢[T] (A ⋎ (~A)) := by
  constructor
  apply implE (A := ~~(A ⋎ ~A)) (ax <| by grind)
  apply implI
  apply implE (A := A ⋎ ~A) (ass <| by grind)
  apply disjI₂
  apply implI
  refine implE (A := A) ?_ (ass <| by grind)
  apply implI
  apply implE (A := A ⋎ ~A) (ass <| by grind)
  apply disjI₁
  exact ass <| by grind

end PL
