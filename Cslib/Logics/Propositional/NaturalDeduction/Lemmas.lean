/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Miscellaneous natural-deduction derivations -/

/-! ### Partial order, lattice, and Heyting algebra results

The following amount to showing that "Propositions modulo equivalence" form a Heyting algebra: that
the operations are well-defined on equivalence classes, and the validity of the axioms.
-/

namespace PL

namespace NJ

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

/-! ### Converting between assumptions and axioms -/

def Theory.Derivation.axsToAss {T : Theory Atom} {Γ Δ : Ctx Atom} {B : Proposition Atom} :
    (T ∪ Δ).Derivation ⟨Γ, B⟩ → T.Derivation ⟨Γ ∪ Δ, B⟩
  | @ax _ _ _ _ B _ => by
    by_cases B ∈ Δ
    case pos => exact ass <| by grind
    case neg => exact ax <| by grind
  | ass _ => ass <| by grind
  | conjI D E => conjI (axsToAss D) (axsToAss E)
  | conjE₁ D => conjE₁ (axsToAss D)
  | conjE₂ D => conjE₂ (axsToAss D)
  | disjI₁ D => disjI₁ (axsToAss D)
  | disjI₂ D => disjI₂ (axsToAss D)
  | @disjE _ _ _ _ A' B C D E₁ E₂ => by
    refine disjE (axsToAss D) ?_ ?_
    · let E₁' : _ := axsToAss (B := C) E₁
      rw [Finset.insert_union] at E₁'
      assumption
    · let E₂' : _ := axsToAss (B := C) E₂
      rw [Finset.insert_union] at E₂'
      assumption
  | @implI _ _ _ A' B _ D => by
    let D' : _ := axsToAss (B := B) D
    rw [Finset.insert_union] at D'
    exact implI _ D'
  | implE D E => implE (axsToAss D) (axsToAss E)

theorem Theory.SDerivable.axs_to_ass {T : Theory Atom} {Γ Δ : Ctx Atom} {B : Proposition Atom} :
    Γ ⊢[T ∪ Δ] B → (Γ ∪ Δ) ⊢[T] B
  | ⟨D⟩ => ⟨Theory.Derivation.axsToAss D⟩

private lemma Finset.insert_sdiff_subset {α : Type _} [DecidableEq α] (x : α) (s t : Finset α) :
    insert x s \ t ⊆ insert x (s \ t) := by grind

private def Theory.Derivation.assToAxs' {T : Theory Atom} {Γ Δ : Ctx Atom} {B : Proposition Atom} :
    T.Derivation ⟨Γ, B⟩ → (T ∪ Δ).Derivation ⟨Γ \ Δ, B⟩
  | @ass _ _ _ _ B _ => by
    by_cases B ∈ Δ
    case pos =>
      exact ax <| by grind
    case neg =>
      exact ass <| by grind
  | ax _ => ax <| by grind
  | conjI D E => conjI (assToAxs' D) (assToAxs' E)
  | conjE₁ D => conjE₁ (assToAxs' D)
  | conjE₂ D => conjE₂ (assToAxs' D)
  | disjI₁ D => disjI₁ (assToAxs' D)
  | disjI₂ D => disjI₂ (assToAxs' D)
  | @disjE _ _ _ _ A' B C D E₁ E₂ =>
    disjE (assToAxs' D)
      ((assToAxs' (Δ := Δ) (B := C) E₁).weak_ctx <| Finset.insert_sdiff_subset A' Γ Δ)
      ((assToAxs' (Δ := Δ) (B := C) E₂).weak_ctx <| Finset.insert_sdiff_subset B Γ Δ)
  | @implI _ _ _ A' B _ D =>
    implI _ ((assToAxs' (Δ := Δ) (B := B) D).weak_ctx <| Finset.insert_sdiff_subset A' Γ Δ)
  | implE D E => implE (assToAxs' D) (assToAxs' E)

def Theory.Derivation.assToAxs {T : Theory Atom} {Γ Δ : Ctx Atom} {B : Proposition Atom}
    (D : T.Derivation ⟨Γ ∪ Δ, B⟩) : (T ∪ Δ).Derivation ⟨Γ, B⟩ := (assToAxs' D).weak_ctx <| by grind

theorem Theory.SDerivable.ass_to_axs {T : Theory Atom} {Γ Δ : Ctx Atom} {B : Proposition Atom} :
    (Γ ∪ Δ) ⊢[T] B → Γ ⊢[T ∪ Δ] B
  | ⟨D⟩ => ⟨Theory.Derivation.assToAxs D⟩

theorem Theory.SDerivable.iff_sDerivable_extension {Γ Δ : Ctx Atom} {B : Proposition Atom} :
    (Γ ∪ Δ) ⊢[T] B ↔ Γ ⊢[T ∪ Δ] B := ⟨Theory.SDerivable.ass_to_axs, Theory.SDerivable.axs_to_ass⟩


end NJ

end PL
