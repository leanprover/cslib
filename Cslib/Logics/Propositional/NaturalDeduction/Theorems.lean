/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Elementary derivations and equivalences in NJ -/

variable {Atom : Type u} [DecidableEq Atom]

namespace PL

open Proposition

namespace NJ

open Derivation

/-!
### Negation theorems

The following are valid in minimal logic, so we use `impl (-) C` over `~(-) := impl (-) bot`.
-/

/-- Double negation introduction -/
def Derivation.dni {A B : Proposition Atom} : Derivation ⟨{A}, impl (impl A B) B⟩ :=
  implI (A := A.impl B) _ <|
  implE (A := A) (ax' (by grind)) (ax' (by grind))

theorem SDerivable.dni {A B : Proposition Atom} : SDerivable ⟨{A},impl (impl A B) B⟩ :=
  sDerivable_iff.mpr ⟨Derivation.dni⟩

/-- The double negation of excluded-middle, or in minimal-logic-style ⊢ (A ∨ (A → B)) → B → B. -/
def Derivation.notNotLEM {A B : Proposition Atom} :
    Derivation ⟨∅, (A.disj <| impl A B).impl B |>.impl B⟩ :=
  implI _ <|
  implE (A := A.disj (A.impl B)) (ax' <| by grind) <|
  disjI₂ <|
  implI _ <|
  implE (A := A.disj (A.impl B)) (ax' <| by grind) <|
  disjI₁ <|
  ax' <| by grind

theorem Derivable.not_not_lem {A B : Proposition Atom} :
    SDerivable ⟨∅, (A.disj <| impl A B).impl B |>.impl B⟩ :=
  sDerivable_iff.mpr ⟨Derivation.notNotLEM⟩

/-- Triple negation elimination -/
def Derivation.tne {A B : Proposition Atom} :
    Derivation ⟨{((A.impl B).impl B).impl B}, A.impl B⟩ :=
  implI _ <|
  implE (A := (A.impl B).impl B) (ax' <| by grind) <|
  Derivation.dni.weak' (Γ := {A}) (by grind)

theorem Derivable.tne {A B : Proposition Atom} :
    SDerivable ⟨{((A.impl B).impl B).impl B}, A.impl B⟩ := sDerivable_iff.mpr ⟨Derivation.tne⟩

def tneEquiv {A B : Proposition Atom} :
    Proposition.equiv (A.impl B) (((A.impl B).impl B).impl B) := ⟨Derivation.dni, Derivation.tne⟩

theorem tne_equivalent {A B : Proposition Atom} :
    Equiv (A.impl B) (((A.impl B).impl B).impl B) := equiv_iff.mpr ⟨tneEquiv⟩

/-- Modus tollens -/
def Derivation.modusTollens {Γ : Ctx Atom} {A B : Proposition Atom} (C : Proposition Atom)
    (D : Derivation ⟨insert A Γ, B⟩) : Derivation ⟨insert (B.impl C) Γ, A.impl C⟩ :=
  implI _ <|
  implE (A := B)
    (ax' (by grind))
    (D.weak' (h := by grind))

theorem Derivable.modus_tollens {Γ : Ctx Atom} {A B : Proposition Atom} (C : Proposition Atom)
    (h : SDerivable ⟨insert A Γ, B⟩) : SDerivable ⟨insert (B.impl C) Γ, A.impl C⟩ :=
  let ⟨D⟩ := sDerivable_iff.mp h; sDerivable_iff.mpr ⟨D.modusTollens C⟩

/-!
### De Morgan laws

The following are valid in minimal logic, so we use `impl (-) C` over `~(-) := impl (-) bot`.
-/

/-- (A → C) ∧ (B → C) ⊢ (A ∨ B) → C -/
def disjImpOfConjImps {A B C : Proposition Atom} :
    Derivation ⟨{conj (impl A C) (impl B C)}, impl (disj A B) C⟩ :=
  implI _ <|
  disjE (A := A) (B := B)
    (ax _ _)
    (implE (A := A)
      (conjE₁ (B := B.impl C) (ax' <| by grind))
      (ax _ _))
    (implE (A := B)
      (conjE₂ (A := A.impl C) (ax' (by grind)))
      (ax _ _))

/-- (A → C) ∧ (B → C) ⊢ (A ∨ B) → C -/
theorem disj_imp_of_conj_imps {A B C : Proposition Atom} :
    SDerivable ⟨{conj (impl A C) (impl B C)}, impl (disj A B) C⟩ :=
  sDerivable_iff.mpr ⟨disjImpOfConjImps⟩

/-- (A ∨ B) → C ⊢ (A → C) ∧ (B → C) -/
def conjImpsOfDisjImp {A B C : Proposition Atom} :
    Derivation ⟨{impl (disj A B) C}, conj (impl A C) (impl B C)⟩ :=
  conjI
    (implI {impl (disj A B) C} <|
      implE (A := A.disj B) (B := C)
        (ax' (by grind))
        (disjI₁ (ax _ _)))
    (implI {impl (disj A B) C} <|
      implE (A := A.disj B) (B := C)
        (ax' (by grind))
        (disjI₂ (ax _ _)))

/-- (A ∨ B) → C ⊢ (A → C) ∧ (B → C) -/
theorem conj_imps_of_disj_imp {A B C : Proposition Atom} :
    SDerivable ⟨{impl (disj A B) C}, conj (impl A C) (impl B C)⟩ :=
  sDerivable_iff.mpr ⟨conjImpsOfDisjImp⟩

def disjImpConjImpsEquiv {A B C : Proposition Atom} :
    Proposition.equiv (impl (disj A B) C) (conj (impl A C) (impl B C)) :=
  ⟨conjImpsOfDisjImp, disjImpOfConjImps⟩

theorem disj_imp_conj_imps_equivalent {A B C : Proposition Atom} :
    Equiv (impl (disj A B) C) (conj (impl A C) (impl B C)) :=
  equiv_iff.mpr ⟨disjImpConjImpsEquiv⟩

/-- (A → C) ∨ (B → C) ⊢ (A ∧ B) → C -/
def conjImpOfDisjImps {A B C : Proposition Atom} :
    Derivation ⟨{disj (impl A C) (impl B C)}, impl (conj A B) C⟩ := by
  apply implI
  apply disjE (A := A.impl C) (B := B.impl C)
  · exact ax' (by grind)
  · apply implE (A := A)
    · apply ax
    · apply conjE₁ (B := B)
      exact ax' (by grind)
  · apply implE (A := B)
    · apply ax
    · apply conjE₂ (A := A)
      exact ax' (by grind)

/-- (A → C) ∨ (B → C) ⊢ (A ∧ B) → C -/
theorem conj_imp_of_disj_imps {A B C : Proposition Atom} :
    SDerivable ⟨{disj (impl A C) (impl B C)}, impl (conj A B) C⟩ :=
  sDerivable_iff.mpr ⟨conjImpOfDisjImps⟩

/-! ### Further equivalences and implications -/

/-- Equivalence of A → (B → C) and (A ∧ B) → C -/
def curryEquiv {A B C : Proposition Atom} :
    Proposition.equiv (A.impl (B.impl C)) (impl (A.conj B) C) := by
  constructor
  · apply implI
    apply implE (A := B)
    · apply implE (A := A)
      · exact ax' (by grind)
      · apply conjE₁ (B := B)
        exact ax' (by grind)
    · apply conjE₂ (A := A)
      exact ax' (by grind)
  · apply implI
    apply implI
    apply implE (A := A.conj B)
    · exact ax' (by grind)
    · apply conjI <;> exact ax' (by grind)

/-- Equivalence of A → (B → C) and (A ∧ B) → C -/
theorem curry_equiv {A B C : Proposition Atom} :
    Equiv (A.impl (B.impl C)) (impl (A.conj B) C) := equiv_iff.mpr ⟨curryEquiv⟩

/-- A ∧ B ⊢ B ∧ A -/
def conjCommDer {A B : Proposition Atom} : Derivation ⟨{A.conj B}, B.conj A⟩ := by
  apply conjI
  · apply conjE₂ (A := A)
    exact ax' (by grind)
  · apply conjE₁ (B := B)
    exact ax' (by grind)

/-- Equivalence of A ∧ B and B ∧ A -/
def conjCommEquiv {A B : Proposition Atom} : Proposition.equiv (A.conj B) (B.conj A) :=
  ⟨conjCommDer, conjCommDer⟩

/-- Equivalence of A ∧ B and B ∧ A -/
theorem conj_comm_equiv {A B : Proposition Atom} : Equiv (A.conj B) (B.conj A) :=
  equiv_iff.mpr ⟨conjCommEquiv⟩

/-- Equivalence of A ∧ A and A -/
def conjIdemEquiv {A : Proposition Atom} : Proposition.equiv (A.conj A) A := by
  constructor
  · apply conjE₁ (B := A)
    exact ax' (by grind)
  · apply conjI <;> exact ax' (by grind)

/-- Equivalence of A ∧ A and A -/
theorem conj_idem_equiv {A : Proposition Atom} : Equiv (A.conj A) A :=
  equiv_iff.mpr ⟨conjIdemEquiv⟩

/-- A ∨ B ⊢ B ∨ A -/
def disjCommDer {A B : Proposition Atom} : Derivation ⟨{A.disj B}, B.disj A⟩ := by
  apply disjE (A := A) (B := B)
  · exact ax' (by grind)
  · apply disjI₂
    exact ax' (by grind)
  · apply disjI₁
    exact ax' (by grind)

/-- Equivalence of A ∨ B and B ∨ A -/
def disjCommEquiv {A B : Proposition Atom} : Proposition.equiv (A.disj B) (B.disj A) :=
  ⟨disjCommDer, disjCommDer⟩

/-- Equivalence of A ∨ B and B ∨ A -/
theorem disj_comm_equiv {A B : Proposition Atom} : Equiv (A.disj B) (B.disj A) :=
  equiv_iff.mpr ⟨disjCommEquiv⟩

/-- Equivalence of A ∨ A and A -/
def disjIdemEquiv {A : Proposition Atom} : Proposition.equiv (A.disj A) A := by
  constructor
  · apply disjE (A := A) (B := A) <;> exact ax' (by grind)
  · apply disjI₁
    exact ax' (by grind)

/-- Equivalence of A ∨ A and A -/
theorem disj_idem_equiv {A : Proposition Atom} : Equiv (A.disj A) A :=
  equiv_iff.mpr ⟨disjIdemEquiv⟩

/-- Equivalence of A → (A → B) and A → B -/
def implIdemEquiv {A B : Proposition Atom} :
    Proposition.equiv (A.impl <| A.impl B) (A.impl B) := by
  constructor
  · apply implI
    apply implE (A := A)
    · apply implE (A := A)
      · exact ax' (by grind)
      · exact ax' (by grind)
    · exact ax' (by grind)
  · apply implI
    exact ax' (by grind)

/-- Equivalence of A → (A → B) and A → B -/
theorem impl_idem_equiv {A B : Proposition Atom} :
    Equiv (A.impl <| A.impl B) (A.impl B) := equiv_iff.mpr ⟨implIdemEquiv⟩

/-- A → (B → C) ⊢ B → (A → C) -/
def implSwapDer {A B C : Proposition Atom} :
    Derivation ⟨{A.impl <| B.impl C}, B.impl (A.impl C)⟩ := by
  apply implI
  apply implI
  apply implE (A := B)
  · apply implE (A := A) <;> exact ax' (by grind)
  · exact ax' (by grind)

/-- Equivalence of A → (B → C) and B → (A → C) -/
def implSwapEquiv {A B C : Proposition Atom} :
    Proposition.equiv (A.impl <| B.impl C) (B.impl (A.impl C)) := ⟨implSwapDer, implSwapDer⟩

/-- Equivalence of A → (B → C) and B → (A → C) -/
theorem impl_swap_equiv {A B C : Proposition Atom} :
    Equiv (A.impl <| B.impl C) (B.impl (A.impl C)) := equiv_iff.mpr ⟨implSwapEquiv⟩

/-- A → (B → C) ⊢ (A → B) → (A → C) -/
def implImplDistrib {A B C : Proposition Atom} :
    Derivation ⟨{A.impl (B.impl C)}, impl (A.impl B) (A.impl C)⟩ := by
  apply implI
  apply implI
  apply implE (A := B) <;> apply implE (A := A) <;> exact ax' (by grind)

theorem impl_impl_distrib {A B C : Proposition Atom} :
    SDerivable ⟨{A.impl (B.impl C)}, impl (A.impl B) (A.impl C)⟩ :=
  sDerivable_iff.mpr ⟨implImplDistrib⟩

/-- Equivalence of A ∧ (A ∨ B) and A -/
def absorbConjDisj {A B : Proposition Atom} : Proposition.equiv (A.conj <| (A.disj B)) A := by
  constructor
  · apply conjE₁ (B := (A.disj B))
    exact ax' (by grind)
  · apply conjI
    · exact ax' (by grind)
    · apply disjI₁
      exact ax' (by grind)

/-- Equivalence of A ∧ (A ∨ B) and A -/
theorem absorb_conj_disj {A B : Proposition Atom} : Equiv (A.conj <| (A.disj B)) A :=
  equiv_iff.mpr ⟨absorbConjDisj⟩

/-- Equivalence of A ∨ (A ∧ B) and A -/
def absorbDisjConj {A B : Proposition Atom} : Proposition.equiv (A.disj <| A.conj B) A := by
  constructor
  · apply disjE (A := A) (B := A.conj B)
    · exact ax' (by grind)
    · exact ax' (by grind)
    · apply conjE₁ (B := B)
      exact ax' (by grind)
  · apply disjI₁
    exact ax' (by grind)

/-- Equivalence of A ∨ (A ∧ B) and A -/
theorem absorb_disj_conj {A B : Proposition Atom} :  Equiv (A.disj <| A.conj B) A :=
  equiv_iff.mpr ⟨absorbDisjConj⟩

/-- Falsum is absorbing for conjunction -/
theorem bot_conj_absorb (T : Theory Atom) {A : Proposition Atom} [IsIntuitionistic T] :
  T.Equiv (A.conj bot) bot := by
  constructor
  · refine ⟨∅, by grind, ?_⟩
    apply implI
    apply conjE₂ (A := A)
    exact ax' (by grind)
  · refine ⟨{bot.impl A}, by grind [IsIntuitionistic], ?_⟩
    apply implI
    apply conjI
    · apply implE (A := bot)
      · exact ax' (by grind)
      · exact ax ..
    · exact ax' (by grind)

/-- Falsum is neutral for disjunction -/
theorem bot_disj_neutral (T : Theory Atom) {A : Proposition Atom} [IsIntuitionistic T] :
    T.Equiv (A.disj bot) A := by
  constructor
  · refine ⟨{impl bot A}, by grind [IsIntuitionistic], ?_⟩
    apply implI
    apply disjE (A := A) (B := bot)
    · exact ax' (by grind)
    · exact ax' (by grind)
    · apply implE (A := bot)
      · exact ax' (by grind)
      · exact ax' (by grind)
  · refine ⟨∅, by grind, ?_⟩
    apply implI
    apply disjI₁
    exact ax ..

/-! ### Partial order, lattice, and Heyting algebra results

The following amount to showing that "Propositions modulo equivalence" form a Heyting algebra: that
the operations are well-defined on equivalence classes, and the validity of the axioms.
-/

section OrderTheory

variable (T : Theory Atom)

theorem Theory.le_wd {A A' B B' : Proposition Atom} (hA : T.Equiv A A') (hB : T.Equiv B B') :
    T.Derivable (A.impl B) ↔ T.Derivable (A'.impl B') := by
  constructor <;> intro h
  · exact hA.2.trans h |>.trans hB.1
  · exact hA.1.trans h |>.trans hB.2

theorem Theory.le_refl {A : Proposition Atom} : T.Derivable (A.impl A) := by
  refine ⟨∅, by grind, ?_⟩
  apply implI
  exact ax _ _

theorem Theory.le_trans {A B C : Proposition Atom} (hAB : T.Derivable (A.impl B))
    (hBC : T.Derivable (B.impl C)) : T.Derivable (A.impl C) := hAB.trans hBC

theorem Theory.le_antisymm {A B : Proposition Atom} (hAB : T.Derivable (A.impl B))
    (hBA : T.Derivable (B.impl A)) : T.Equiv A B := ⟨hAB, hBA⟩

theorem Theory.inf_wd {A A' B B' : Proposition Atom} :
    T.Equiv A A' → T.Equiv B B' → T.Equiv (A.conj B) (A'.conj B')
  | ⟨⟨ΓA, hA, DA⟩, ⟨ΓA', hA', DA'⟩⟩, ⟨⟨ΓB, hB, DB⟩, ⟨ΓB', hB', DB'⟩⟩ => by
    constructor
    · refine ⟨ΓA ∪ ΓB, by grind, ?_⟩
      apply implI
      apply conjI
      · apply implE (A := A)
        · exact DA.weak' (by grind)
        · apply conjE₁ (B := B)
          apply ax' (by grind)
      · apply implE (A := B)
        · exact DB.weak' (by grind)
        · apply conjE₂ (A := A)
          apply ax' (by grind)
    · refine ⟨ΓA' ∪ ΓB', by grind, ?_⟩
      apply implI
      apply conjI
      · apply implE (A := A')
        · exact DA'.weak' (by grind)
        · apply conjE₁ (B := B')
          apply ax' (by grind)
      · apply implE (A := B')
        · exact DB'.weak' (by grind)
        · apply conjE₂ (A := A')
          apply ax' (by grind)

theorem Theory.sup_wd {A A' B B' : Proposition Atom} :
    T.Equiv A A' → T.Equiv B B' → T.Equiv (A.disj B) (A'.disj B')
  | ⟨⟨ΓA, hA, DA⟩, ⟨ΓA', hA', DA'⟩⟩, ⟨⟨ΓB, hB, DB⟩, ⟨ΓB', hB', DB'⟩⟩ => by
    constructor
    · refine ⟨ΓA ∪ ΓB, by grind, ?_⟩
      apply implI
      apply disjE (A := A) (B := B) (ax' <| by grind)
      · apply disjI₁
        apply implE (A := A)
        · exact DA.weak' (by grind)
        · exact ax ..
      · apply disjI₂
        apply implE (A := B)
        · exact DB.weak' (by grind)
        · exact ax ..
    · refine ⟨ΓA' ∪ ΓB', by grind, ?_⟩
      apply implI
      apply disjE (A := A') (B := B') (ax' <| by grind)
      · apply disjI₁
        apply implE (A := A')
        · exact DA'.weak' (by grind)
        · exact ax ..
      · apply disjI₂
        apply implE (A := B')
        · exact DB'.weak' (by grind)
        · exact ax ..

theorem Theory.inf_le_left {A B : Proposition Atom} : T.Derivable ((A.conj B).impl A) := by
  refine ⟨∅, by grind, ?_⟩
  apply implI
  apply conjE₁ (B := B)
  exact ax ..

theorem Theory.inf_le_right {A B : Proposition Atom} : T.Derivable ((A.conj B).impl B) := by
  refine ⟨∅, by grind, ?_⟩
  apply implI
  apply conjE₂ (A := A)
  exact ax ..

theorem Theory.le_inf {A B C : Proposition Atom} :
    T.Derivable (A.impl B) → T.Derivable (A.impl C) → T.Derivable (A.impl (B.conj C))
  | ⟨Γ, h, D⟩, ⟨Γ', h', D'⟩ => by
    refine ⟨Γ ∪ Γ', by grind, ?_⟩
    apply implI
    apply conjI
    · apply implE (A := A)
      · exact D.weak' (by grind)
      · exact ax ..
    · apply implE (A := A)
      · exact D'.weak' (by grind)
      · exact ax ..

theorem Theory.le_sup_left {A B : Proposition Atom} : T.Derivable (A.impl (A.disj B)) := by
  refine ⟨∅, by grind, ?_⟩
  apply implI
  apply disjI₁
  exact ax ..

theorem Theory.le_sup_right {A B : Proposition Atom} : T.Derivable (B.impl (A.disj B)) := by
  refine ⟨∅, by grind, ?_⟩
  apply implI
  apply disjI₂
  exact ax ..

theorem Theory.sup_le {A B C : Proposition Atom} :
    T.Derivable (A.impl C) → T.Derivable (B.impl C) → T.Derivable (A.disj B |>.impl C)
  | ⟨Γ, h, D⟩, ⟨Γ', h', D'⟩ => by
    refine ⟨Γ ∪ Γ', by grind, ?_⟩
    apply implI
    apply disjE (A := A) (B := B)
    · exact ax ..
    · apply implE (A := A)
      · exact D.weak' (by grind)
      · exact ax ..
    · apply implE (A := B)
      · exact D'.weak' (by grind)
      · exact ax ..

theorem Theory.le_top {A : Proposition Atom} : T.Derivable (A.impl Proposition.top) := by
  refine ⟨∅, by grind, ?_⟩
  apply implI
  exact derivationTop.weak' (by grind)

theorem Theory.bot_le {A : Proposition Atom} [IsIntuitionistic T] : T.Derivable (bot.impl A) :=
  Theory.Derivable.ax' (by grind [IsIntuitionistic])

theorem Theory.himp_wd {A A' B B' : Proposition Atom} :
    T.Equiv A A' → T.Equiv B B' → T.Equiv (A.impl B) (A'.impl B')
  | ⟨⟨ΓA, hA, DA⟩, ⟨ΓA', hA', DA'⟩⟩, ⟨⟨ΓB, hB, DB⟩, ⟨ΓB', hB', DB'⟩⟩ => by
    constructor
    · refine ⟨ΓA' ∪ ΓB, by grind, ?_⟩
      apply implI; apply implI
      apply implE (A := B)
      · exact DB.weak' (by grind)
      · apply implE (A := A)
        · exact ax' (by grind)
        · apply implE (A := A')
          · exact DA'.weak' (by grind)
          · exact ax ..
    · refine ⟨ΓA ∪ ΓB', by grind, ?_⟩
      apply implI; apply implI
      apply implE (A := B')
      · exact DB'.weak' (by grind)
      · apply implE (A := A')
        · exact ax' (by grind)
        · apply implE (A := A)
          · exact DA.weak' (by grind)
          · exact ax ..

theorem Theory.le_himp_iff {A B C : Proposition Atom} :
    T.Derivable (A.impl (B.impl C)) ↔ T.Derivable ((A.conj B).impl C) := by
  apply T.equivalent_derivable
  apply Theory.Equiv.theory_weak (Theory.empty Atom) T (by grind)
  exact curry_equiv

end OrderTheory

end NJ

end PL
