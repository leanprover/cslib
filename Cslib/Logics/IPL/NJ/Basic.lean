/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
import Cslib.Logics.IPL.NJ.Defs

/-! # Elementary derivations and equivalences in NJ -/

variable {Atom : Type u} [DecidableEq Atom]

namespace IPL

open Proposition

namespace NJ

open Derivation

/-!
### Negation theorems

The following are valid in minimal logic, so we use `impl (-) C` over `~(-) := impl (-) bot`.
-/

/-- Double negation introduction -/
def Derivation.dni {A B : Proposition Atom} : Derivation ⟨{A}, impl (impl A B) B⟩ := by
  apply implI (A := A.impl B)
  apply implE (A := A) <;> exact ax' (by grind)

theorem Derivable.dni {A B : Proposition Atom} : Derivable ⟨{A},impl (impl A B) B⟩ :=
  ⟨Derivation.dni⟩

/-- The double negation of excluded-middle, or in minimal-logic-style ⊢ (A ∨ (A → B)) → B → B. -/
def Derivation.notNotLEM {A B : Proposition Atom} :
    Derivation ⟨∅, (A.disj <| impl A B).impl B |>.impl B⟩ := by
  apply implI
  rw [insert_empty_eq]
  apply implE (A := A.disj (A.impl B)) (ax' <| by grind)
  apply disjI₂
  apply implI
  apply implE (A := A.disj (A.impl B)) (ax' <| by grind)
  apply disjI₁
  apply ax' <| by grind

theorem Derivable.not_not_lem {A B : Proposition Atom} :
    Derivable ⟨∅, (A.disj <| impl A B).impl B |>.impl B⟩ := ⟨Derivation.notNotLEM⟩

/-- Triple negation elimination -/
def Derivation.tne {A B : Proposition Atom} :
    Derivation ⟨{((A.impl B).impl B).impl B}, A.impl B⟩ := by
  apply implI
  apply implE (A := (A.impl B).impl B) (ax' <| by grind)
  exact Derivation.dni.weak' (Γ := {A}) (by grind)

theorem Derivable.tne {A B : Proposition Atom} :
    Derivable ⟨{((A.impl B).impl B).impl B}, A.impl B⟩ := ⟨Derivation.tne⟩

def tneEquiv {A B : Proposition Atom} :
    Proposition.equiv (A.impl B) (((A.impl B).impl B).impl B) := ⟨Derivation.dni, Derivation.tne⟩

theorem tne_equivalent {A B : Proposition Atom} :
    Proposition.Equiv (A.impl B) (((A.impl B).impl B).impl B) := ⟨Derivable.dni, Derivable.tne⟩

/-- Modus tollens -/
def Derivation.modusTollens {Γ : Ctx Atom} {A B : Proposition Atom} (C : Proposition Atom)
    (D : Derivation ⟨insert A Γ, B⟩) : Derivation ⟨insert (B.impl C) Γ, A.impl C⟩ := by
  apply implI
  apply implE (A := B)
  · exact ax' (by grind)
  · exact D.weak' (h := by grind)

theorem Derivable.modus_tollens {Γ : Ctx Atom} {A B : Proposition Atom} (C : Proposition Atom)
    (h : Derivable ⟨insert A Γ, B⟩) : Derivable ⟨insert (B.impl C) Γ, A.impl C⟩ :=
  let ⟨D⟩ := h; ⟨D.modusTollens C⟩

/-!
### De Morgan laws

The following are valid in minimal logic, so we use `impl (-) C` over `~(-) := impl (-) bot`.
-/

/-- (A → C) ∧ (B → C) ⊢ (A ∨ B) → C -/
def disjImpOfConjImps {A B C : Proposition Atom} :
    Derivation ⟨{conj (impl A C) (impl B C)}, impl (disj A B) C⟩ := by
  apply implI
  apply disjE (A := A) (B := B)
  · apply ax
  · apply implE (A := A)
    · apply conjE₁ (B := B.impl C)
      exact ax' (by grind)
    · apply ax
  · apply implE (A := B)
    · apply conjE₂ (A := A.impl C)
      exact ax' (by grind)
    · apply ax

/-- (A → C) ∧ (B → C) ⊢ (A ∨ B) → C -/
theorem disj_imp_of_conj_imps {A B C : Proposition Atom} :
    Derivable ⟨{conj (impl A C) (impl B C)}, impl (disj A B) C⟩ := ⟨disjImpOfConjImps⟩

/-- (A ∨ B) → C ⊢ (A → C) ∧ (B → C) -/
def conjImpsOfDisjImp {A B C : Proposition Atom} :
    Derivation ⟨{impl (disj A B) C}, conj (impl A C) (impl B C)⟩ := by
  apply conjI
  · apply implI
    apply implE (A := A.disj B)
    · exact ax' (by grind)
    · apply disjI₁
      apply ax
  · apply implI
    apply implE (A := A.disj B)
    · exact ax' (by grind)
    · apply disjI₂
      apply ax

/-- (A ∨ B) → C ⊢ (A → C) ∧ (B → C) -/
theorem conj_imps_of_disj_imp {A B C : Proposition Atom} :
    Derivable ⟨{impl (disj A B) C}, conj (impl A C) (impl B C)⟩ := ⟨conjImpsOfDisjImp⟩

def disjImpConjImpsEquiv {A B C : Proposition Atom} :
    Proposition.equiv (impl (disj A B) C) (conj (impl A C) (impl B C)) :=
  ⟨conjImpsOfDisjImp, disjImpOfConjImps⟩

theorem disj_imp_conj_imps_equivalent {A B C : Proposition Atom} :
    Proposition.Equiv (impl (disj A B) C) (conj (impl A C) (impl B C)) :=
  ⟨conj_imps_of_disj_imp, disj_imp_of_conj_imps⟩

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
    Derivable ⟨{disj (impl A C) (impl B C)}, impl (conj A B) C⟩ := ⟨conjImpOfDisjImps⟩

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
    Proposition.Equiv (A.impl (B.impl C)) (impl (A.conj B) C) := ⟨⟨curryEquiv.1⟩, ⟨curryEquiv.2⟩⟩

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
theorem conj_comm_equiv {A B : Proposition Atom} : Proposition.Equiv (A.conj B) (B.conj A) :=
  ⟨⟨conjCommDer⟩, ⟨conjCommDer⟩⟩

/-- Equivalence of A ∧ A and A -/
def conjIdemEquiv {A : Proposition Atom} : Proposition.equiv (A.conj A) A := by
  constructor
  · apply conjE₁ (B := A)
    exact ax' (by grind)
  · apply conjI <;> exact ax' (by grind)

/-- Equivalence of A ∧ A and A -/
theorem conj_idem_equiv {A : Proposition Atom} : Proposition.Equiv (A.conj A) A :=
  ⟨⟨conjIdemEquiv.1⟩, ⟨conjIdemEquiv.2⟩⟩

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
theorem disj_comm_equiv {A B : Proposition Atom} : Proposition.Equiv (A.disj B) (B.disj A) :=
  ⟨⟨disjCommDer⟩, ⟨disjCommDer⟩⟩

/-- Equivalence of A ∨ A and A -/
def disjIdemEquiv {A : Proposition Atom} : Proposition.equiv (A.disj A) A := by
  constructor
  · apply disjE (A := A) (B := A) <;> exact ax' (by grind)
  · apply disjI₁
    exact ax' (by grind)

/-- Equivalence of A ∨ A and A -/
theorem disj_idem_equiv {A : Proposition Atom} : Proposition.Equiv (A.disj A) A :=
  ⟨⟨disjIdemEquiv.1⟩, ⟨disjIdemEquiv.2⟩⟩

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
    Proposition.Equiv (A.impl <| A.impl B) (A.impl B) := ⟨⟨implIdemEquiv.1⟩, ⟨implIdemEquiv.2⟩⟩

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

/-- A → (B → C) ⊢ (A → B) → (A → C) -/
def implImplDistrib {A B C : Proposition Atom} :
    Derivation ⟨{A.impl (B.impl C)}, impl (A.impl B) (A.impl C)⟩ := by
  apply implI
  apply implI
  apply implE (A := B) <;> apply implE (A := A) <;> exact ax' (by grind)

theorem impl_impl_distrib {A B C : Proposition Atom} :
    Derivable ⟨{A.impl (B.impl C)}, impl (A.impl B) (A.impl C)⟩ := ⟨implImplDistrib⟩

/-- Equivalence of A → (B → C) and B → (A → C) -/
theorem impl_swap_equiv {A B C : Proposition Atom} :
    Proposition.Equiv (A.impl <| B.impl C) (B.impl (A.impl C)) := ⟨⟨implSwapDer⟩, ⟨implSwapDer⟩⟩

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
theorem absorb_conj_disj {A B : Proposition Atom} : Proposition.Equiv (A.conj <| (A.disj B)) A :=
  ⟨⟨absorbConjDisj.1⟩, ⟨absorbConjDisj.2⟩⟩

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
theorem absorb_disj_conj {A B : Proposition Atom} :  Proposition.Equiv (A.disj <| A.conj B) A :=
  ⟨⟨absorbDisjConj.1⟩, ⟨absorbDisjConj.2⟩⟩

/-- Falsum is absorbing for conjunction -/
def botConjAbsorb {A : Proposition Atom} : Proposition.equiv (A.conj bot) bot := by
  constructor
  · apply conjE₂ (A := A)
    exact ax' (by grind)
  · apply conjI
    · apply botE
      exact ax' (by grind)
    · exact ax' (by grind)

/-- Falsum is absorbing for conjunction -/
theorem bot_conj_absorb {A : Proposition Atom} : Proposition.Equiv (A.conj bot) bot :=
  ⟨⟨botConjAbsorb.1⟩, ⟨botConjAbsorb.2⟩⟩

/-- Falsum is neutral for disjunction -/
def botDisjNeutral {A : Proposition Atom} : Proposition.equiv (A.disj bot) A := by
  constructor
  · apply disjE (A := A) (B := bot)
    · exact ax' (by grind)
    · exact ax' (by grind)
    · apply botE
      exact ax' (by grind)
  · apply disjI₁
    exact ax' (by grind)

/-- Falsum is neutral for disjunction -/
theorem bot_disj_neutral {A : Proposition Atom} : Proposition.Equiv (A.disj bot) A :=
  ⟨⟨botDisjNeutral.1⟩, ⟨botDisjNeutral.2⟩⟩

end NJ

end IPL
