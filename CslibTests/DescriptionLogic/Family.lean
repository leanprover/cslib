/-
Copyright (c) 2026 Alexandre Rademaker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexandre Rademaker, Guilherme Lima
-/

import Cslib.Logics.DescriptionLogic.ALC.Basic
import Mathlib.Data.Fintype.Basic

/-! # The family TBox

The terminology of Fig. 2.2 in [Baader2007]:

```
Woman                  ≡ Person ⊓ Female
Man                    ≡ Person ⊓ ¬Woman
Mother                 ≡ Woman ⊓ ∃hasChild.Person
Father                 ≡ Man ⊓ ∃hasChild.Person
Parent                 ≡ Father ⊔ Mother
Grandmother            ≡ Mother ⊓ ∃hasChild.Parent
MotherWithManyChildren ≡ Mother ⊓ ≥3 hasChild
MotherWithoutDaughter  ≡ Mother ⊓ ∀hasChild.¬Woman
Wife                   ≡ Woman ⊓ ∃hasHusband.Man
```

The number restriction `≥3 hasChild` is not expressible in ALC (it is a graded modality, not a
`triangle`), so `MotherWithManyChildren` is left out.
-/

namespace CslibTests.DL

open Cslib Logic DL Modal
open scoped InferenceSystem Modal.Proposition Satisfies Congruence

inductive Role where
  | hasChild
  | hasHusband
deriving DecidableEq

inductive Name where
  | Person | Female
  | Woman | Man | Mother | Father | Parent | Grandmother | MotherWithoutDaughter | Wife
deriving DecidableEq

abbrev C := Concept Role Name

/-- Lifts a concept name to a concept. -/
abbrev n (A : Name) : C := .atom A

open Role Name

def woman : TAxiom Role Name := .equiv (n Woman) (n Person ∧ n Female)
def man : TAxiom Role Name := .equiv (n Man) (n Person ∧ ¬n Woman)
def mother : TAxiom Role Name := .equiv (n Mother) (n Woman ∧ d⟨hasChild⟩(n Person))
def father : TAxiom Role Name := .equiv (n Father) (n Man ∧ d⟨hasChild⟩(n Person))
def parent : TAxiom Role Name := .equiv (n Parent) (n Father ∨ n Mother)
def grandmother : TAxiom Role Name :=
  .equiv (n Grandmother) (n Mother ∧ d⟨hasChild⟩(n Parent))
def motherWithoutDaughter : TAxiom Role Name :=
  .equiv (n MotherWithoutDaughter) (n Mother ∧ d[hasChild](¬n Woman))
def wife : TAxiom Role Name := .equiv (n Wife) (n Woman ∧ d⟨hasHusband⟩(n Man))

/-- The family TBox. -/
def family : TBox Role Name :=
  {woman, man, mother, father, parent, grandmother, motherWithoutDaughter, wife}

/-! ## Reasoning with the TBox -/

/-- Every mother is a person. -/
example : Entails Δ family (.incl (n Mother) (n Person)) := by
  intro I hI x
  have hM : n Mother ≡[Proposition.Equiv I.toModal] (n Woman ∧ d⟨hasChild⟩(n Person)) :=
    hI mother (by simp [family])
  have hW : n Woman ≡[Proposition.Equiv I.toModal] (n Person ∧ n Female) :=
    hI woman (by simp [family])
  rw [Proposition.equiv_iff_forall_iff] at hM hW
  rw [Satisfies.imp_iff_imp]
  grind

/-- Every grandmother is a parent. -/
example : Entails Δ family (.incl (n Grandmother) (n Parent)) := by
  intro I hI x
  have hG : n Grandmother ≡[Proposition.Equiv I.toModal] (n Mother ∧ d⟨hasChild⟩(n Parent)) :=
    hI grandmother (by simp [family])
  have hP : n Parent ≡[Proposition.Equiv I.toModal] (n Father ∨ n Mother) :=
    hI parent (by simp [family])
  rw [Proposition.equiv_iff_forall_iff] at hG hP
  rw [Satisfies.imp_iff_imp]
  grind

/-- Unfolding `Woman` under `∀hasChild.¬·`, by congruence of logical equivalence. -/
example : Entails Δ family
    (.equiv (n MotherWithoutDaughter) (n Mother ∧ d[hasChild](¬(n Person ∧ n Female)))) := by
  intro I hI
  have hMWD : n MotherWithoutDaughter ≡[Proposition.Equiv I.toModal]
      (n Mother ∧ d[hasChild](¬n Woman)) :=
    hI motherWithoutDaughter (by simp [family])
  have hW : n Woman ≡[Proposition.Equiv I.toModal] (n Person ∧ n Female) :=
    hI woman (by simp [family])
  -- The context `Mother ⊓ ∀hasChild.¬[·]`, where `∀R.φ` unfolds to `¬∃R.¬φ`.
  let ctx : HasContext.Context C :=
    Proposition.Context.andR (n Mother) (.not (.dynDiamond (.not (.not .hole)) hasChild))
  exact IsTrans.trans _ _ _ hMWD
    ((LawfulCongruence.covariant (r := Proposition.Equiv I.toModal)).elim ctx hW)

/-! ## A concrete model

Ana and Bob are married and have a daughter, Carla, who has a son, Davi. -/

inductive Person where
  | ana | bob | carla | davi
deriving DecidableEq

open Person

instance : Fintype Person := ⟨{ana, bob, carla, davi}, by intro x; cases x <;> decide⟩

def concP : Name → Person → Prop
  | Name.Person, _ => True
  | Female, p => p = ana ∨ p = carla
  | Woman, p => p = ana ∨ p = carla
  | Man, p => p = bob ∨ p = davi
  | Mother, p => p = ana ∨ p = carla
  | Father, p => p = bob
  | Parent, p => p = ana ∨ p = bob ∨ p = carla
  | Grandmother, p => p = ana
  | MotherWithoutDaughter, p => p = carla
  | Wife, p => p = ana

def roleP : Role → Person → Person → Prop
  | hasChild, x, y => (x = ana ∧ y = carla) ∨ (x = bob ∧ y = carla) ∨ (x = carla ∧ y = davi)
  | hasHusband, x, y => x = ana ∧ y = bob

def I : Interpretation Person Role Name :=
  ⟨fun A => {x | concP A x}, roleP⟩

/-- The interpretation `I` is a model of the family TBox. -/
theorem I_isModel : I.IsModel family := by
  intro ax hax
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff] at hax
  rcases hax with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [woman, man, mother, father, parent, grandmother, motherWithoutDaughter, wife,
      Interpretation.Sat]
    rw [Proposition.equiv_iff_forall_iff]
    simp only [Satisfies.alc_atom_iff, Satisfies.and_iff_and, Satisfies.or_iff_or,
      Satisfies.not_iff_not, Satisfies.alc_exists_iff, Satisfies.alc_forall_iff, I,
      Set.mem_ofPred_eq, concP, roleP]
    decide

/-- Ana is a grandmother: an ABox assertion. -/
example : I.SatAssertion id (.concept (n Grandmother) ana) := by
  rw [Interpretation.SatAssertion, Satisfies.alc_atom_iff]
  simp [I, concP]

end CslibTests.DL
