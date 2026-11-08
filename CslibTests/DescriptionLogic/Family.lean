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

open Role Name

def woman : TAxiom Role Name := .equiv Woman (Person ∧ Female)
def man : TAxiom Role Name := .equiv Man (Person ∧ ¬Woman)
def mother : TAxiom Role Name := .equiv Mother (Woman ∧ ∃ hasChild . Person)
def father : TAxiom Role Name := .equiv Father (Man ∧ ∃ hasChild . Person)
def parent : TAxiom Role Name := .equiv Parent (Father ∨ Mother)
def grandmother : TAxiom Role Name :=
  .equiv Grandmother (Mother ∧ ∃ hasChild . Parent)
def motherWithoutDaughter : TAxiom Role Name :=
  .equiv MotherWithoutDaughter (Mother ∧ ∀ hasChild . (¬Woman))
def wife : TAxiom Role Name := .equiv Wife (Woman ∧ ∃ hasHusband . Man)

/-- The family TBox. -/
def family : TBox Role Name :=
  {woman, man, mother, father, parent, grandmother, motherWithoutDaughter, wife}

/-! ## Reasoning with the TBox -/

/-- Every mother is a person. -/
example : Entails Δ family (.incl Mother Person) := by
  intro I hI x
  have hM : Mother ≡[Proposition.Equiv I.toModal] (Woman ∧ ∃ hasChild . Person) :=
    hI mother (by simp [family])
  have hW : Woman ≡[Proposition.Equiv I.toModal] (Person ∧ Female) :=
    hI woman (by simp [family])
  rw [Proposition.equiv_iff_forall_iff] at hM hW
  rw [Satisfies.imp_iff_imp]
  grind

/-- Every grandmother is a parent. -/
example : Entails Δ family (.incl Grandmother Parent) := by
  intro I hI x
  have hG : Grandmother ≡[Proposition.Equiv I.toModal] (Mother ∧ ∃ hasChild . Parent) :=
    hI grandmother (by simp [family])
  have hP : Parent ≡[Proposition.Equiv I.toModal] (Father ∨ Mother) :=
    hI parent (by simp [family])
  rw [Proposition.equiv_iff_forall_iff] at hG hP
  rw [Satisfies.imp_iff_imp]
  grind

/-- Unfolding `Woman` under `∀hasChild.¬·`, by congruence of logical equivalence. -/
example : Entails Δ family
    (.equiv MotherWithoutDaughter (Mother ∧ ∀ hasChild . (¬(Person ∧ Female)))) := by
  intro I hI
  have hMWD : MotherWithoutDaughter ≡[Proposition.Equiv I.toModal]
      (Mother ∧ ∀ hasChild . (¬Woman)) :=
    hI motherWithoutDaughter (by simp [family])
  have hW : Woman ≡[Proposition.Equiv I.toModal] (Person ∧ Female) :=
    hI woman (by simp [family])
  -- The context `Mother ⊓ ∀hasChild.¬[·]`, where `∀R.φ` unfolds to `¬∃R.¬φ`.
  let ctx : HasContext.Context C :=
    Proposition.Context.andR Mother (.not (.dynDiamond (.not (.not .hole)) hasChild))
  exact IsTrans.trans _ _ _ hMWD
    ((LawfulCongruence.covariant (r := Proposition.Equiv I.toModal)).elim ctx hW)

/-! ## A concrete model

Ana and Bob are married and have a daughter, Carla, who has a son, Davi. -/

inductive Individual where
  | ana | bob | carla | davi
deriving DecidableEq, Inhabited

open Individual

instance : Fintype Individual := ⟨{ana, bob, carla, davi}, by intro x; cases x <;> decide⟩

def concP : Name → Individual → Prop
  | Person, _ => True
  | Female, p => p = ana ∨ p = carla
  | Woman, p => p = ana ∨ p = carla
  | Man, p => p = bob ∨ p = davi
  | Mother, p => p = ana ∨ p = carla
  | Father, p => p = bob
  | Parent, p => p = ana ∨ p = bob ∨ p = carla
  | Grandmother, p => p = ana
  | MotherWithoutDaughter, p => p = carla
  | Wife, p => p = ana

def roleP : Role → Individual → Individual → Prop
  | hasChild, x, y => (x = ana ∧ y = carla) ∨ (x = bob ∧ y = carla) ∨ (x = carla ∧ y = davi)
  | hasHusband, x, y => x = ana ∧ y = bob

def I : Interpretation Individual Role Name where
  conc A := {x | concP A x}
  role := roleP

/-- The interpretation `I` is a model of the family TBox. -/
theorem I_satisfiesTBox : I.SatisfiesTBox family := by
  intro ax hax
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff] at hax
  rcases hax with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [woman, man, mother, father, parent, grandmother, motherWithoutDaughter, wife,
      Interpretation.SatisfiesTAxiom]
    rw [Proposition.equiv_iff_forall_iff]
    simp only [Satisfies.alc_atom_iff_conc, Satisfies.and_iff_and, Satisfies.or_iff_or,
      Satisfies.not_iff_not, Satisfies.alc_exists_iff, Satisfies.alc_forall_iff, I,
      Set.mem_ofPred_eq, concP, roleP]
    decide

/-- The family TBox is consistent: `I` is a model. -/
example : Consistent Individual family := ⟨I, I_satisfiesTBox⟩

/-- Ana is a grandmother: an ABox assertion. Individual names are interpreted in the domain by
`id`, since here the names of individuals are the elements of the domain `Individual`. -/
example : I.SatisfiesAssertion id (.concept Grandmother ana) := by
  rw [Interpretation.SatisfiesAssertion, Satisfies.alc_atom_iff_conc]
  simp [I, concP]

/-- A small ABox: Ana is a grandmother and has Carla as a child, and Carla has a child. -/
def familyABox : ABox Role Name Individual :=
  {.concept Grandmother ana, .role hasChild ana carla,
    .concept (∃ hasChild . Person) carla}

/-- `I` satisfies the ABox. -/
example : I.SatisfiesABox id familyABox := by
  intro α hα
  simp only [familyABox, Set.mem_insert_iff, Set.mem_singleton_iff] at hα
  rcases hα with rfl | rfl | rfl <;>
    simp [Interpretation.SatisfiesAssertion, Satisfies.alc_exists_iff, I, concP, roleP]

end CslibTests.DL
