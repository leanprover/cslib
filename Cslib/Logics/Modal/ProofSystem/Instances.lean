/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.ProofSystem

/-! # Instance Registration for Modal Proof Systems (K, T, D, S4, S5)

This module registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the five standard normal modal logics, connecting the abstract typeclass
hierarchy (from `ProofSystem.lean`) to the concrete parameterized `DerivationTree`
(from `DerivationTree.lean`).

## Architecture

Each system has an axiom predicate (an inductive type enumerating its axiom schemata),
and instances are registered mapping the tag type to `DerivationTree` parameterized
over that predicate. For S5, the existing `ModalAxiom` is reused.

## Systems

| System | Tag Type | Axiom Predicate | Bundled Class |
|--------|----------|-----------------|---------------|
| K | `Modal.HilbertK` | `KAxiom` | `ModalHilbert` |
| T | `Modal.HilbertT` | `TAxiom` | `ModalTHilbert` |
| D | `Modal.HilbertD` | `DAxiom` | `ModalDHilbert` |
| S4 | `Modal.HilbertS4` | `S4Axiom` | `ModalS4Hilbert` |
| S5 | `Modal.HilbertS5` | `ModalAxiom` | `ModalS5Hilbert` |
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Axiom Predicates -/

namespace Cslib.Logic.Modal

/-- Axiom schemata for modal logic K.

The 5 axiom constructors cover:
- **Propositional** (4): `implyK` (weakening), `implyS` (distribution), `efq` (ex falso),
  `peirce` (double negation elimination / Peirce's law)
- **Modal** (1): `modalK` (K distribution) -/
inductive KAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      KAxiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      KAxiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      KAxiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      KAxiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      KAxiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))

/-- Axiom schemata for modal logic T.

The 6 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (2): `modalK` (K distribution), `modalT` (reflexivity) -/
inductive TAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      TAxiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      TAxiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      TAxiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      TAxiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      TAxiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- T / reflexivity: `□φ → φ` -/
  | modalT (φ : Proposition Atom) :
      TAxiom (Proposition.imp (Proposition.box φ) φ)

/-- Axiom schemata for modal logic D.

The 6 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (2): `modalK` (K distribution), `modalD` (seriality) -/
inductive DAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      DAxiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      DAxiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      DAxiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      DAxiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      DAxiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- D / seriality: `□φ → ◇φ` where `◇φ = (□(φ → ⊥)) → ⊥` -/
  | modalD (φ : Proposition Atom) :
      DAxiom (Proposition.imp (Proposition.box φ)
        (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot))

/-- Axiom schemata for modal logic S4.

The 7 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (3): `modalK` (K distribution), `modalT` (reflexivity), `modalFour` (transitivity) -/
inductive S4Axiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      S4Axiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      S4Axiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      S4Axiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      S4Axiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      S4Axiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- T / reflexivity: `□φ → φ` -/
  | modalT (φ : Proposition Atom) :
      S4Axiom (Proposition.imp (Proposition.box φ) φ)
  /-- 4 / transitivity: `□φ → □□φ` -/
  | modalFour (φ : Proposition Atom) :
      S4Axiom (Proposition.imp (Proposition.box φ) (Proposition.box (Proposition.box φ)))

/-- Axiom schemata for modal logic KB.

The 6 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (2): `modalK` (K distribution), `modalB` (symmetry) -/
inductive BAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      BAxiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      BAxiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      BAxiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      BAxiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      BAxiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- B / symmetry: `φ → □◇φ` -/
  | modalB (φ : Proposition Atom) :
      BAxiom (φ.imp (Proposition.box (Proposition.diamond φ)))

/-- Axiom schemata for modal logic K4.

The 6 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (2): `modalK` (K distribution), `modalFour` (transitivity) -/
inductive K4Axiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      K4Axiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      K4Axiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      K4Axiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      K4Axiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      K4Axiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- 4 / transitivity: `□φ → □□φ` -/
  | modalFour (φ : Proposition Atom) :
      K4Axiom (Proposition.imp (Proposition.box φ) (Proposition.box (Proposition.box φ)))

/-- Axiom schemata for modal logic K5.

The 6 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (2): `modalK` (K distribution), `modalFive` (Euclideanness) -/
inductive K5Axiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      K5Axiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      K5Axiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      K5Axiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      K5Axiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      K5Axiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- 5 / Euclideanness: `◇φ → □◇φ` -/
  | modalFive (φ : Proposition Atom) :
      K5Axiom (((Proposition.box (φ.imp .bot)).imp .bot).imp
        (Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot)))

/-- Axiom schemata for modal logic K45.

The 7 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (3): `modalK` (K distribution), `modalFour` (transitivity),
  `modalFive` (Euclideanness) -/
inductive K45Axiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      K45Axiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      K45Axiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      K45Axiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      K45Axiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      K45Axiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- 4 / transitivity: `□φ → □□φ` -/
  | modalFour (φ : Proposition Atom) :
      K45Axiom (Proposition.imp (Proposition.box φ) (Proposition.box (Proposition.box φ)))
  /-- 5 / Euclideanness: `◇φ → □◇φ` -/
  | modalFive (φ : Proposition Atom) :
      K45Axiom (((Proposition.box (φ.imp .bot)).imp .bot).imp
        (Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot)))

/-- Axiom schemata for modal logic TB.

The 7 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (3): `modalK` (K distribution), `modalT` (reflexivity),
  `modalB` (symmetry) -/
inductive TBAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      TBAxiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      TBAxiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      TBAxiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      TBAxiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      TBAxiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- T / reflexivity: `□φ → φ` -/
  | modalT (φ : Proposition Atom) :
      TBAxiom (Proposition.imp (Proposition.box φ) φ)
  /-- B / symmetry: `φ → □◇φ` -/
  | modalB (φ : Proposition Atom) :
      TBAxiom (φ.imp (Proposition.box (Proposition.diamond φ)))

/-- Axiom schemata for modal logic KB5.

The 7 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (3): `modalK` (K distribution), `modalB` (symmetry),
  `modalFive` (Euclideanness) -/
inductive KB5Axiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      KB5Axiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      KB5Axiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      KB5Axiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      KB5Axiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      KB5Axiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- B / symmetry: `φ → □◇φ` -/
  | modalB (φ : Proposition Atom) :
      KB5Axiom (φ.imp (Proposition.box (Proposition.diamond φ)))
  /-- 5 / Euclideanness: `◇φ → □◇φ` -/
  | modalFive (φ : Proposition Atom) :
      KB5Axiom (((Proposition.box (φ.imp .bot)).imp .bot).imp
        (Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot)))

/-- Axiom schemata for modal logic D4.

The 7 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (3): `modalK` (K distribution), `modalD` (seriality),
  `modalFour` (transitivity) -/
inductive D4Axiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      D4Axiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      D4Axiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      D4Axiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      D4Axiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      D4Axiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- D / seriality: `□φ → ◇φ` where `◇φ = (□(φ → ⊥)) → ⊥` -/
  | modalD (φ : Proposition Atom) :
      D4Axiom (Proposition.imp (Proposition.box φ)
        (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot))
  /-- 4 / transitivity: `□φ → □□φ` -/
  | modalFour (φ : Proposition Atom) :
      D4Axiom (Proposition.imp (Proposition.box φ) (Proposition.box (Proposition.box φ)))

/-- Axiom schemata for modal logic D5.

The 7 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (3): `modalK` (K distribution), `modalD` (seriality),
  `modalFive` (Euclideanness) -/
inductive D5Axiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      D5Axiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      D5Axiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      D5Axiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      D5Axiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      D5Axiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- D / seriality: `□φ → ◇φ` where `◇φ = (□(φ → ⊥)) → ⊥` -/
  | modalD (φ : Proposition Atom) :
      D5Axiom (Proposition.imp (Proposition.box φ)
        (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot))
  /-- 5 / Euclideanness: `◇φ → □◇φ` -/
  | modalFive (φ : Proposition Atom) :
      D5Axiom (((Proposition.box (φ.imp .bot)).imp .bot).imp
        (Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot)))

/-- Axiom schemata for modal logic D45.

The 8 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (4): `modalK` (K distribution), `modalD` (seriality),
  `modalFour` (transitivity), `modalFive` (Euclideanness) -/
inductive D45Axiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      D45Axiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      D45Axiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      D45Axiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      D45Axiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      D45Axiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- D / seriality: `□φ → ◇φ` where `◇φ = (□(φ → ⊥)) → ⊥` -/
  | modalD (φ : Proposition Atom) :
      D45Axiom (Proposition.imp (Proposition.box φ)
        (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot))
  /-- 4 / transitivity: `□φ → □□φ` -/
  | modalFour (φ : Proposition Atom) :
      D45Axiom (Proposition.imp (Proposition.box φ) (Proposition.box (Proposition.box φ)))
  /-- 5 / Euclideanness: `◇φ → □◇φ` -/
  | modalFive (φ : Proposition Atom) :
      D45Axiom (((Proposition.box (φ.imp .bot)).imp .bot).imp
        (Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot)))

/-- Axiom schemata for modal logic DB.

The 7 axiom constructors cover:
- **Propositional** (4): `implyK`, `implyS`, `efq`, `peirce`
- **Modal** (3): `modalK` (K distribution), `modalD` (seriality),
  `modalB` (symmetry) -/
inductive DBAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : Proposition Atom) :
      DBAxiom (Proposition.imp φ (Proposition.imp ψ φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : Proposition Atom) :
      DBAxiom (Proposition.imp (Proposition.imp φ (Proposition.imp ψ χ))
        (Proposition.imp (Proposition.imp φ ψ) (Proposition.imp φ χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : Proposition Atom) :
      DBAxiom (Proposition.imp Proposition.bot φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : Proposition Atom) :
      DBAxiom (Proposition.imp (Proposition.imp (Proposition.imp φ ψ) φ) φ)
  /-- K distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modalK (φ ψ : Proposition Atom) :
      DBAxiom (Proposition.imp (Proposition.box (Proposition.imp φ ψ))
        (Proposition.imp (Proposition.box φ) (Proposition.box ψ)))
  /-- D / seriality: `□φ → ◇φ` where `◇φ = (□(φ → ⊥)) → ⊥` -/
  | modalD (φ : Proposition Atom) :
      DBAxiom (Proposition.imp (Proposition.box φ)
        (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot))
  /-- B / symmetry: `φ → □◇φ` -/
  | modalB (φ : Proposition Atom) :
      DBAxiom (φ.imp (Proposition.box (Proposition.diamond φ)))

end Cslib.Logic.Modal

/-! ## Instance Registrations -/

section ModalInstances

/-! ### System K Instances -/

instance : InferenceSystem Modal.HilbertK
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.KAxiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertK
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertK
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertK
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.KAxiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertK
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.KAxiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertK
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.KAxiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertK
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.KAxiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertK
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.KAxiom.modalK _ _)⟩

instance :
    ModalHilbert Modal.HilbertK
      (F := Modal.Proposition Atom) where

/-! ### System T Instances -/

instance : InferenceSystem Modal.HilbertT
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.TAxiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertT
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertT
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertT
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertT
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertT
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertT
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertT
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.modalK _ _)⟩

instance :
    HasAxiomT Modal.HilbertT
      (F := Modal.Proposition Atom) where
  T := ⟨Modal.DerivationTree.ax [] _
    (Modal.TAxiom.modalT _)⟩

instance :
    ModalHilbert Modal.HilbertT
      (F := Modal.Proposition Atom) where

instance :
    ModalTHilbert Modal.HilbertT
      (F := Modal.Proposition Atom) where

/-! ### System D Instances -/

instance : InferenceSystem Modal.HilbertD
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.DAxiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertD
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertD
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertD
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.DAxiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertD
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.DAxiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertD
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.DAxiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertD
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.DAxiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertD
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.DAxiom.modalK _ _)⟩

instance :
    HasAxiomD Modal.HilbertD
      (F := Modal.Proposition Atom) where
  D := ⟨Modal.DerivationTree.ax [] _
    (Modal.DAxiom.modalD _)⟩

instance :
    ModalHilbert Modal.HilbertD
      (F := Modal.Proposition Atom) where

instance :
    ModalDHilbert Modal.HilbertD
      (F := Modal.Proposition Atom) where

/-! ### System S4 Instances -/

instance : InferenceSystem Modal.HilbertS4
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.S4Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertS4
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertS4
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertS4
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.S4Axiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertS4
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.S4Axiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertS4
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.S4Axiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertS4
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.S4Axiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertS4
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.S4Axiom.modalK _ _)⟩

instance :
    HasAxiomT Modal.HilbertS4
      (F := Modal.Proposition Atom) where
  T := ⟨Modal.DerivationTree.ax [] _
    (Modal.S4Axiom.modalT _)⟩

instance :
    HasAxiom4 Modal.HilbertS4
      (F := Modal.Proposition Atom) where
  four := ⟨Modal.DerivationTree.ax [] _
    (Modal.S4Axiom.modalFour _)⟩

instance :
    ModalHilbert Modal.HilbertS4
      (F := Modal.Proposition Atom) where

instance :
    ModalTHilbert Modal.HilbertS4
      (F := Modal.Proposition Atom) where

instance :
    ModalS4Hilbert Modal.HilbertS4
      (F := Modal.Proposition Atom) where

/-! ### System S5 Instances -/

instance : InferenceSystem Modal.HilbertS5
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.ModalAxiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.ModalAxiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.ModalAxiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.ModalAxiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.ModalAxiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.ModalAxiom.modalK _ _)⟩

instance :
    HasAxiomT Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  T := ⟨Modal.DerivationTree.ax [] _
    (Modal.ModalAxiom.modalT _)⟩

instance :
    HasAxiom4 Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  four := ⟨Modal.DerivationTree.ax [] _
    (Modal.ModalAxiom.modalFour _)⟩

instance :
    HasAxiomB Modal.HilbertS5
      (F := Modal.Proposition Atom) where
  B := ⟨Modal.DerivationTree.ax [] _
    (Modal.ModalAxiom.modalB _)⟩

instance :
    ModalHilbert Modal.HilbertS5
      (F := Modal.Proposition Atom) where

instance :
    ModalTHilbert Modal.HilbertS5
      (F := Modal.Proposition Atom) where

instance :
    ModalS4Hilbert Modal.HilbertS5
      (F := Modal.Proposition Atom) where

instance :
    ModalS5Hilbert Modal.HilbertS5
      (F := Modal.Proposition Atom) where

/-! ### System KB Instances -/

instance : InferenceSystem Modal.HilbertB
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.BAxiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertB
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertB
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertB
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.BAxiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertB
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.BAxiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertB
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.BAxiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertB
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.BAxiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertB
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.BAxiom.modalK _ _)⟩

instance :
    HasAxiomB Modal.HilbertB
      (F := Modal.Proposition Atom) where
  B := ⟨Modal.DerivationTree.ax [] _
    (Modal.BAxiom.modalB _)⟩

instance :
    ModalHilbert Modal.HilbertB
      (F := Modal.Proposition Atom) where

instance :
    ModalBHilbert Modal.HilbertB
      (F := Modal.Proposition Atom) where

/-! ### System K4 Instances -/

instance : InferenceSystem Modal.HilbertK4
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.K4Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertK4
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertK4
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertK4
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.K4Axiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertK4
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.K4Axiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertK4
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.K4Axiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertK4
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.K4Axiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertK4
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.K4Axiom.modalK _ _)⟩

instance :
    HasAxiom4 Modal.HilbertK4
      (F := Modal.Proposition Atom) where
  four := ⟨Modal.DerivationTree.ax [] _
    (Modal.K4Axiom.modalFour _)⟩

instance :
    ModalHilbert Modal.HilbertK4
      (F := Modal.Proposition Atom) where

instance :
    ModalK4Hilbert Modal.HilbertK4
      (F := Modal.Proposition Atom) where

/-! ### System K5 Instances -/

instance : InferenceSystem Modal.HilbertK5
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.K5Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.K5Axiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.K5Axiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.K5Axiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.K5Axiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.K5Axiom.modalK _ _)⟩

instance :
    HasAxiom5 Modal.HilbertK5
      (F := Modal.Proposition Atom) where
  five := ⟨Modal.DerivationTree.ax [] _
    (Modal.K5Axiom.modalFive _)⟩

instance :
    ModalHilbert Modal.HilbertK5
      (F := Modal.Proposition Atom) where

instance :
    ModalK5Hilbert Modal.HilbertK5
      (F := Modal.Proposition Atom) where

/-! ### System K45 Instances -/

instance : InferenceSystem Modal.HilbertK45
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.K45Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.K45Axiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.K45Axiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.K45Axiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.K45Axiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.K45Axiom.modalK _ _)⟩

instance :
    HasAxiom4 Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  four := ⟨Modal.DerivationTree.ax [] _
    (Modal.K45Axiom.modalFour _)⟩

instance :
    HasAxiom5 Modal.HilbertK45
      (F := Modal.Proposition Atom) where
  five := ⟨Modal.DerivationTree.ax [] _
    (Modal.K45Axiom.modalFive _)⟩

instance :
    ModalHilbert Modal.HilbertK45
      (F := Modal.Proposition Atom) where

instance :
    ModalK4Hilbert Modal.HilbertK45
      (F := Modal.Proposition Atom) where

instance :
    ModalK45Hilbert Modal.HilbertK45
      (F := Modal.Proposition Atom) where

/-! ### System TB Instances -/

instance : InferenceSystem Modal.HilbertTB
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.TBAxiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.TBAxiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.TBAxiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.TBAxiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.TBAxiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.TBAxiom.modalK _ _)⟩

instance :
    HasAxiomT Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  T := ⟨Modal.DerivationTree.ax [] _
    (Modal.TBAxiom.modalT _)⟩

instance :
    HasAxiomB Modal.HilbertTB
      (F := Modal.Proposition Atom) where
  B := ⟨Modal.DerivationTree.ax [] _
    (Modal.TBAxiom.modalB _)⟩

instance :
    ModalHilbert Modal.HilbertTB
      (F := Modal.Proposition Atom) where

instance :
    ModalTHilbert Modal.HilbertTB
      (F := Modal.Proposition Atom) where

instance :
    ModalTBHilbert Modal.HilbertTB
      (F := Modal.Proposition Atom) where

/-! ### System KB5 Instances -/

instance : InferenceSystem Modal.HilbertKB5
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.KB5Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.modalK _ _)⟩

instance :
    HasAxiomB Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  B := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.modalB _)⟩

instance :
    HasAxiom5 Modal.HilbertKB5
      (F := Modal.Proposition Atom) where
  five := ⟨Modal.DerivationTree.ax [] _
    (Modal.KB5Axiom.modalFive _)⟩

instance :
    ModalHilbert Modal.HilbertKB5
      (F := Modal.Proposition Atom) where

instance :
    ModalBHilbert Modal.HilbertKB5
      (F := Modal.Proposition Atom) where

instance :
    ModalKB5Hilbert Modal.HilbertKB5
      (F := Modal.Proposition Atom) where

/-! ### System D4 Instances -/

instance : InferenceSystem Modal.HilbertD4
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.D4Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.D4Axiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.D4Axiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.D4Axiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.D4Axiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.D4Axiom.modalK _ _)⟩

instance :
    HasAxiomD Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  D := ⟨Modal.DerivationTree.ax [] _
    (Modal.D4Axiom.modalD _)⟩

instance :
    HasAxiom4 Modal.HilbertD4
      (F := Modal.Proposition Atom) where
  four := ⟨Modal.DerivationTree.ax [] _
    (Modal.D4Axiom.modalFour _)⟩

instance :
    ModalHilbert Modal.HilbertD4
      (F := Modal.Proposition Atom) where

instance :
    ModalDHilbert Modal.HilbertD4
      (F := Modal.Proposition Atom) where

instance :
    ModalD4Hilbert Modal.HilbertD4
      (F := Modal.Proposition Atom) where

/-! ### System D5 Instances -/

instance : InferenceSystem Modal.HilbertD5
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.D5Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertD5
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertD5
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertD5
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.D5Axiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertD5
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.D5Axiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertD5
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.D5Axiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertD5
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.D5Axiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertD5
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.D5Axiom.modalK _ _)⟩

instance :
    HasAxiomD Modal.HilbertD5
      (F := Modal.Proposition Atom) where
  D := ⟨Modal.DerivationTree.ax [] _
    (Modal.D5Axiom.modalD _)⟩

instance :
    HasAxiom5 Modal.HilbertD5
      (F := Modal.Proposition Atom) where
  five := ⟨Modal.DerivationTree.ax [] _
    (Modal.D5Axiom.modalFive _)⟩

instance :
    ModalHilbert Modal.HilbertD5
      (F := Modal.Proposition Atom) where

instance :
    ModalDHilbert Modal.HilbertD5
      (F := Modal.Proposition Atom) where

instance :
    ModalD5Hilbert Modal.HilbertD5
      (F := Modal.Proposition Atom) where

/-! ### System D45 Instances -/

instance : InferenceSystem Modal.HilbertD45
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.D45Axiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.modalK _ _)⟩

instance :
    HasAxiomD Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  D := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.modalD _)⟩

instance :
    HasAxiom4 Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  four := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.modalFour _)⟩

instance :
    HasAxiom5 Modal.HilbertD45
      (F := Modal.Proposition Atom) where
  five := ⟨Modal.DerivationTree.ax [] _
    (Modal.D45Axiom.modalFive _)⟩

instance :
    ModalHilbert Modal.HilbertD45
      (F := Modal.Proposition Atom) where

instance :
    ModalDHilbert Modal.HilbertD45
      (F := Modal.Proposition Atom) where

instance :
    ModalD4Hilbert Modal.HilbertD45
      (F := Modal.Proposition Atom) where

instance :
    ModalD45Hilbert Modal.HilbertD45
      (F := Modal.Proposition Atom) where

/-! ### System DB Instances -/

instance : InferenceSystem Modal.HilbertDB
    (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.DBAxiom Atom) [] φ

instance :
    ModusPonens Modal.HilbertDB
      (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    Necessitation Modal.HilbertDB
      (F := Modal.Proposition Atom) where
  nec := fun h => by
    obtain ⟨d⟩ := h
    exact ⟨Modal.DerivationTree.necessitation _ d⟩

instance :
    HasAxiomImplyK Modal.HilbertDB
      (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _
    (Modal.DBAxiom.implyK _ _)⟩

instance :
    HasAxiomImplyS Modal.HilbertDB
      (F := Modal.Proposition Atom) where
  implyS := ⟨Modal.DerivationTree.ax [] _
    (Modal.DBAxiom.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Modal.HilbertDB
      (F := Modal.Proposition Atom) where
  efq := ⟨Modal.DerivationTree.ax [] _
    (Modal.DBAxiom.efq _)⟩

instance :
    HasAxiomPeirce Modal.HilbertDB
      (F := Modal.Proposition Atom) where
  peirce := ⟨Modal.DerivationTree.ax [] _
    (Modal.DBAxiom.peirce _ _)⟩

instance :
    HasAxiomK Modal.HilbertDB
      (F := Modal.Proposition Atom) where
  K := ⟨Modal.DerivationTree.ax [] _
    (Modal.DBAxiom.modalK _ _)⟩

instance :
    HasAxiomD Modal.HilbertDB
      (F := Modal.Proposition Atom) where
  D := ⟨Modal.DerivationTree.ax [] _
    (Modal.DBAxiom.modalD _)⟩

instance :
    HasAxiomB Modal.HilbertDB
      (F := Modal.Proposition Atom) where
  B := ⟨Modal.DerivationTree.ax [] _
    (Modal.DBAxiom.modalB _)⟩

instance :
    ModalHilbert Modal.HilbertDB
      (F := Modal.Proposition Atom) where

instance :
    ModalDHilbert Modal.HilbertDB
      (F := Modal.Proposition Atom) where

instance :
    ModalDBHilbert Modal.HilbertDB
      (F := Modal.Proposition Atom) where

end ModalInstances
