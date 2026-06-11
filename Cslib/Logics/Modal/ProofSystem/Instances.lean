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

end ModalInstances
