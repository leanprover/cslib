/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.ProofSystem

/-! # Instance Registration for Modal Logic KB

Registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the modal logic KB.
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Axiom Predicate -/

namespace Cslib.Logic.Modal

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

end Cslib.Logic.Modal

/-! ## Instance Registrations -/

section ModalInstances

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

end ModalInstances
