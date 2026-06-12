/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.ProofSystem

/-! # Instance Registration for Modal Logic TB

Registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the modal logic TB.
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Axiom Predicate -/

namespace Cslib.Logic.Modal

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

end Cslib.Logic.Modal

/-! ## Instance Registrations -/

section ModalInstances

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

end ModalInstances
