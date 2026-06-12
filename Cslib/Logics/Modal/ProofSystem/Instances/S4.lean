/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.ProofSystem

/-! # Instance Registration for Modal Logic S4

Registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the modal logic S4.
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Axiom Predicate -/

namespace Cslib.Logic.Modal

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

end ModalInstances
