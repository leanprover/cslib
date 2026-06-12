/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Foundations.Logic.ProofSystem

/-! # Instance Registration for Modal Logic S5

Registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the modal logic S5. Reuses the existing `ModalAxiom` type.
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type u}

/-! ## Instance Registrations -/

section ModalInstances

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
