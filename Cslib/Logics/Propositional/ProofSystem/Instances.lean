/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.ProofSystem.Derivation
public import Cslib.Foundations.Logic.ProofSystem

/-! # Instance Registration for Propositional.HilbertCl

This module registers `InferenceSystem`, `ModusPonens`, all `HasAxiom*`,
and `ClassicalHilbert` instances for the `Propositional.HilbertCl` tag type,
connecting the abstract typeclass hierarchy to the concrete derivation tree.

## Architecture

The `InferenceSystem` instance maps `HilbertCl⇓φ` to `DerivationTree [] φ`.
This makes `InferenceSystem.DerivableIn HilbertCl φ = Nonempty (DerivationTree [] φ)`.

Since `PropositionalConnectives (PL.Proposition Atom)` maps `bot := .bot` and
`imp := .imp`, the generic axiom formulas (`Axioms.ImplyK`, etc.) are definitionally
equal to the concrete formulas used in `PropositionalAxiom`.

## References

* Cslib/Logics/Bimodal/ProofSystem/Instances.lean -- bimodal instance pattern
* Cslib/Foundations/Logic/ProofSystem.lean -- typeclass hierarchy
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type*} [DecidableEq Atom]

namespace Cslib.Logic.PL

section PropositionalInstances

/-! ## InferenceSystem Instance -/

instance : InferenceSystem Propositional.HilbertCl
    (PL.Proposition Atom) where
  derivation φ := PL.DerivationTree PropositionalAxiom
    ([] : List (PL.Proposition Atom)) φ

/-! ## ModusPonens Instance -/

instance :
    ModusPonens Propositional.HilbertCl
      (F := PL.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨PL.DerivationTree.modus_ponens [] _ _ d1 d2⟩

/-! ## Propositional Axiom Instances -/

instance :
    HasAxiomImplyK Propositional.HilbertCl
      (F := PL.Proposition Atom) where
  implyK := ⟨PL.DerivationTree.ax [] _ (.implyK _ _)⟩

instance :
    HasAxiomImplyS Propositional.HilbertCl
      (F := PL.Proposition Atom) where
  implyS := ⟨PL.DerivationTree.ax [] _ (.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Propositional.HilbertCl
      (F := PL.Proposition Atom) where
  efq := ⟨PL.DerivationTree.ax [] _ (.efq _)⟩

instance :
    HasAxiomPeirce Propositional.HilbertCl
      (F := PL.Proposition Atom) where
  peirce := ⟨PL.DerivationTree.ax [] _ (.peirce _ _)⟩

/-! ## ClassicalHilbert Instance -/

instance :
    ClassicalHilbert Propositional.HilbertCl
      (F := PL.Proposition Atom) where

end PropositionalInstances

end Cslib.Logic.PL
