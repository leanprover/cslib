/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.ProofSystem.Derivation
public import Cslib.Foundations.Logic.ProofSystem

/-! # Instance Registration for Propositional.HilbertInt and Propositional.HilbertMin

This module registers `InferenceSystem`, `ModusPonens`, axiom instances,
`IntuitionisticHilbert`, and `MinimalHilbert` instances for the
`Propositional.HilbertInt` and `Propositional.HilbertMin` tag types,
connecting the abstract typeclass hierarchy to the concrete derivation trees
parameterized over `IntPropAxiom` and `MinPropAxiom` respectively.

## Architecture

- `HilbertInt` instances use `DerivationTree IntPropAxiom [] phi`.
- `HilbertMin` instances use `DerivationTree MinPropAxiom [] phi`.

## References

* Cslib/Logics/Propositional/ProofSystem/Instances.lean -- classical instance pattern
* Cslib/Foundations/Logic/ProofSystem.lean -- typeclass hierarchy
-/

@[expose] public section

open Cslib.Logic

variable {Atom : Type*} [DecidableEq Atom]

namespace Cslib.Logic.PL

/-! ## HilbertInt Instances -/

section IntuitionisticInstances

instance : InferenceSystem Propositional.HilbertInt
    (PL.Proposition Atom) where
  derivation φ := PL.DerivationTree IntPropAxiom
    ([] : List (PL.Proposition Atom)) φ

instance :
    ModusPonens Propositional.HilbertInt
      (F := PL.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨PL.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    HasAxiomImplyK Propositional.HilbertInt
      (F := PL.Proposition Atom) where
  implyK := ⟨PL.DerivationTree.ax [] _ (.implyK _ _)⟩

instance :
    HasAxiomImplyS Propositional.HilbertInt
      (F := PL.Proposition Atom) where
  implyS := ⟨PL.DerivationTree.ax [] _ (.implyS _ _ _)⟩

instance :
    HasAxiomEFQ Propositional.HilbertInt
      (F := PL.Proposition Atom) where
  efq := ⟨PL.DerivationTree.ax [] _ (.efq _)⟩

instance :
    IntuitionisticHilbert Propositional.HilbertInt
      (F := PL.Proposition Atom) where

end IntuitionisticInstances

/-! ## HilbertMin Instances -/

section MinimalInstances

instance : InferenceSystem Propositional.HilbertMin
    (PL.Proposition Atom) where
  derivation φ := PL.DerivationTree MinPropAxiom
    ([] : List (PL.Proposition Atom)) φ

instance :
    ModusPonens Propositional.HilbertMin
      (F := PL.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨PL.DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance :
    HasAxiomImplyK Propositional.HilbertMin
      (F := PL.Proposition Atom) where
  implyK := ⟨PL.DerivationTree.ax [] _ (.implyK _ _)⟩

instance :
    HasAxiomImplyS Propositional.HilbertMin
      (F := PL.Proposition Atom) where
  implyS := ⟨PL.DerivationTree.ax [] _ (.implyS _ _ _)⟩

instance :
    MinimalHilbert Propositional.HilbertMin
      (F := PL.Proposition Atom) where

end MinimalInstances

end Cslib.Logic.PL
