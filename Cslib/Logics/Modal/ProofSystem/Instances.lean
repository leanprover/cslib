/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Modal.ProofSystem.Instances.K
public import Cslib.Logics.Modal.ProofSystem.Instances.T
public import Cslib.Logics.Modal.ProofSystem.Instances.D
public import Cslib.Logics.Modal.ProofSystem.Instances.B
public import Cslib.Logics.Modal.ProofSystem.Instances.K4
public import Cslib.Logics.Modal.ProofSystem.Instances.K5
public import Cslib.Logics.Modal.ProofSystem.Instances.K45
public import Cslib.Logics.Modal.ProofSystem.Instances.S4
public import Cslib.Logics.Modal.ProofSystem.Instances.S5
public import Cslib.Logics.Modal.ProofSystem.Instances.TB
public import Cslib.Logics.Modal.ProofSystem.Instances.KB5
public import Cslib.Logics.Modal.ProofSystem.Instances.D4
public import Cslib.Logics.Modal.ProofSystem.Instances.D5
public import Cslib.Logics.Modal.ProofSystem.Instances.D45
public import Cslib.Logics.Modal.ProofSystem.Instances.DB

/-! # Instance Registration for Modal Proof Systems (K, T, D, S4, S5)

This module registers `InferenceSystem`, inference rule, axiom, and bundled class
instances for the fifteen standard normal modal logics, connecting the abstract typeclass
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
| KB | `Modal.HilbertB` | `BAxiom` | `ModalBHilbert` |
| K4 | `Modal.HilbertK4` | `K4Axiom` | `ModalK4Hilbert` |
| K5 | `Modal.HilbertK5` | `K5Axiom` | `ModalK5Hilbert` |
| K45 | `Modal.HilbertK45` | `K45Axiom` | `ModalK45Hilbert` |
| S4 | `Modal.HilbertS4` | `S4Axiom` | `ModalS4Hilbert` |
| S5 | `Modal.HilbertS5` | `ModalAxiom` | `ModalS5Hilbert` |
| TB | `Modal.HilbertTB` | `TBAxiom` | `ModalTBHilbert` |
| KB5 | `Modal.HilbertKB5` | `KB5Axiom` | `ModalKB5Hilbert` |
| D4 | `Modal.HilbertD4` | `D4Axiom` | `ModalD4Hilbert` |
| D5 | `Modal.HilbertD5` | `D5Axiom` | `ModalD5Hilbert` |
| D45 | `Modal.HilbertD45` | `D45Axiom` | `ModalD45Hilbert` |
| DB | `Modal.HilbertDB` | `DBAxiom` | `ModalDBHilbert` |
-/
