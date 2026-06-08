/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Foundations.Logic.Connectives
public import Cslib.Foundations.Logic.Axioms

/-! # Proof System Typeclasses

This module defines the typeclass hierarchy for Hilbert-style proof systems.
Each axiom gets a `HasAxiom*` typeclass, and bundled proof system classes
compose these via `extends`.

## Architecture

### Layer 1: Individual Axiom Typeclasses

Each `HasAxiom*` typeclass states that a particular proof system tag `S`
proves the corresponding axiom for all formula instantiations.

### Layer 2: Inference Rule Typeclasses

`ModusPonens`, `Necessitation` state that the proof system is closed
under the corresponding rule.

### Layer 3: Bundled Proof System Classes

`PropositionalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, etc. compose
the individual axiom and rule typeclasses via `extends`.

### Layer 4: Tag Types

Opaque tag types (`Propositional.HilbertCl`, `Modal.HilbertK`, etc.)
serve as proof system identifiers. Concrete `InferenceSystem` and
`HasAxiom*` instances will be registered when derivation trees are defined.

## Note

This module defines the **interface** only. Concrete instances require
derivation trees (not yet ported) and are future work.
-/

@[expose] public section

namespace Cslib.Logic

variable {F : Type*}

/-! ### Inference Rule Typeclasses -/

/-- A proof system has modus ponens: from `S ⊢ φ → ψ` and `S ⊢ φ`,
    derive `S ⊢ ψ`. -/
class ModusPonens (S : Type*) [HasImp F] [InferenceSystem S F] where
  /-- Modus ponens rule. -/
  mp {φ ψ : F} : InferenceSystem.DerivableIn S (HasImp.imp φ ψ) →
    InferenceSystem.DerivableIn S φ → InferenceSystem.DerivableIn S ψ

/-- A proof system has necessitation: from `S ⊢ φ`, derive `S ⊢ □φ`. -/
class Necessitation (S : Type*) [HasBox F] [InferenceSystem S F] where
  /-- Necessitation rule. -/
  nec {φ : F} :
    InferenceSystem.DerivableIn S φ →
    InferenceSystem.DerivableIn S (HasBox.box φ)

/-- Marker class: the proof system has temporal necessitation. -/
class TemporalNecessitation (S : Type*) [HasUntil F] [HasSince F]
    [InferenceSystem S F]

/-! ### Individual Axiom Typeclasses -/

section AxiomClasses

variable (S : Type*) [HasBot F] [HasImp F] [InferenceSystem S F]

/-- The proof system proves ImplyK: φ → (ψ → φ). -/
class HasAxiomImplyK where
  implyK {φ ψ : F} : InferenceSystem.DerivableIn S (Axioms.ImplyK φ ψ)

/-- The proof system proves ImplyS. -/
class HasAxiomImplyS where
  implyS {φ ψ χ : F} :
    InferenceSystem.DerivableIn S (Axioms.ImplyS φ ψ χ)

/-- The proof system proves EFQ: ⊥ → φ. -/
class HasAxiomEFQ where
  efq {φ : F} : InferenceSystem.DerivableIn S (Axioms.EFQ φ)

/-- The proof system proves Peirce's law. -/
class HasAxiomPeirce where
  peirce {φ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.Peirce φ ψ)

/-- The proof system proves DNE: ¬¬φ → φ. -/
class HasAxiomDNE where
  dne {φ : F} : InferenceSystem.DerivableIn S (Axioms.DNE φ)

variable [HasBox F]

/-- The proof system proves axiom K: □(φ → ψ) → (□φ → □ψ). -/
class HasAxiomK where
  K {φ ψ : F} : InferenceSystem.DerivableIn S (Axioms.AxiomK φ ψ)

/-- The proof system proves axiom T: □φ → φ. -/
class HasAxiomT where
  T {φ : F} : InferenceSystem.DerivableIn S (Axioms.AxiomT φ)

/-- The proof system proves axiom 4: □φ → □□φ. -/
class HasAxiom4 where
  four {φ : F} : InferenceSystem.DerivableIn S (Axioms.Axiom4 φ)

/-- The proof system proves axiom B: φ → □◇φ. -/
class HasAxiomB where
  B {φ : F} : InferenceSystem.DerivableIn S (Axioms.AxiomB φ)

/-- The proof system proves axiom 5: ◇φ → □◇φ. -/
class HasAxiom5 where
  five {φ : F} : InferenceSystem.DerivableIn S (Axioms.Axiom5 φ)

/-- The proof system proves axiom D: □φ → ◇φ. -/
class HasAxiomD where
  D {φ : F} : InferenceSystem.DerivableIn S (Axioms.AxiomD φ)

variable [HasUntil F]

/-- The proof system proves the modal-future interaction axiom. -/
class HasAxiomMF where
  MF {φ : F} :
    InferenceSystem.DerivableIn S (Axioms.ModalFuture φ)

end AxiomClasses

/-! ### Bundled Proof System Classes -/

/-- Classical propositional Hilbert system. -/
class PropositionalHilbert (S : Type*) [HasBot F] [HasImp F]
    [InferenceSystem S F]
    extends ModusPonens S (F := F),
            HasAxiomImplyK S (F := F),
            HasAxiomImplyS S (F := F),
            HasAxiomEFQ S (F := F),
            HasAxiomPeirce S (F := F)

/-- Modal Hilbert system K. -/
class ModalHilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends PropositionalHilbert S (F := F),
            Necessitation S (F := F),
            HasAxiomK S (F := F)

/-- Modal Hilbert system S5 (extends K with T, 4, B). -/
class ModalS5Hilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalHilbert S (F := F),
            HasAxiomT S (F := F),
            HasAxiom4 S (F := F),
            HasAxiomB S (F := F)

/-- Temporal Hilbert system BX. -/
class TemporalBXHilbert (S : Type*) [HasBot F] [HasImp F] [HasUntil F]
    [HasSince F] [InferenceSystem S F]
    extends PropositionalHilbert S (F := F),
            TemporalNecessitation S (F := F)

/-- Bimodal Hilbert system TM. -/
class BimodalTMHilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [HasUntil F] [HasSince F] [InferenceSystem S F]
    extends ModalS5Hilbert S (F := F),
            TemporalNecessitation S (F := F),
            HasAxiomMF S (F := F)

/-! ### Tag Types -/

/-- Tag type for classical propositional Hilbert system. -/
opaque Propositional.HilbertCl : Type := Empty

/-- Tag type for modal logic K. -/
opaque Modal.HilbertK : Type := Empty

/-- Tag type for modal logic S5. -/
opaque Modal.HilbertS5 : Type := Empty

/-- Tag type for temporal logic BX. -/
opaque Temporal.HilbertBX : Type := Empty

/-- Tag type for bimodal logic TM. -/
opaque Bimodal.HilbertTM : Type := Empty

end Cslib.Logic
