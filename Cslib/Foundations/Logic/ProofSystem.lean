/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.InferenceSystem
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

Three-level propositional hierarchy:
- `MinimalHilbert` (K, S, MP) -- minimal logic
- `IntuitionisticHilbert` (+ EFQ) -- intuitionistic logic
- `ClassicalHilbert` (+ Peirce) -- classical logic

Extensions: `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`,
`BimodalTMHilbert` all extend `ClassicalHilbert`.

### Layer 4: Tag Types

Opaque tag types (`Propositional.HilbertCl`, `Propositional.HilbertMin`,
`Propositional.HilbertInt`, `Modal.HilbertK`, etc.) serve as proof system
identifiers. Concrete `InferenceSystem` and `HasAxiom*` instances will be
registered when derivation trees are defined.

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

/-- The proof system has temporal necessitation: from `S ⊢ φ`, derive `S ⊢ G(φ)`
    and `S ⊢ H(φ)`.
    G(φ) = ¬F(¬φ) = (⊤ U (φ → ⊥)) → ⊥
    H(φ) = ¬P(¬φ) = (⊤ S (φ → ⊥)) → ⊥ -/
class TemporalNecessitation (S : Type*) [HasBot F] [HasImp F]
    [HasUntil F] [HasSince F] [InferenceSystem S F] where
  /-- Temporal necessitation (G-necessitation): from `S ⊢ φ`, derive `S ⊢ G(φ)`. -/
  tempNec {φ : F} :
    InferenceSystem.DerivableIn S φ →
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasUntil.untl (HasImp.imp φ HasBot.bot)
          (HasImp.imp (HasBot.bot : F) HasBot.bot))
        HasBot.bot)
  /-- Past temporal necessitation (H-necessitation): from `S ⊢ φ`, derive `S ⊢ H(φ)`. -/
  tempNecPast {φ : F} :
    InferenceSystem.DerivableIn S φ →
    InferenceSystem.DerivableIn S
      (HasImp.imp
        (HasSince.snce (HasImp.imp φ HasBot.bot)
          (HasImp.imp (HasBot.bot : F) HasBot.bot))
        HasBot.bot)

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

/-! ### Temporal Axiom Typeclasses -/

section TemporalAxiomClasses

variable (S : Type*) [HasBot F] [HasImp F] [HasUntil F] [HasSince F]
  [InferenceSystem S F]

/-- The proof system proves serial future (BX1): ⊤ → F ⊤. -/
class HasAxiomSerialFuture where
  serialFuture : InferenceSystem.DerivableIn S (Axioms.SerialFuture (F := F))

/-- The proof system proves serial past (BX1'): ⊤ → P ⊤. -/
class HasAxiomSerialPast where
  serialPast : InferenceSystem.DerivableIn S (Axioms.SerialPast (F := F))

/-- The proof system proves guard monotonicity of Until under G (BX2G). -/
class HasAxiomLeftMonoUntilG where
  leftMonoUntilG {φ ψ χ : F} :
    InferenceSystem.DerivableIn S (Axioms.LeftMonoUntilG φ ψ χ)

/-- The proof system proves guard monotonicity of Since under H (BX2H). -/
class HasAxiomLeftMonoSinceH where
  leftMonoSinceH {φ ψ χ : F} :
    InferenceSystem.DerivableIn S (Axioms.LeftMonoSinceH φ ψ χ)

/-- The proof system proves event monotonicity of Until (BX3). -/
class HasAxiomRightMonoUntil where
  rightMonoUntil {φ ψ χ : F} :
    InferenceSystem.DerivableIn S (Axioms.RightMonoUntil φ ψ χ)

/-- The proof system proves event monotonicity of Since (BX3'). -/
class HasAxiomRightMonoSince where
  rightMonoSince {φ ψ χ : F} :
    InferenceSystem.DerivableIn S (Axioms.RightMonoSince φ ψ χ)

/-- The proof system proves temporal connectedness future (BX4). -/
class HasAxiomConnectFuture where
  connectFuture {φ : F} :
    InferenceSystem.DerivableIn S (Axioms.ConnectFuture φ)

/-- The proof system proves temporal connectedness past (BX4'). -/
class HasAxiomConnectPast where
  connectPast {φ : F} :
    InferenceSystem.DerivableIn S (Axioms.ConnectPast φ)

/-- The proof system proves Until-Since enrichment (BX13). -/
class HasAxiomEnrichmentUntil where
  enrichmentUntil {φ ψ p : F} :
    InferenceSystem.DerivableIn S (Axioms.EnrichmentUntil φ ψ p)

/-- The proof system proves Since-Until enrichment (BX13'). -/
class HasAxiomEnrichmentSince where
  enrichmentSince {φ ψ p : F} :
    InferenceSystem.DerivableIn S (Axioms.EnrichmentSince φ ψ p)

/-- The proof system proves self-accumulation of Until (BX5). -/
class HasAxiomSelfAccumUntil where
  selfAccumUntil {φ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.SelfAccumUntil φ ψ)

/-- The proof system proves self-accumulation of Since (BX5'). -/
class HasAxiomSelfAccumSince where
  selfAccumSince {φ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.SelfAccumSince φ ψ)

/-- The proof system proves absorption of Until (BX6). -/
class HasAxiomAbsorbUntil where
  absorbUntil {φ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.AbsorbUntil φ ψ)

/-- The proof system proves absorption of Since (BX6'). -/
class HasAxiomAbsorbSince where
  absorbSince {φ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.AbsorbSince φ ψ)

/-- The proof system proves linearity of Until (BX7). -/
class HasAxiomLinearUntil where
  linearUntil {φ ψ χ θ : F} :
    InferenceSystem.DerivableIn S (Axioms.LinearUntil φ ψ χ θ)

/-- The proof system proves linearity of Since (BX7'). -/
class HasAxiomLinearSince where
  linearSince {φ ψ χ θ : F} :
    InferenceSystem.DerivableIn S (Axioms.LinearSince φ ψ χ θ)

/-- The proof system proves Until implies eventuality (BX10). -/
class HasAxiomUntilF where
  untilF {φ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.UntilF φ ψ)

/-- The proof system proves Since implies past eventuality (BX10'). -/
class HasAxiomSinceP where
  sinceP {φ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.SinceP φ ψ)

/-- The proof system proves temporal linearity (BX11). -/
class HasAxiomTempLinearity where
  tempLinearity {φ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.TempLinearity φ ψ)

/-- The proof system proves temporal linearity past (BX11'). -/
class HasAxiomTempLinearityPast where
  tempLinearityPast {φ ψ : F} :
    InferenceSystem.DerivableIn S (Axioms.TempLinearityPast φ ψ)

/-- The proof system proves F-Until equivalence (BX12). -/
class HasAxiomFUntilEquiv where
  fUntilEquiv {φ : F} :
    InferenceSystem.DerivableIn S (Axioms.FUntilEquiv φ)

/-- The proof system proves P-Since equivalence (BX12'). -/
class HasAxiomPSinceEquiv where
  pSinceEquiv {φ : F} :
    InferenceSystem.DerivableIn S (Axioms.PSinceEquiv φ)

end TemporalAxiomClasses

/-! ### Bundled Proof System Classes -/

/-- Minimal propositional Hilbert system (K, S, MP). -/
class MinimalHilbert (S : Type*) [HasBot F] [HasImp F]
    [InferenceSystem S F]
    extends ModusPonens S (F := F),
            HasAxiomImplyK S (F := F),
            HasAxiomImplyS S (F := F)

/-- Intuitionistic propositional Hilbert system (K, S, MP, EFQ). -/
class IntuitionisticHilbert (S : Type*) [HasBot F] [HasImp F]
    [InferenceSystem S F]
    extends MinimalHilbert S (F := F),
            HasAxiomEFQ S (F := F)

/-- Classical propositional Hilbert system (K, S, MP, EFQ, Peirce). -/
class ClassicalHilbert (S : Type*) [HasBot F] [HasImp F]
    [InferenceSystem S F]
    extends IntuitionisticHilbert S (F := F),
            HasAxiomPeirce S (F := F)

/-- Modal Hilbert system K. -/
class ModalHilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ClassicalHilbert S (F := F),
            Necessitation S (F := F),
            HasAxiomK S (F := F)

/-- Modal Hilbert system T (extends K with T / reflexivity). -/
class ModalTHilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalHilbert S (F := F),
            HasAxiomT S (F := F)

/-- Modal Hilbert system D (extends K with D / seriality). -/
class ModalDHilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalHilbert S (F := F),
            HasAxiomD S (F := F)

/-- Modal Hilbert system S4 (extends T with 4 / transitivity). -/
class ModalS4Hilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalTHilbert S (F := F),
            HasAxiom4 S (F := F)

/-- Modal Hilbert system S5 (extends S4 with B / symmetry). -/
class ModalS5Hilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalS4Hilbert S (F := F),
            HasAxiomB S (F := F)

/-- Modal Hilbert system KB (extends K with B / symmetry). -/
class ModalBHilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalHilbert S (F := F),
            HasAxiomB S (F := F)

/-- Modal Hilbert system K4 (extends K with 4 / transitivity). -/
class ModalK4Hilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalHilbert S (F := F),
            HasAxiom4 S (F := F)

/-- Modal Hilbert system K5 (extends K with 5 / Euclideanness). -/
class ModalK5Hilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalHilbert S (F := F),
            HasAxiom5 S (F := F)

/-- Modal Hilbert system K45 (extends K4 with 5 / Euclideanness). -/
class ModalK45Hilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalK4Hilbert S (F := F),
            HasAxiom5 S (F := F)

/-- Modal Hilbert system TB (extends T with B / symmetry). -/
class ModalTBHilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalTHilbert S (F := F),
            HasAxiomB S (F := F)

/-- Modal Hilbert system KB5 (extends KB with 5 / Euclideanness). -/
class ModalKB5Hilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalBHilbert S (F := F),
            HasAxiom5 S (F := F)

/-- Modal Hilbert system D4 (extends D with 4 / transitivity). -/
class ModalD4Hilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalDHilbert S (F := F),
            HasAxiom4 S (F := F)

/-- Modal Hilbert system D5 (extends D with 5 / Euclideanness). -/
class ModalD5Hilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalDHilbert S (F := F),
            HasAxiom5 S (F := F)

/-- Modal Hilbert system D45 (extends D4 with 5 / Euclideanness). -/
class ModalD45Hilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalD4Hilbert S (F := F),
            HasAxiom5 S (F := F)

/-- Modal Hilbert system DB (extends D with B / symmetry). -/
class ModalDBHilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [InferenceSystem S F]
    extends ModalDHilbert S (F := F),
            HasAxiomB S (F := F)

/-- Temporal Hilbert system BX: extends classical propositional logic with
    temporal necessitation and all 22 BX temporal axiom typeclasses. -/
class TemporalBXHilbert (S : Type*) [HasBot F] [HasImp F] [HasUntil F]
    [HasSince F] [InferenceSystem S F]
    extends ClassicalHilbert S (F := F),
            TemporalNecessitation S (F := F),
            HasAxiomSerialFuture S (F := F),
            HasAxiomSerialPast S (F := F),
            HasAxiomLeftMonoUntilG S (F := F),
            HasAxiomLeftMonoSinceH S (F := F),
            HasAxiomRightMonoUntil S (F := F),
            HasAxiomRightMonoSince S (F := F),
            HasAxiomConnectFuture S (F := F),
            HasAxiomConnectPast S (F := F),
            HasAxiomEnrichmentUntil S (F := F),
            HasAxiomEnrichmentSince S (F := F),
            HasAxiomSelfAccumUntil S (F := F),
            HasAxiomSelfAccumSince S (F := F),
            HasAxiomAbsorbUntil S (F := F),
            HasAxiomAbsorbSince S (F := F),
            HasAxiomLinearUntil S (F := F),
            HasAxiomLinearSince S (F := F),
            HasAxiomUntilF S (F := F),
            HasAxiomSinceP S (F := F),
            HasAxiomTempLinearity S (F := F),
            HasAxiomTempLinearityPast S (F := F),
            HasAxiomFUntilEquiv S (F := F),
            HasAxiomPSinceEquiv S (F := F)

/-- Bimodal Hilbert system TM: extends S5 modal logic and BX temporal logic
    with the modal-future interaction axiom. -/
class BimodalTMHilbert (S : Type*) [HasBot F] [HasImp F] [HasBox F]
    [HasUntil F] [HasSince F] [InferenceSystem S F]
    extends ModalS5Hilbert S (F := F),
            TemporalBXHilbert S (F := F),
            HasAxiomMF S (F := F)

/-! ### Tag Types -/

/-- Tag type for minimal propositional Hilbert system. -/
opaque Propositional.HilbertMin : Type := Empty

/-- Tag type for intuitionistic propositional Hilbert system. -/
opaque Propositional.HilbertInt : Type := Empty

/-- Tag type for classical propositional Hilbert system. -/
opaque Propositional.HilbertCl : Type := Empty

/-- Tag type for modal logic K. -/
opaque Modal.HilbertK : Type := Empty

/-- Tag type for modal logic T. -/
opaque Modal.HilbertT : Type := Empty

/-- Tag type for modal logic D. -/
opaque Modal.HilbertD : Type := Empty

/-- Tag type for modal logic S4. -/
opaque Modal.HilbertS4 : Type := Empty

/-- Tag type for modal logic S5. -/
opaque Modal.HilbertS5 : Type := Empty

/-- Tag type for modal logic KB. -/
opaque Modal.HilbertB : Type := Empty

/-- Tag type for modal logic K4. -/
opaque Modal.HilbertK4 : Type := Empty

/-- Tag type for modal logic K5. -/
opaque Modal.HilbertK5 : Type := Empty

/-- Tag type for modal logic K45. -/
opaque Modal.HilbertK45 : Type := Empty

/-- Tag type for modal logic TB. -/
opaque Modal.HilbertTB : Type := Empty

/-- Tag type for modal logic KB5. -/
opaque Modal.HilbertKB5 : Type := Empty

/-- Tag type for modal logic D4. -/
opaque Modal.HilbertD4 : Type := Empty

/-- Tag type for modal logic D5. -/
opaque Modal.HilbertD5 : Type := Empty

/-- Tag type for modal logic D45. -/
opaque Modal.HilbertD45 : Type := Empty

/-- Tag type for modal logic DB. -/
opaque Modal.HilbertDB : Type := Empty

/-- Tag type for temporal logic BX. -/
opaque Temporal.HilbertBX : Type := Empty

/-- Tag type for bimodal logic TM. -/
opaque Bimodal.HilbertTM : Type := Empty

end Cslib.Logic
