/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives

/-! # Polymorphic Axiom Definitions

This module defines axiom formulas as polymorphic `abbrev`s parameterized over the connective
typeclasses. Each axiom is defined once and can be instantiated at any formula type with the
appropriate connectives.

## Organization

- **Propositional axioms**: `ImplyK`, `ImplyS`, `EFQ`, `Peirce`
  (require `HasBot`, `HasImp`)
- **Modal axioms**: `AxiomK`, `AxiomT`, `Axiom4`, `AxiomB`, `Axiom5`, `AxiomD`
  (require additionally `HasBox`)
- **Temporal axioms**: `SerialFuture`, `ConnectFuture`, etc.
  (require `HasUntil`, `HasSince`)
- **Interaction axiom**: `ModalFuture`
  (requires both `HasBox` and `HasUntil`)
-/

@[expose] public section

namespace Cslib.Logic.Axioms

variable {F : Type*}

/-! ### Propositional Axioms -/

section Propositional
variable [HasBot F] [HasImp F]

/-- K axiom for implication: φ → (ψ → φ) -/
protected abbrev ImplyK (φ ψ : F) : F :=
  HasImp.imp φ (HasImp.imp ψ φ)

/-- S axiom for implication: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)) -/
protected abbrev ImplyS (φ ψ χ : F) : F :=
  HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
    (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp φ χ))

/-- Ex falso quodlibet: ⊥ → φ -/
protected abbrev EFQ (φ : F) : F :=
  HasImp.imp HasBot.bot φ

/-- Peirce's law (classical): ((φ → ψ) → φ) → φ -/
protected abbrev Peirce (φ ψ : F) : F :=
  HasImp.imp (HasImp.imp (HasImp.imp φ ψ) φ) φ

/-- Double negation elimination: ¬¬φ → φ
    where ¬φ = φ → ⊥ -/
protected abbrev DNE (φ : F) : F :=
  HasImp.imp (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot) φ

end Propositional

/-! ### Modal Axioms -/

section Modal
variable [HasBot F] [HasImp F] [HasBox F]

/-- Distribution axiom K: □(φ → ψ) → (□φ → □ψ) -/
protected abbrev AxiomK (φ ψ : F) : F :=
  HasImp.imp (HasBox.box (HasImp.imp φ ψ))
    (HasImp.imp (HasBox.box φ) (HasBox.box ψ))

/-- Reflexivity axiom T: □φ → φ -/
protected abbrev AxiomT (φ : F) : F :=
  HasImp.imp (HasBox.box φ) φ

/-- Transitivity axiom 4: □φ → □□φ -/
protected abbrev Axiom4 (φ : F) : F :=
  HasImp.imp (HasBox.box φ) (HasBox.box (HasBox.box φ))

/-- Symmetry axiom B: φ → □◇φ
    where ◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥ -/
protected abbrev AxiomB (φ : F) : F :=
  HasImp.imp φ (HasBox.box
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot))

/-- Euclidean axiom 5: ◇φ → □◇φ
    where ◇φ = (□(φ → ⊥)) → ⊥ -/
protected abbrev Axiom5 (φ : F) : F :=
  HasImp.imp
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)
    (HasBox.box (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot))

/-- Seriality axiom D: □φ → ◇φ
    where ◇φ = (□(φ → ⊥)) → ⊥ -/
protected abbrev AxiomD (φ : F) : F :=
  HasImp.imp (HasBox.box φ)
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)

end Modal

/-! ### Temporal Axioms -/

section Temporal
variable [HasBot F] [HasImp F] [HasUntil F] [HasSince F]

/-- Serial future: ⊤ → F ⊤
    where ⊤ = ⊥ → ⊥, F φ = ⊤ U φ -/
protected abbrev SerialFuture : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  HasImp.imp top (HasUntil.untl top top)

/-- Serial past: ⊤ → P ⊤
    where P φ = ⊤ S φ -/
protected abbrev SerialPast : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  HasImp.imp top (HasSince.snce top top)

end Temporal

/-! ### Interaction Axioms -/

section Interaction
variable [HasBot F] [HasImp F] [HasBox F] [HasUntil F]

/-- Modal-future interaction axiom MF: □F φ → F □φ
    where F φ = ⊤ U φ -/
protected abbrev ModalFuture (φ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  HasImp.imp
    (HasBox.box (HasUntil.untl top φ))
    (HasUntil.untl top (HasBox.box φ))

end Interaction

end Cslib.Logic.Axioms
