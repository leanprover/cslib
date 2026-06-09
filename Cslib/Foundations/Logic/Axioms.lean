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

/-- Serial future (BX1): ⊤ → F ⊤
    where ⊤ = ⊥ → ⊥, F φ = ⊤ U φ -/
protected abbrev SerialFuture : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  HasImp.imp top (HasUntil.untl top top)

/-- Serial past (BX1'): ⊤ → P ⊤
    where P φ = ⊤ S φ -/
protected abbrev SerialPast : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  HasImp.imp top (HasSince.snce top top)

/-- Guard monotonicity of Until under G (BX2G):
    G(φ → χ) → (ψ U φ → ψ U χ)
    where G(α) = ¬(⊤ U ¬α) -/
protected abbrev LeftMonoUntilG (φ χ ψ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let G_imp := HasImp.imp (HasUntil.untl (neg (HasImp.imp φ χ)) top) HasBot.bot
  HasImp.imp G_imp
    (HasImp.imp (HasUntil.untl ψ φ) (HasUntil.untl ψ χ))

/-- Guard monotonicity of Since under H (BX2H):
    H(φ → χ) → (ψ S φ → ψ S χ)
    where H(α) = ¬(⊤ S ¬α) -/
protected abbrev LeftMonoSinceH (φ χ ψ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let H_imp := HasImp.imp (HasSince.snce (neg (HasImp.imp φ χ)) top) HasBot.bot
  HasImp.imp H_imp
    (HasImp.imp (HasSince.snce ψ φ) (HasSince.snce ψ χ))

/-- Event monotonicity of Until (BX3):
    G(φ → ψ) → (φ U χ → ψ U χ)
    where G(α) = ¬(⊤ U ¬α) -/
protected abbrev RightMonoUntil (φ ψ χ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let G_imp := HasImp.imp (HasUntil.untl (neg (HasImp.imp φ ψ)) top) HasBot.bot
  HasImp.imp G_imp
    (HasImp.imp (HasUntil.untl φ χ) (HasUntil.untl ψ χ))

/-- Event monotonicity of Since (BX3'):
    H(φ → ψ) → (φ S χ → ψ S χ)
    where H(α) = ¬(⊤ S ¬α) -/
protected abbrev RightMonoSince (φ ψ χ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let H_imp := HasImp.imp (HasSince.snce (neg (HasImp.imp φ ψ)) top) HasBot.bot
  HasImp.imp H_imp
    (HasImp.imp (HasSince.snce φ χ) (HasSince.snce ψ χ))

/-- Temporal connectedness future (BX4): φ → G(P(φ))
    where P(α) = ⊤ S α, G(α) = ¬(⊤ U ¬α) -/
protected abbrev ConnectFuture (φ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let P_φ := HasSince.snce φ top
  let G_P_φ := HasImp.imp (HasUntil.untl (neg P_φ) top) HasBot.bot
  HasImp.imp φ G_P_φ

/-- Temporal connectedness past (BX4'): φ → H(F(φ))
    where F(α) = ⊤ U α, H(α) = ¬(⊤ S ¬α) -/
protected abbrev ConnectPast (φ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let F_φ := HasUntil.untl φ top
  let H_F_φ := HasImp.imp (HasSince.snce (neg F_φ) top) HasBot.bot
  HasImp.imp φ H_F_φ

/-- Until-Since enrichment (BX13):
    p ∧ (ψ U φ) → (ψ ∧ S(p, φ)) U φ
    where ∧ is Lukasiewicz conjunction -/
protected abbrev EnrichmentUntil (φ ψ p : F) : F :=
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let conj := fun (a b : F) => HasImp.imp (HasImp.imp a (neg b)) HasBot.bot
  HasImp.imp (conj p (HasUntil.untl ψ φ))
    (HasUntil.untl (conj ψ (HasSince.snce p φ)) φ)

/-- Since-Until enrichment (BX13'):
    p ∧ (ψ S φ) → (ψ ∧ U(p, φ)) S φ -/
protected abbrev EnrichmentSince (φ ψ p : F) : F :=
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let conj := fun (a b : F) => HasImp.imp (HasImp.imp a (neg b)) HasBot.bot
  HasImp.imp (conj p (HasSince.snce ψ φ))
    (HasSince.snce (conj ψ (HasUntil.untl p φ)) φ)

/-- Self-accumulation of Until (BX5):
    U(ψ, φ) → U(ψ, φ ∧ U(ψ, φ)) -/
protected abbrev SelfAccumUntil (φ ψ : F) : F :=
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let conj := fun (a b : F) => HasImp.imp (HasImp.imp a (neg b)) HasBot.bot
  HasImp.imp (HasUntil.untl ψ φ)
    (HasUntil.untl ψ (conj φ (HasUntil.untl ψ φ)))

/-- Self-accumulation of Since (BX5'):
    S(ψ, φ) → S(ψ, φ ∧ S(ψ, φ)) -/
protected abbrev SelfAccumSince (φ ψ : F) : F :=
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let conj := fun (a b : F) => HasImp.imp (HasImp.imp a (neg b)) HasBot.bot
  HasImp.imp (HasSince.snce ψ φ)
    (HasSince.snce ψ (conj φ (HasSince.snce ψ φ)))

/-- Absorption of Until (BX6):
    U(φ ∧ U(ψ, φ), φ) → U(ψ, φ) -/
protected abbrev AbsorbUntil (φ ψ : F) : F :=
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let conj := fun (a b : F) => HasImp.imp (HasImp.imp a (neg b)) HasBot.bot
  HasImp.imp (HasUntil.untl (conj φ (HasUntil.untl ψ φ)) φ)
    (HasUntil.untl ψ φ)

/-- Absorption of Since (BX6'):
    S(φ ∧ S(ψ, φ), φ) → S(ψ, φ) -/
protected abbrev AbsorbSince (φ ψ : F) : F :=
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let conj := fun (a b : F) => HasImp.imp (HasImp.imp a (neg b)) HasBot.bot
  HasImp.imp (HasSince.snce (conj φ (HasSince.snce ψ φ)) φ)
    (HasSince.snce ψ φ)

/-- Linearity of Until (BX7):
    U(ψ,φ) ∧ U(θ,χ) → U(ψ∧θ, φ∧χ) ∨ U(ψ∧χ, φ∧χ) ∨ U(φ∧θ, φ∧χ) -/
protected abbrev LinearUntil (φ ψ χ θ : F) : F :=
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let conj := fun (a b : F) => HasImp.imp (HasImp.imp a (neg b)) HasBot.bot
  let disj := fun (a b : F) => HasImp.imp (neg a) b
  HasImp.imp (conj (HasUntil.untl ψ φ) (HasUntil.untl θ χ))
    (disj (disj (HasUntil.untl (conj ψ θ) (conj φ χ))
                (HasUntil.untl (conj ψ χ) (conj φ χ)))
          (HasUntil.untl (conj φ θ) (conj φ χ)))

/-- Linearity of Since (BX7'):
    S(ψ,φ) ∧ S(θ,χ) → S(ψ∧θ, φ∧χ) ∨ S(ψ∧χ, φ∧χ) ∨ S(φ∧θ, φ∧χ) -/
protected abbrev LinearSince (φ ψ χ θ : F) : F :=
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let conj := fun (a b : F) => HasImp.imp (HasImp.imp a (neg b)) HasBot.bot
  let disj := fun (a b : F) => HasImp.imp (neg a) b
  HasImp.imp (conj (HasSince.snce ψ φ) (HasSince.snce θ χ))
    (disj (disj (HasSince.snce (conj ψ θ) (conj φ χ))
                (HasSince.snce (conj ψ χ) (conj φ χ)))
          (HasSince.snce (conj φ θ) (conj φ χ)))

/-- Until implies eventuality (BX10):
    U(ψ, φ) → F(ψ)
    where F(α) = ⊤ U α -/
protected abbrev UntilF (φ ψ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  HasImp.imp (HasUntil.untl ψ φ) (HasUntil.untl ψ top)

/-- Since implies past eventuality (BX10'):
    S(ψ, φ) → P(ψ)
    where P(α) = α S ⊤ -/
protected abbrev SinceP (φ ψ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  HasImp.imp (HasSince.snce ψ φ) (HasSince.snce ψ top)

/-- Temporal linearity (BX11):
    F(φ) ∧ F(ψ) → F(φ ∧ ψ) ∨ F(φ ∧ F(ψ)) ∨ F(F(φ) ∧ ψ) -/
protected abbrev TempLinearity (φ ψ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let conj := fun (a b : F) => HasImp.imp (HasImp.imp a (neg b)) HasBot.bot
  let disj := fun (a b : F) => HasImp.imp (neg a) b
  let F' := fun (x : F) => HasUntil.untl x top
  HasImp.imp (conj (F' φ) (F' ψ))
    (disj (F' (conj φ ψ))
      (disj (F' (conj φ (F' ψ)))
            (F' (conj (F' φ) ψ))))

/-- Temporal linearity past (BX11'):
    P(φ) ∧ P(ψ) → P(φ ∧ ψ) ∨ P(φ ∧ P(ψ)) ∨ P(P(φ) ∧ ψ) -/
protected abbrev TempLinearityPast (φ ψ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  let neg := fun (x : F) => HasImp.imp x HasBot.bot
  let conj := fun (a b : F) => HasImp.imp (HasImp.imp a (neg b)) HasBot.bot
  let disj := fun (a b : F) => HasImp.imp (neg a) b
  let P' := fun (x : F) => HasSince.snce x top
  HasImp.imp (conj (P' φ) (P' ψ))
    (disj (P' (conj φ ψ))
      (disj (P' (conj φ (P' ψ)))
            (P' (conj (P' φ) ψ))))

/-- F-Until equivalence (BX12):
    F(φ) → U(φ, ⊤)
    where F(α) = ⊤ U α -/
protected abbrev FUntilEquiv (φ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  HasImp.imp (HasUntil.untl φ top) (HasUntil.untl φ top)

/-- P-Since equivalence (BX12'):
    P(φ) → S(φ, ⊤)
    Note: Under the Burgess 1982 convention, this is trivially P(φ) → P(φ). -/
protected abbrev PSinceEquiv (φ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  HasImp.imp (HasSince.snce φ top) (HasSince.snce φ top)

end Temporal

/-! ### Interaction Axioms -/

section Interaction
variable [HasBot F] [HasImp F] [HasBox F] [HasUntil F]

/-- Modal-future interaction axiom MF: □φ → □(Gφ)
    where G φ = ¬F(¬φ) = ¬(⊤ U ¬φ)
    Necessary truths remain necessary in the future. -/
protected abbrev ModalFuture (φ : F) : F :=
  let top := HasImp.imp (HasBot.bot : F) HasBot.bot
  let neg_φ := HasImp.imp φ HasBot.bot
  let G_φ := HasImp.imp (HasUntil.untl neg_φ top) HasBot.bot
  HasImp.imp (HasBox.box φ) (HasBox.box G_φ)

end Interaction

end Cslib.Logic.Axioms
