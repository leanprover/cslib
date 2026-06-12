/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Temporal.Syntax.Formula

/-! # Temporal Axiom Schemata (BX System)

This module defines the concrete axiom inductive type for temporal logic under the
Burgess-Xu (BX) axiom system. Each constructor maps directly to an axiom schema of the
BX temporal proof system.

## Organization

- `FrameClass`: Classification for axiom validity (Base, Dense, Discrete)
- `Axiom`: Inductive type with 26 constructors (4 propositional + 22 temporal)
- `minFrameClass`: Minimum frame class for each axiom
-/

set_option linter.style.emptyLine false

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic.Temporal

variable {Atom : Type u}

/--
Frame class classification for axiom validity.

- `Base`: all base axioms are valid on all linear orders
- `Dense`: extends Base with density axioms
- `Discrete`: extends Base with discreteness axioms
-/
inductive FrameClass where
  | Base
  | Dense
  | Discrete
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

instance : LE FrameClass where
  le a b := match a, b with
    | .Base, _ => True
    | .Dense, .Dense => True
    | .Discrete, .Discrete => True
    | _, _ => False

instance : DecidableRel (LE.le : FrameClass → FrameClass → Prop) :=
  fun a b => by cases a <;> cases b <;> simp only [LE.le] <;> infer_instance

instance : PartialOrder FrameClass where
  le := (· ≤ ·)
  le_refl := by intro a; cases a <;> simp [LE.le]
  le_trans := by intro a b c hab hbc; cases a <;> cases b <;> cases c <;> simp_all [LE.le]
  le_antisymm := by intro a b hab hba; cases a <;> cases b <;> simp_all [LE.le]

/-- Base is the minimum frame class. -/
theorem FrameClass.base_le (fc : FrameClass) : FrameClass.Base ≤ fc := by
  cases fc <;> trivial

/--
Axiom schemata for temporal logic under the Burgess-Xu (BX) system.

28 constructors organized into three layers:
- **Propositional** (4): Classical propositional tautologies
- **BX Temporal** (22): Burgess-Xu axioms for Until/Since on linear orders
- **Density** (2): Axioms valid on dense linear orders
-/
inductive Axiom : Formula Atom → Type u where
  -- Layer 1: Propositional (4)

  /-- Propositional K (distribution): (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)) -/
  | imp_k (φ ψ χ : Formula Atom) :
      Axiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))

  /-- Propositional S (weakening): φ → (ψ → φ) -/
  | imp_s (φ ψ : Formula Atom) : Axiom (φ.imp (ψ.imp φ))

  /-- Ex Falso Quodlibet: ⊥ → φ -/
  | efq (φ : Formula Atom) : Axiom (Formula.bot.imp φ)

  /-- Peirce's Law: ((φ → ψ) → φ) → φ -/
  | peirce (φ ψ : Formula Atom) : Axiom (((φ.imp ψ).imp φ).imp φ)

  -- Layer 2: BX Temporal (22)

  /-- BX1: Serial future: ⊤ → F(⊤) -/
  | serial_future :
      Axiom (Formula.top.imp (Formula.someFuture Formula.top))

  /-- BX1': Serial past: ⊤ → P(⊤) -/
  | serial_past :
      Axiom (Formula.top.imp (Formula.somePast Formula.top))

  /-- BX2G: Guard monotonicity of Until under G:
      G(φ → ψ) → (χ U φ → χ U ψ) -/
  | left_mono_until_G (φ ψ χ : Formula Atom) :
      Axiom ((φ.imp ψ).allFuture.imp ((Formula.untl χ φ).imp (Formula.untl χ ψ)))

  /-- BX2H: Guard monotonicity of Since under H:
      H(φ → ψ) → (χ S φ → χ S ψ) -/
  | left_mono_since_H (φ ψ χ : Formula Atom) :
      Axiom ((φ.imp ψ).allPast.imp ((Formula.snce χ φ).imp (Formula.snce χ ψ)))

  /-- BX3: Event monotonicity of Until:
      G(φ → ψ) → (φ U χ → ψ U χ) -/
  | right_mono_until (φ ψ χ : Formula Atom) :
      Axiom ((φ.imp ψ).allFuture.imp ((Formula.untl φ χ).imp (Formula.untl ψ χ)))

  /-- BX3': Event monotonicity of Since:
      H(φ → ψ) → (φ S χ → ψ S χ) -/
  | right_mono_since (φ ψ χ : Formula Atom) :
      Axiom ((φ.imp ψ).allPast.imp ((Formula.snce φ χ).imp (Formula.snce ψ χ)))

  /-- BX4: Temporal connectedness future: φ → G(P(φ)) -/
  | connect_future (φ : Formula Atom) :
      Axiom (φ.imp (φ.somePast.allFuture))

  /-- BX4': Temporal connectedness past: φ → H(F(φ)) -/
  | connect_past (φ : Formula Atom) :
      Axiom (φ.imp (φ.someFuture.allPast))

  /-- BX13: Until-Since enrichment:
      p ∧ (ψ U φ) → (ψ ∧ S(p, φ)) U φ -/
  | enrichment_until (φ ψ p : Formula Atom) :
      Axiom (Formula.and p (Formula.untl ψ φ) |>.imp
        (Formula.untl (Formula.and ψ (Formula.snce p φ)) φ))

  /-- BX13': Since-Until enrichment:
      p ∧ (ψ S φ) → (ψ ∧ U(p, φ)) S φ -/
  | enrichment_since (φ ψ p : Formula Atom) :
      Axiom (Formula.and p (Formula.snce ψ φ) |>.imp
        (Formula.snce (Formula.and ψ (Formula.untl p φ)) φ))

  /-- BX5: Self-accumulation of Until:
      U(ψ, φ) → U(ψ, φ ∧ U(ψ, φ)) -/
  | self_accum_until (φ ψ : Formula Atom) :
      Axiom ((Formula.untl ψ φ).imp
        (Formula.untl ψ (Formula.and φ (Formula.untl ψ φ))))

  /-- BX5': Self-accumulation of Since:
      S(ψ, φ) → S(ψ, φ ∧ S(ψ, φ)) -/
  | self_accum_since (φ ψ : Formula Atom) :
      Axiom ((Formula.snce ψ φ).imp
        (Formula.snce ψ (Formula.and φ (Formula.snce ψ φ))))

  /-- BX6: Absorption of Until:
      U(φ ∧ U(ψ, φ), φ) → U(ψ, φ) -/
  | absorb_until (φ ψ : Formula Atom) :
      Axiom ((Formula.untl (Formula.and φ (Formula.untl ψ φ)) φ).imp (Formula.untl ψ φ))

  /-- BX6': Absorption of Since:
      S(φ ∧ S(ψ, φ), φ) → S(ψ, φ) -/
  | absorb_since (φ ψ : Formula Atom) :
      Axiom ((Formula.snce (Formula.and φ (Formula.snce ψ φ)) φ).imp (Formula.snce ψ φ))

  /-- BX7: Linearity of Until:
      U(ψ,φ) ∧ U(θ,χ) → U(ψ∧θ, φ∧χ) ∨ U(ψ∧χ, φ∧χ) ∨ U(φ∧θ, φ∧χ) -/
  | linear_until (φ ψ χ θ : Formula Atom) :
      Axiom (Formula.and (Formula.untl ψ φ) (Formula.untl θ χ)
        |>.imp (Formula.or
          (Formula.or
            (Formula.untl (Formula.and ψ θ) (Formula.and φ χ))
            (Formula.untl (Formula.and ψ χ) (Formula.and φ χ)))
          (Formula.untl (Formula.and φ θ) (Formula.and φ χ))))

  /-- BX7': Linearity of Since:
      S(ψ,φ) ∧ S(θ,χ) → S(ψ∧θ, φ∧χ) ∨ S(ψ∧χ, φ∧χ) ∨ S(φ∧θ, φ∧χ) -/
  | linear_since (φ ψ χ θ : Formula Atom) :
      Axiom (Formula.and (Formula.snce ψ φ) (Formula.snce θ χ)
        |>.imp (Formula.or
          (Formula.or
            (Formula.snce (Formula.and ψ θ) (Formula.and φ χ))
            (Formula.snce (Formula.and ψ χ) (Formula.and φ χ)))
          (Formula.snce (Formula.and φ θ) (Formula.and φ χ))))

  /-- BX10: Until implies eventuality: U(ψ, φ) → F(ψ) -/
  | until_F (φ ψ : Formula Atom) :
      Axiom ((Formula.untl ψ φ).imp (Formula.someFuture ψ))

  /-- BX10': Since implies past eventuality: S(ψ, φ) → P(ψ) -/
  | since_P (φ ψ : Formula Atom) :
      Axiom ((Formula.snce ψ φ).imp (Formula.somePast ψ))

  /-- BX11: Temporal linearity:
      F(φ) ∧ F(ψ) → F(φ ∧ ψ) ∨ F(φ ∧ F(ψ)) ∨ F(F(φ) ∧ ψ) -/
  | temp_linearity (φ ψ : Formula Atom) :
      Axiom (Formula.and (Formula.someFuture φ) (Formula.someFuture ψ) |>.imp
        (Formula.or (Formula.someFuture (Formula.and φ ψ))
          (Formula.or (Formula.someFuture (Formula.and φ (Formula.someFuture ψ)))
            (Formula.someFuture (Formula.and (Formula.someFuture φ) ψ)))))

  /-- BX11': Temporal linearity past:
      P(φ) ∧ P(ψ) → P(φ ∧ ψ) ∨ P(φ ∧ P(ψ)) ∨ P(P(φ) ∧ ψ) -/
  | temp_linearity_past (φ ψ : Formula Atom) :
      Axiom (Formula.and (Formula.somePast φ) (Formula.somePast ψ) |>.imp
        (Formula.or (Formula.somePast (Formula.and φ ψ))
          (Formula.or (Formula.somePast (Formula.and φ (Formula.somePast ψ)))
            (Formula.somePast (Formula.and (Formula.somePast φ) ψ)))))

  /-- BX12: F-Until equivalence: F(φ) → U(φ, ⊤) -/
  | F_until_equiv (φ : Formula Atom) :
      Axiom ((Formula.someFuture φ).imp (Formula.untl φ Formula.top))

  /-- BX12': P-Since equivalence: P(φ) → S(φ, ⊤) -/
  | P_since_equiv (φ : Formula Atom) :
      Axiom ((Formula.somePast φ).imp (Formula.snce φ Formula.top))

  -- Layer 3: Density (2)

  /-- Density axiom: G(G(φ)) → G(φ). Valid on densely ordered frames. -/
  | density (φ : Formula Atom) :
      Axiom (φ.allFuture.allFuture.imp φ.allFuture)

  /-- Dense indicator: ¬U(⊤, ⊥). Asserts no immediate successor exists.
      Valid on densely ordered frames. -/
  | dense_indicator :
      Axiom (Formula.untl Formula.top Formula.bot).neg

set_option linter.dupNamespace false in
/-- Minimum frame class for each axiom constructor. Base BX axioms
    are valid on all linear temporal orders. Density axioms require
    densely ordered frames. -/
def Axiom.minFrameClass {φ : Formula Atom} :
    Cslib.Logic.Temporal.Axiom φ → FrameClass
  | .density _ => .Dense
  | .dense_indicator => .Dense
  | _ => .Base

end Cslib.Logic.Temporal
