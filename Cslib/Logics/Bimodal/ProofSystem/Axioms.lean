/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Syntax.Formula

/-! # Bimodal Axiom Schemata (BX System)

This module defines the concrete axiom inductive type for bimodal logic TM under the
Burgess-Xu (BX) axiom system. Each constructor maps directly to an axiom schema.

## Organization

- `FrameClass`: Classification for axiom validity (Base, Dense, Discrete)
- `Axiom`: Inductive type with 42 constructors (4 propositional + 5 modal + 22 temporal
  + 1 interaction + 5 uniformity + 2 prior + 1 Z1 + 2 density)
- `minFrameClass`: Minimum frame class for each axiom
-/

set_option linter.style.emptyLine false

@[expose] public section

namespace Cslib.Logic.Bimodal

open Cslib.Logic.Bimodal

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

instance : DecidableRel (LE.le : FrameClass -> FrameClass -> Prop) :=
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
Axiom schemata for bimodal logic TM under the Burgess-Xu (BX) system.

42 constructors organized into eight layers:
- **Propositional** (4): Classical propositional tautologies
- **S5 Modal** (5): S5 axioms for metaphysical necessity
- **BX Temporal** (22): Burgess-Xu axioms for Until/Since on linear orders
- **Interaction** (1): Modal-temporal interaction axiom MF
- **Uniformity** (5): Discreteness uniformity axioms
- **Prior** (2): Prior-UZ/SZ for discrete well-ordering
- **Z1** (1): IsSuccArchimedean characteristic axiom
- **Density** (2): GGphi -> Gphi and neg U(top, bot)
-/
inductive Axiom : Formula Atom -> Type u where
  -- Layer 1: Propositional (4)

  /-- Propositional K (distribution): (phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi)) -/
  | imp_k (phi psi chi : Formula Atom) :
      Axiom ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi)))

  /-- Propositional S (weakening): phi -> (psi -> phi) -/
  | imp_s (phi psi : Formula Atom) : Axiom (phi.imp (psi.imp phi))

  /-- Ex Falso Quodlibet: bot -> phi -/
  | efq (phi : Formula Atom) : Axiom (Formula.bot.imp phi)

  /-- Peirce's Law: ((phi -> psi) -> phi) -> phi -/
  | peirce (phi psi : Formula Atom) : Axiom (((phi.imp psi).imp phi).imp phi)

  -- Layer 2: S5 Modal (5)

  /-- Modal T: box phi -> phi (reflexivity) -/
  | modal_t (phi : Formula Atom) : Axiom (Formula.box phi |>.imp phi)

  /-- Modal 4: box phi -> box(box phi) (transitivity) -/
  | modal_4 (phi : Formula Atom) : Axiom ((Formula.box phi).imp (Formula.box (Formula.box phi)))

  /-- Modal B: phi -> box(diamond phi) (symmetry) -/
  | modal_b (phi : Formula Atom) : Axiom (phi.imp (Formula.box phi.diamond))

  /-- Modal 5 Collapse: diamond(box phi) -> box phi (S5 characteristic) -/
  | modal_5_collapse (phi : Formula Atom) : Axiom (phi.box.diamond.imp phi.box)

  /-- Modal K Distribution: box(phi -> psi) -> (box phi -> box psi) -/
  | modal_k_dist (phi psi : Formula Atom) :
      Axiom ((phi.imp psi).box.imp (phi.box.imp psi.box))

  -- Layer 3: BX Temporal (22)

  /-- BX1: Serial future: top -> F(top) -/
  | serial_future :
      Axiom (Formula.top.imp (Formula.someFuture Formula.top))

  /-- BX1': Serial past: top -> P(top) -/
  | serial_past :
      Axiom (Formula.top.imp (Formula.somePast Formula.top))

  /-- BX2G: Guard monotonicity of Until under G:
      G(phi -> chi) -> (psi U phi -> psi U chi) -/
  | left_mono_until_G (phi chi psi : Formula Atom) :
      Axiom ((phi.imp chi).allFuture.imp ((Formula.untl psi phi).imp (Formula.untl psi chi)))

  /-- BX2H: Guard monotonicity of Since under H:
      H(phi -> chi) -> (psi S phi -> psi S chi) -/
  | left_mono_since_H (phi chi psi : Formula Atom) :
      Axiom ((phi.imp chi).allPast.imp ((Formula.snce psi phi).imp (Formula.snce psi chi)))

  /-- BX3: Event monotonicity of Until:
      G(phi -> psi) -> (phi U chi -> psi U chi) -/
  | right_mono_until (phi psi chi : Formula Atom) :
      Axiom ((phi.imp psi).allFuture.imp ((Formula.untl phi chi).imp (Formula.untl psi chi)))

  /-- BX3': Event monotonicity of Since:
      H(phi -> psi) -> (phi S chi -> psi S chi) -/
  | right_mono_since (phi psi chi : Formula Atom) :
      Axiom ((phi.imp psi).allPast.imp ((Formula.snce phi chi).imp (Formula.snce psi chi)))

  /-- BX4: Temporal connectedness future: phi -> G(P(phi)) -/
  | connect_future (phi : Formula Atom) :
      Axiom (phi.imp (phi.somePast.allFuture))

  /-- BX4': Temporal connectedness past: phi -> H(F(phi)) -/
  | connect_past (phi : Formula Atom) :
      Axiom (phi.imp (phi.someFuture.allPast))

  /-- BX13: Until-Since enrichment:
      p and (psi U phi) -> (psi and S(p, phi)) U phi -/
  | enrichment_until (phi psi p : Formula Atom) :
      Axiom (Formula.and p (Formula.untl psi phi) |>.imp
        (Formula.untl (Formula.and psi (Formula.snce p phi)) phi))

  /-- BX13': Since-Until enrichment:
      p and (psi S phi) -> (psi and U(p, phi)) S phi -/
  | enrichment_since (phi psi p : Formula Atom) :
      Axiom (Formula.and p (Formula.snce psi phi) |>.imp
        (Formula.snce (Formula.and psi (Formula.untl p phi)) phi))

  /-- BX5: Self-accumulation of Until:
      U(psi, phi) -> U(psi, phi and U(psi, phi)) -/
  | self_accum_until (phi psi : Formula Atom) :
      Axiom ((Formula.untl psi phi).imp
        (Formula.untl psi (Formula.and phi (Formula.untl psi phi))))

  /-- BX5': Self-accumulation of Since:
      S(psi, phi) -> S(psi, phi and S(psi, phi)) -/
  | self_accum_since (phi psi : Formula Atom) :
      Axiom ((Formula.snce psi phi).imp
        (Formula.snce psi (Formula.and phi (Formula.snce psi phi))))

  /-- BX6: Absorption of Until:
      U(phi and U(psi, phi), phi) -> U(psi, phi) -/
  | absorb_until (phi psi : Formula Atom) :
      Axiom ((Formula.untl (Formula.and phi (Formula.untl psi phi)) phi).imp (Formula.untl psi phi))

  /-- BX6': Absorption of Since:
      S(phi and S(psi, phi), phi) -> S(psi, phi) -/
  | absorb_since (phi psi : Formula Atom) :
      Axiom ((Formula.snce (Formula.and phi (Formula.snce psi phi)) phi).imp
        (Formula.snce psi phi))

  /-- BX7: Linearity of Until:
      U(psi,phi) and U(theta,chi) ->
      U(psi and theta, phi and chi) or U(psi and chi, phi and chi) or
      U(phi and theta, phi and chi) -/
  | linear_until (phi psi chi theta : Formula Atom) :
      Axiom (Formula.and (Formula.untl psi phi) (Formula.untl theta chi)
        |>.imp (Formula.or
          (Formula.or
            (Formula.untl (Formula.and psi theta) (Formula.and phi chi))
            (Formula.untl (Formula.and psi chi) (Formula.and phi chi)))
          (Formula.untl (Formula.and phi theta) (Formula.and phi chi))))

  /-- BX7': Linearity of Since:
      S(psi,phi) and S(theta,chi) ->
      S(psi and theta, phi and chi) or S(psi and chi, phi and chi) or
      S(phi and theta, phi and chi) -/
  | linear_since (phi psi chi theta : Formula Atom) :
      Axiom (Formula.and (Formula.snce psi phi) (Formula.snce theta chi)
        |>.imp (Formula.or
          (Formula.or
            (Formula.snce (Formula.and psi theta) (Formula.and phi chi))
            (Formula.snce (Formula.and psi chi) (Formula.and phi chi)))
          (Formula.snce (Formula.and phi theta) (Formula.and phi chi))))

  /-- BX10: Until implies eventuality: U(psi, phi) -> F(psi) -/
  | until_F (phi psi : Formula Atom) :
      Axiom ((Formula.untl psi phi).imp (Formula.someFuture psi))

  /-- BX10': Since implies past eventuality: S(psi, phi) -> P(psi) -/
  | since_P (phi psi : Formula Atom) :
      Axiom ((Formula.snce psi phi).imp (Formula.somePast psi))

  /-- BX11: Temporal linearity:
      F(phi) and F(psi) -> F(phi and psi) or F(phi and F(psi)) or F(F(phi) and psi) -/
  | temp_linearity (phi psi : Formula Atom) :
      Axiom (Formula.and (Formula.someFuture phi) (Formula.someFuture psi) |>.imp
        (Formula.or (Formula.someFuture (Formula.and phi psi))
          (Formula.or (Formula.someFuture (Formula.and phi (Formula.someFuture psi)))
            (Formula.someFuture (Formula.and (Formula.someFuture phi) psi)))))

  /-- BX11': Temporal linearity past:
      P(phi) and P(psi) -> P(phi and psi) or P(phi and P(psi)) or P(P(phi) and psi) -/
  | temp_linearity_past (phi psi : Formula Atom) :
      Axiom (Formula.and (Formula.somePast phi) (Formula.somePast psi) |>.imp
        (Formula.or (Formula.somePast (Formula.and phi psi))
          (Formula.or (Formula.somePast (Formula.and phi (Formula.somePast psi)))
            (Formula.somePast (Formula.and (Formula.somePast phi) psi)))))

  /-- BX12: F-Until equivalence: F(phi) -> U(phi, top) -/
  | F_until_equiv (phi : Formula Atom) :
      Axiom ((Formula.someFuture phi).imp (Formula.untl phi Formula.top))

  /-- BX12': P-Since equivalence: P(phi) -> S(phi, top) -/
  | P_since_equiv (phi : Formula Atom) :
      Axiom ((Formula.somePast phi).imp (Formula.snce phi Formula.top))

  -- Layer 4: Modal-Temporal Interaction (1)

  /-- Modal-Future: box phi -> box(G phi). Necessary truths remain necessary in the future. -/
  | modal_future (phi : Formula Atom) :
      Axiom ((Formula.box phi).imp (Formula.box (Formula.allFuture phi)))

  -- Layer 5: Uniformity Axioms (5)

  /-- Discrete symmetry forward: U(top,bot) -> S(top,bot). -/
  | discrete_symm_fwd :
      Axiom ((Formula.untl (Formula.top) Formula.bot).imp
        (Formula.snce (Formula.top) Formula.bot))

  /-- Discrete symmetry backward: S(top,bot) -> U(top,bot). -/
  | discrete_symm_bwd :
      Axiom ((Formula.snce (Formula.top) Formula.bot).imp
        (Formula.untl (Formula.top) Formula.bot))

  /-- Discrete propagation forward: U(top,bot) -> G(U(top,bot)). -/
  | discrete_propagate_fwd :
      Axiom ((Formula.untl (Formula.top) Formula.bot).imp
        (Formula.allFuture (Formula.untl (Formula.top) Formula.bot)))

  /-- Discrete propagation backward: U(top,bot) -> H(U(top,bot)). -/
  | discrete_propagate_bwd :
      Axiom ((Formula.untl (Formula.top) Formula.bot).imp
        (Formula.allPast (Formula.untl (Formula.top) Formula.bot)))

  /-- Discrete box necessity: U(top,bot) -> box(U(top,bot)). -/
  | discrete_box_necessity :
      Axiom ((Formula.untl (Formula.top) Formula.bot).imp
        (Formula.box (Formula.untl (Formula.top) Formula.bot)))

  -- Layer 6: Prior Axioms (2)

  /-- Prior-UZ: F(phi) -> U(phi, neg phi). -/
  | prior_UZ (phi : Formula Atom) :
      Axiom (phi.someFuture.imp (Formula.untl phi phi.neg))

  /-- Prior-SZ: P(phi) -> S(phi, neg phi). -/
  | prior_SZ (phi : Formula Atom) :
      Axiom (phi.somePast.imp (Formula.snce phi phi.neg))

  -- Layer 7: Z1 Axiom (1)

  /-- Z1: G(G phi -> phi) -> (F(G phi) -> G phi). -/
  | z1 (phi : Formula Atom) :
      Axiom ((phi.allFuture.imp phi).allFuture.imp
        (phi.allFuture.someFuture.imp phi.allFuture))

  -- Layer 8: Density Axioms (2)

  /-- Density: G(G phi) -> G phi. -/
  | density (phi : Formula Atom) :
      Axiom (phi.allFuture.allFuture.imp phi.allFuture)

  /-- Dense indicator: neg U(top, bot). -/
  | dense_indicator :
      Axiom (Formula.untl (Formula.top) Formula.bot).neg

set_option linter.dupNamespace false in
/-- Minimum frame class for each axiom constructor.
    Base (37 axioms), Dense (2: density, dense_indicator), Discrete (3: prior_UZ, prior_SZ, z1). -/
def Axiom.minFrameClass {phi : Formula Atom} :
    Cslib.Logic.Bimodal.Axiom phi -> FrameClass
  | density _ => .Dense
  | dense_indicator => .Dense
  | prior_UZ _ => .Discrete
  | prior_SZ _ => .Discrete
  | z1 _ => .Discrete
  | _ => .Base

end Cslib.Logic.Bimodal
