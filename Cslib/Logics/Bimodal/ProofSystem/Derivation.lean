/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Bimodal.ProofSystem.Axioms
public import Cslib.Logics.Bimodal.Syntax.Context

/-! # Derivation Trees for Bimodal Logic

This module defines derivation trees for bimodal logic TM,
representing syntactic provability from a context of assumptions.

## Main Definitions

- `DerivationTree fc Gamma phi`: Derivation tree parameterized by frame class
  `fc`, context `Gamma`, and conclusion `phi`
- `DerivationTree.lift`: Frame class monotonicity

## Inference Rules

The derivation tree includes 7 inference rules:
1. **axiom**: Axiom schema instance, gated by `ax.minFrameClass <= fc`
2. **assumption**: Formulas in context are derivable
3. **modus_ponens**: If `Gamma |-[fc] phi -> psi` and `Gamma |-[fc] phi`
   then `Gamma |-[fc] psi`
4. **necessitation**: If `|-[fc] phi` then `|-[fc] box phi`
5. **temporal_necessitation**: If `|-[fc] phi` then `|-[fc] G phi`
6. **temporal_duality**: If `|-[fc] phi` then `|-[fc] swapTemporal phi`
7. **weakening**: If `Gamma |-[fc] phi` and `Gamma <= Delta`
   then `Delta |-[fc] phi`
-/

set_option linter.style.emptyLine false

@[expose] public section

namespace Cslib.Logic.Bimodal

open Cslib.Logic.Bimodal

variable {Atom : Type u}

/--
Derivation tree for bimodal logic TM, parameterized by frame class.

`DerivationTree fc Gamma phi` represents a derivation tree showing
that formula `phi` is derivable from the context of assumptions `Gamma`
using only axioms compatible with frame class `fc`.
-/
inductive DerivationTree (fc : FrameClass) :
    Context Atom -> Formula Atom -> Type u where
  /-- Axiom rule: Axiom schema instances are derivable from any context,
      provided the axiom's minimum frame class is compatible
      with `fc`. -/
  | axiom (Gamma : Context Atom) (phi : Formula Atom) (h : Axiom phi)
      (h_fc : h.minFrameClass ≤ fc) : DerivationTree fc Gamma phi
  /-- Assumption rule: Formulas in the context are derivable. -/
  | assumption (Gamma : Context Atom) (phi : Formula Atom)
      (h : phi ∈ Gamma) : DerivationTree fc Gamma phi
  /-- Modus ponens: If `Gamma |-[fc] phi -> psi` and
      `Gamma |-[fc] phi` then `Gamma |-[fc] psi`. -/
  | modus_ponens (Gamma : Context Atom) (phi psi : Formula Atom)
      (d1 : DerivationTree fc Gamma (phi.imp psi))
      (d2 : DerivationTree fc Gamma phi) :
      DerivationTree fc Gamma psi
  /-- Necessitation: If `|-[fc] phi` then `|-[fc] box phi`. -/
  | necessitation (phi : Formula Atom)
      (d : DerivationTree fc [] phi) :
      DerivationTree fc [] (Formula.box phi)
  /-- Temporal necessitation: If `|-[fc] phi` then `|-[fc] G phi`. -/
  | temporal_necessitation (phi : Formula Atom)
      (d : DerivationTree fc [] phi) :
      DerivationTree fc [] phi.allFuture
  /-- Temporal duality: If `|-[fc] phi` then
      `|-[fc] swapTemporal phi`. -/
  | temporal_duality (phi : Formula Atom)
      (d : DerivationTree fc [] phi) :
      DerivationTree fc [] phi.swapTemporal
  /-- Weakening: If `Gamma |-[fc] phi` and `Gamma <= Delta` then
      `Delta |-[fc] phi`. -/
  | weakening (Gamma Delta : Context Atom) (phi : Formula Atom)
      (d : DerivationTree fc Gamma phi)
      (h : Gamma ⊆ Delta) : DerivationTree fc Delta phi

namespace DerivationTree

/-- Lift a derivation tree from frame class `fc1` to `fc2`
    when `fc1 <= fc2`. -/
def lift {fc₁ fc₂ : FrameClass} (h_le : fc₁ ≤ fc₂)
    {Gamma : Context Atom} {phi : Formula Atom} :
    DerivationTree fc₁ Gamma phi -> DerivationTree fc₂ Gamma phi
  | .axiom Gamma phi h h_fc =>
      .axiom Gamma phi h (le_trans h_fc h_le)
  | .assumption Gamma phi h => .assumption Gamma phi h
  | .modus_ponens Gamma phi psi d1 d2 =>
      .modus_ponens Gamma phi psi (d1.lift h_le) (d2.lift h_le)
  | .necessitation phi d =>
      .necessitation phi (d.lift h_le)
  | .temporal_necessitation phi d =>
      .temporal_necessitation phi (d.lift h_le)
  | .temporal_duality phi d =>
      .temporal_duality phi (d.lift h_le)
  | .weakening Gamma Delta phi d h =>
      .weakening Gamma Delta phi (d.lift h_le) h

/-- Default notation for derivability at Base frame class. -/
scoped notation:50 Gamma " ⊢ " phi =>
  DerivationTree FrameClass.Base Gamma phi

/-- Notation for derivability at explicit frame class. -/
scoped notation:50 Gamma " ⊢[" fc "] " phi =>
  DerivationTree fc Gamma phi

/-- Notation for theorem derivability (empty context) at Base. -/
scoped notation:50 "⊢ " phi =>
  DerivationTree FrameClass.Base ([] : Context _) phi

/-! ## Height Function -/

/--
Computable height function via pattern matching.

The height is defined as the maximum depth of the derivation tree:
- Base cases (axiom, assumption): height 0
- Compound cases: 1 + max height of subderivations
-/
def height {fc : FrameClass} {Gamma : Context Atom} {phi : Formula Atom} :
    DerivationTree fc Gamma phi → Nat
  | .axiom _ _ _ _ => 0
  | .assumption _ _ _ => 0
  | .modus_ponens _ _ _ d1 d2 => 1 + max d1.height d2.height
  | .necessitation _ d => 1 + d.height
  | .temporal_necessitation _ d => 1 + d.height
  | .temporal_duality _ d => 1 + d.height
  | .weakening _ _ _ d _ => 1 + d.height

/-- Modus ponens height is strictly greater than the left subderivation. -/
theorem mp_height_gt_left {fc : FrameClass} {Gamma : Context Atom}
    {phi psi : Formula Atom}
    (d1 : DerivationTree fc Gamma (phi.imp psi))
    (d2 : DerivationTree fc Gamma phi) :
    d1.height < (modus_ponens Gamma phi psi d1 d2).height := by
  simp [height]
  omega

/-- Modus ponens height is strictly greater than the right subderivation. -/
theorem mp_height_gt_right {fc : FrameClass} {Gamma : Context Atom}
    {phi psi : Formula Atom}
    (d1 : DerivationTree fc Gamma (phi.imp psi))
    (d2 : DerivationTree fc Gamma phi) :
    d2.height < (modus_ponens Gamma phi psi d1 d2).height := by
  simp [height]
  omega

/-- Weakening height is strictly greater than the subderivation. -/
theorem subderiv_height_lt {fc : FrameClass} {Gamma Delta : Context Atom}
    {phi : Formula Atom}
    (d : DerivationTree fc Gamma phi)
    (h : Gamma ⊆ Delta) :
    d.height < (weakening Gamma Delta phi d h).height := by
  simp [height]

end DerivationTree

end Cslib.Logic.Bimodal
