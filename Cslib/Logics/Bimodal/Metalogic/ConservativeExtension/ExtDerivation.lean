/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/
import Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ExtFormula
import Cslib.Logics.Bimodal.ProofSystem.Derivation

/-!
# Extended Proof System for Conservative Extension

This module defines the extended axiom and derivation types that mirror the base
proof system but use `ExtFormula` (with `ExtAtom Atom := Atom ⊕ Unit`).

The key construction is `embedDerivation`, which lifts any base derivation
to an extended derivation, preserving the proof structure.

## Main Definitions

- `ExtAxiom`: Axiom schemata for the extended language (mirrors `Axiom` exactly)
- `ExtAxiom.minFrameClass`: Frame class assignment mirroring `Axiom.minFrameClass`
- `ExtDerivationTree`: Derivation trees parameterized by `FrameClass`
- `embedAxiom`: Lifting of base axioms to extended axioms
- `embedDerivation`: Lifting of base derivations to extended derivations
-/

set_option linter.style.emptyLine false

namespace Cslib.Logic.Bimodal.Metalogic.ConservativeExtension

open Cslib.Logic.Bimodal

variable {Atom : Type u}

/-- Context in the extended language. -/
abbrev ExtContext (Atom : Type u) := List (ExtFormula Atom)

/--
Axiom schemata for the extended proof system.
Mirrors all axiom schemas from `Cslib.Logic.Bimodal.Axiom` but over `ExtFormula`.
-/
inductive ExtAxiom : ExtFormula Atom → Type u where
  -- Layer 1: Propositional (4)
  | imp_k (φ ψ χ : ExtFormula Atom) :
      ExtAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | imp_s (φ ψ : ExtFormula Atom) : ExtAxiom (φ.imp (ψ.imp φ))
  | efq (φ : ExtFormula Atom) : ExtAxiom (ExtFormula.bot.imp φ)
  | peirce (φ ψ : ExtFormula Atom) : ExtAxiom (((φ.imp ψ).imp φ).imp φ)

  -- Layer 2: S5 Modal (5)
  | modal_t (φ : ExtFormula Atom) : ExtAxiom (ExtFormula.box φ |>.imp φ)
  | modal_4 (φ : ExtFormula Atom) :
      ExtAxiom ((ExtFormula.box φ).imp (ExtFormula.box (ExtFormula.box φ)))
  | modal_b (φ : ExtFormula Atom) :
      ExtAxiom (φ.imp (ExtFormula.box φ.diamond))
  | modal_5_collapse (φ : ExtFormula Atom) :
      ExtAxiom (φ.box.diamond.imp φ.box)
  | modal_k_dist (φ ψ : ExtFormula Atom) :
      ExtAxiom ((φ.imp ψ).box.imp (φ.box.imp ψ.box))

  -- Layer 3: BX Temporal
  | serial_future :
      ExtAxiom (ExtFormula.top.imp (ExtFormula.some_future ExtFormula.top))
  | serial_past :
      ExtAxiom (ExtFormula.top.imp (ExtFormula.some_past ExtFormula.top))
  | left_mono_until_G (φ χ ψ : ExtFormula Atom) :
      ExtAxiom ((φ.imp χ).all_future.imp ((ExtFormula.untl ψ φ).imp (ExtFormula.untl ψ χ)))
  | left_mono_since_H (φ χ ψ : ExtFormula Atom) :
      ExtAxiom ((φ.imp χ).all_past.imp ((ExtFormula.snce ψ φ).imp (ExtFormula.snce ψ χ)))
  | right_mono_until (φ ψ χ : ExtFormula Atom) :
      ExtAxiom ((φ.imp ψ).all_future.imp ((ExtFormula.untl φ χ).imp (ExtFormula.untl ψ χ)))
  | right_mono_since (φ ψ χ : ExtFormula Atom) :
      ExtAxiom ((φ.imp ψ).all_past.imp ((ExtFormula.snce φ χ).imp (ExtFormula.snce ψ χ)))
  | connect_future (φ : ExtFormula Atom) :
      ExtAxiom (φ.imp (φ.some_past.all_future))
  | connect_past (φ : ExtFormula Atom) :
      ExtAxiom (φ.imp (φ.some_future.all_past))
  | enrichment_until (φ ψ p : ExtFormula Atom) :
      ExtAxiom (ExtFormula.and p (ExtFormula.untl ψ φ) |>.imp
        (ExtFormula.untl (ExtFormula.and ψ (ExtFormula.snce p φ)) φ))
  | enrichment_since (φ ψ p : ExtFormula Atom) :
      ExtAxiom (ExtFormula.and p (ExtFormula.snce ψ φ) |>.imp
        (ExtFormula.snce (ExtFormula.and ψ (ExtFormula.untl p φ)) φ))
  | self_accum_until (φ ψ : ExtFormula Atom) :
      ExtAxiom ((ExtFormula.untl ψ φ).imp
        (ExtFormula.untl ψ (ExtFormula.and φ (ExtFormula.untl ψ φ))))
  | self_accum_since (φ ψ : ExtFormula Atom) :
      ExtAxiom ((ExtFormula.snce ψ φ).imp
        (ExtFormula.snce ψ (ExtFormula.and φ (ExtFormula.snce ψ φ))))
  | absorb_until (φ ψ : ExtFormula Atom) :
      ExtAxiom ((ExtFormula.untl (ExtFormula.and φ (ExtFormula.untl ψ φ)) φ).imp
        (ExtFormula.untl ψ φ))
  | absorb_since (φ ψ : ExtFormula Atom) :
      ExtAxiom ((ExtFormula.snce (ExtFormula.and φ (ExtFormula.snce ψ φ)) φ).imp
        (ExtFormula.snce ψ φ))
  | linear_until (φ ψ χ θ : ExtFormula Atom) :
      ExtAxiom (ExtFormula.and (ExtFormula.untl ψ φ) (ExtFormula.untl θ χ)
        |>.imp (ExtFormula.or
          (ExtFormula.or
            (ExtFormula.untl (ExtFormula.and ψ θ) (ExtFormula.and φ χ))
            (ExtFormula.untl (ExtFormula.and ψ χ) (ExtFormula.and φ χ)))
          (ExtFormula.untl (ExtFormula.and φ θ) (ExtFormula.and φ χ))))
  | linear_since (φ ψ χ θ : ExtFormula Atom) :
      ExtAxiom (ExtFormula.and (ExtFormula.snce ψ φ) (ExtFormula.snce θ χ)
        |>.imp (ExtFormula.or
          (ExtFormula.or
            (ExtFormula.snce (ExtFormula.and ψ θ) (ExtFormula.and φ χ))
            (ExtFormula.snce (ExtFormula.and ψ χ) (ExtFormula.and φ χ)))
          (ExtFormula.snce (ExtFormula.and φ θ) (ExtFormula.and φ χ))))
  | until_F (φ ψ : ExtFormula Atom) :
      ExtAxiom ((ExtFormula.untl ψ φ).imp (ExtFormula.some_future ψ))
  | since_P (φ ψ : ExtFormula Atom) :
      ExtAxiom ((ExtFormula.snce ψ φ).imp (ExtFormula.some_past ψ))
  | temp_linearity (φ ψ : ExtFormula Atom) :
      ExtAxiom (ExtFormula.and (ExtFormula.some_future φ) (ExtFormula.some_future ψ) |>.imp
        (ExtFormula.or (ExtFormula.some_future (ExtFormula.and φ ψ))
          (ExtFormula.or (ExtFormula.some_future (ExtFormula.and φ (ExtFormula.some_future ψ)))
            (ExtFormula.some_future (ExtFormula.and (ExtFormula.some_future φ) ψ)))))
  | temp_linearity_past (φ ψ : ExtFormula Atom) :
      ExtAxiom (ExtFormula.and (ExtFormula.some_past φ) (ExtFormula.some_past ψ) |>.imp
        (ExtFormula.or (ExtFormula.some_past (ExtFormula.and φ ψ))
          (ExtFormula.or (ExtFormula.some_past (ExtFormula.and φ (ExtFormula.some_past ψ)))
            (ExtFormula.some_past (ExtFormula.and (ExtFormula.some_past φ) ψ)))))
  | F_until_equiv (φ : ExtFormula Atom) :
      ExtAxiom ((ExtFormula.some_future φ).imp (ExtFormula.untl φ ExtFormula.top))
  | P_since_equiv (φ : ExtFormula Atom) :
      ExtAxiom ((ExtFormula.some_past φ).imp (ExtFormula.snce φ ExtFormula.top))

  -- Layer 4: Modal-Temporal Interaction (1)
  | modal_future (φ : ExtFormula Atom) :
      ExtAxiom ((ExtFormula.box φ).imp (ExtFormula.box (ExtFormula.all_future φ)))

  -- Layer 5: Uniformity Axioms (5)
  | discrete_symm_fwd :
      ExtAxiom ((ExtFormula.untl ExtFormula.top ExtFormula.bot).imp
        (ExtFormula.snce ExtFormula.top ExtFormula.bot))
  | discrete_symm_bwd :
      ExtAxiom ((ExtFormula.snce ExtFormula.top ExtFormula.bot).imp
        (ExtFormula.untl ExtFormula.top ExtFormula.bot))
  | discrete_propagate_fwd :
      ExtAxiom ((ExtFormula.untl ExtFormula.top ExtFormula.bot).imp
        (ExtFormula.all_future (ExtFormula.untl ExtFormula.top ExtFormula.bot)))
  | discrete_propagate_bwd :
      ExtAxiom ((ExtFormula.untl ExtFormula.top ExtFormula.bot).imp
        (ExtFormula.all_past (ExtFormula.untl ExtFormula.top ExtFormula.bot)))
  | discrete_box_necessity :
      ExtAxiom ((ExtFormula.untl ExtFormula.top ExtFormula.bot).imp
        (ExtFormula.box (ExtFormula.untl ExtFormula.top ExtFormula.bot)))

  -- Layer 6: Prior Axioms (2)
  | prior_UZ (φ : ExtFormula Atom) :
      ExtAxiom (φ.some_future.imp (ExtFormula.untl φ φ.neg))
  | prior_SZ (φ : ExtFormula Atom) :
      ExtAxiom (φ.some_past.imp (ExtFormula.snce φ φ.neg))

  -- Layer 7: Z1 (1)
  | z1 (φ : ExtFormula Atom) :
      ExtAxiom ((φ.all_future.imp φ).all_future.imp (φ.all_future.some_future.imp φ.all_future))

  -- Layer 8: Density (2)
  | density (φ : ExtFormula Atom) :
      ExtAxiom ((φ.all_future.all_future).imp φ.all_future)
  | dense_indicator :
      ExtAxiom (ExtFormula.untl (ExtFormula.bot.imp ExtFormula.bot) ExtFormula.bot).neg

/-- Minimum frame class required by an extended axiom, mirroring `Axiom.minFrameClass`. -/
def ExtAxiom.minFrameClass {φ : ExtFormula Atom} : ExtAxiom φ → FrameClass
  | density _ => .Dense
  | dense_indicator => .Dense
  | prior_UZ _ => .Discrete
  | prior_SZ _ => .Discrete
  | z1 _ => .Discrete
  | _ => .Base

/--
Derivation tree for the extended proof system, parameterized by `FrameClass`.

The `h_fc` constraint on the `axiom` constructor ensures that only axioms compatible
with the frame class `fc` can appear in derivations, mirroring `DerivationTree`.
-/
inductive ExtDerivationTree (fc : FrameClass) :
    ExtContext Atom → ExtFormula Atom → Type u where
  | axiom (Γ : ExtContext Atom) (φ : ExtFormula Atom) (h : ExtAxiom φ)
      (h_fc : h.minFrameClass ≤ fc) :
      ExtDerivationTree fc Γ φ
  | assumption (Γ : ExtContext Atom) (φ : ExtFormula Atom) (h : φ ∈ Γ) :
      ExtDerivationTree fc Γ φ
  | modus_ponens (Γ : ExtContext Atom) (φ ψ : ExtFormula Atom)
      (d1 : ExtDerivationTree fc Γ (φ.imp ψ))
      (d2 : ExtDerivationTree fc Γ φ) : ExtDerivationTree fc Γ ψ
  | necessitation (φ : ExtFormula Atom)
      (d : ExtDerivationTree fc [] φ) : ExtDerivationTree fc [] (ExtFormula.box φ)
  | temporal_necessitation (φ : ExtFormula Atom)
      (d : ExtDerivationTree fc [] φ) : ExtDerivationTree fc [] (ExtFormula.all_future φ)
  | temporal_duality (φ : ExtFormula Atom)
      (d : ExtDerivationTree fc [] φ) : ExtDerivationTree fc [] φ.swap_temporal
  | weakening (Γ Δ : ExtContext Atom) (φ : ExtFormula Atom)
      (d : ExtDerivationTree fc Γ φ)
      (h : Γ ⊆ Δ) : ExtDerivationTree fc Δ φ

/-!
## Embedding Axioms
-/

/-- Embed a base axiom into an extended axiom. -/
def embedAxiom {φ : Formula Atom} : Axiom φ → ExtAxiom (embedFormula φ)
  | .imp_k a b c => .imp_k (embedFormula a) (embedFormula b) (embedFormula c)
  | .imp_s a b => .imp_s (embedFormula a) (embedFormula b)
  | .efq a => .efq (embedFormula a)
  | .peirce a b => .peirce (embedFormula a) (embedFormula b)
  | .modal_t a => .modal_t (embedFormula a)
  | .modal_4 a => .modal_4 (embedFormula a)
  | .modal_b a => .modal_b (embedFormula a)
  | .modal_5_collapse a => .modal_5_collapse (embedFormula a)
  | .modal_k_dist a b => .modal_k_dist (embedFormula a) (embedFormula b)
  | .serial_future => .serial_future
  | .serial_past => .serial_past
  | .left_mono_until_G a b c =>
    .left_mono_until_G (embedFormula a) (embedFormula b) (embedFormula c)
  | .left_mono_since_H a b c =>
    .left_mono_since_H (embedFormula a) (embedFormula b) (embedFormula c)
  | .right_mono_until a b c =>
    .right_mono_until (embedFormula a) (embedFormula b) (embedFormula c)
  | .right_mono_since a b c =>
    .right_mono_since (embedFormula a) (embedFormula b) (embedFormula c)
  | .connect_future a => .connect_future (embedFormula a)
  | .connect_past a => .connect_past (embedFormula a)
  | .enrichment_until a b c =>
    .enrichment_until (embedFormula a) (embedFormula b) (embedFormula c)
  | .enrichment_since a b c =>
    .enrichment_since (embedFormula a) (embedFormula b) (embedFormula c)
  | .self_accum_until a b => .self_accum_until (embedFormula a) (embedFormula b)
  | .self_accum_since a b => .self_accum_since (embedFormula a) (embedFormula b)
  | .absorb_until a b => .absorb_until (embedFormula a) (embedFormula b)
  | .absorb_since a b => .absorb_since (embedFormula a) (embedFormula b)
  | .linear_until a b c d =>
    .linear_until (embedFormula a) (embedFormula b) (embedFormula c) (embedFormula d)
  | .linear_since a b c d =>
    .linear_since (embedFormula a) (embedFormula b) (embedFormula c) (embedFormula d)
  | .until_F a b => .until_F (embedFormula a) (embedFormula b)
  | .since_P a b => .since_P (embedFormula a) (embedFormula b)
  | .temp_linearity a b => .temp_linearity (embedFormula a) (embedFormula b)
  | .temp_linearity_past a b => .temp_linearity_past (embedFormula a) (embedFormula b)
  | .F_until_equiv a => .F_until_equiv (embedFormula a)
  | .P_since_equiv a => .P_since_equiv (embedFormula a)
  | .modal_future a => .modal_future (embedFormula a)
  | .discrete_symm_fwd => .discrete_symm_fwd
  | .discrete_symm_bwd => .discrete_symm_bwd
  | .discrete_propagate_fwd => .discrete_propagate_fwd
  | .discrete_propagate_bwd => .discrete_propagate_bwd
  | .discrete_box_necessity => .discrete_box_necessity
  | .prior_UZ a => .prior_UZ (embedFormula a)
  | .prior_SZ a => .prior_SZ (embedFormula a)
  | .z1 a => .z1 (embedFormula a)
  | .density a => .density (embedFormula a)
  | .dense_indicator => .dense_indicator

/-- The minFrameClass of an embedded axiom equals the original's minFrameClass. -/
theorem embedAxiom_preserves_minFrameClass {φ : Formula Atom} (ax : Axiom φ) :
    (embedAxiom ax).minFrameClass = ax.minFrameClass := by
  cases ax <;> rfl

/-!
## Embedding Derivations
-/

/-- Helper: mapping a list under embedFormula preserves membership. -/
theorem mem_map_embedFormula {Γ : List (Formula Atom)} {φ : Formula Atom} (h : φ ∈ Γ) :
    embedFormula φ ∈ Γ.map embedFormula :=
  List.mem_map_of_mem (f := embedFormula) h

/-- Helper: mapping preserves list subset. -/
theorem map_embedFormula_subset {Γ Δ : List (Formula Atom)} (h : Γ ⊆ Δ) :
    Γ.map embedFormula ⊆ Δ.map embedFormula := by
  intro x hx
  rw [List.mem_map] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, h ha, rfl⟩

/-- Embed a base derivation into an extended derivation.

This is the key structural lemma: every proof in the base system
can be replayed in the extended system. The frame class is preserved.
-/
noncomputable def embedDerivation {fc : FrameClass} : {Γ : List (Formula Atom)} →
    {φ : Formula Atom} →
    DerivationTree fc Γ φ → ExtDerivationTree fc (Γ.map embedFormula) (embedFormula φ)
  | _, _, DerivationTree.axiom _Γ _φ h h_fc =>
    ExtDerivationTree.axiom _ _ (embedAxiom h) (embedAxiom_preserves_minFrameClass h ▸ h_fc)
  | _, _, DerivationTree.assumption _Γ _φ h =>
    ExtDerivationTree.assumption _ _ (mem_map_embedFormula h)
  | _, _, DerivationTree.modus_ponens _Γ a b d1 d2 =>
    ExtDerivationTree.modus_ponens _ (embedFormula a) (embedFormula b)
      (embedDerivation d1) (embedDerivation d2)
  | _, _, DerivationTree.necessitation _φ d =>
    ExtDerivationTree.necessitation _ (embedDerivation d)
  | _, _, DerivationTree.temporal_necessitation _φ d =>
    ExtDerivationTree.temporal_necessitation _ (embedDerivation d)
  | _, _, DerivationTree.temporal_duality φ' d =>
    embedFormula_swapTemporal φ' ▸
      ExtDerivationTree.temporal_duality _ (embedDerivation d)
  | _, _, DerivationTree.weakening _Γ _Δ _φ d h =>
    ExtDerivationTree.weakening _ _ _ (embedDerivation d) (map_embedFormula_subset h)

end Cslib.Logic.Bimodal.Metalogic.ConservativeExtension
