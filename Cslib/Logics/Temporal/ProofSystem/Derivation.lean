/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
import Cslib.Logics.Temporal.ProofSystem.Axioms
import Cslib.Logics.Temporal.Syntax.Context

/-! # Derivation Trees for Temporal Logic

This module defines derivation trees for temporal logic BX,
representing syntactic provability from a context of assumptions.

## Main Definitions

- `DerivationTree fc Γ φ`: Derivation tree parameterized by frame class `fc`,
  context `Γ`, and conclusion `φ`
- `DerivationTree.lift`: Frame class monotonicity

## Inference Rules

The derivation tree includes 6 inference rules:
1. **axiom**: Axiom schema instance, gated by `ax.minFrameClass ≤ fc`
2. **assumption**: Formulas in context are derivable
3. **modus_ponens**: If `Γ ⊢[fc] φ → ψ` and `Γ ⊢[fc] φ` then `Γ ⊢[fc] ψ`
4. **temporal_necessitation**: If `⊢[fc] φ` then `⊢[fc] Gφ`
5. **temporal_duality**: If `⊢[fc] φ` then `⊢[fc] swap_temporal φ`
6. **weakening**: If `Γ ⊢[fc] φ` and `Γ ⊆ Δ` then `Δ ⊢[fc] φ`
-/

set_option linter.style.emptyLine false

namespace Cslib.Logic.Temporal

open Cslib.Logic.Temporal

variable {Atom : Type u}

/--
Derivation tree for temporal logic BX, parameterized by frame class.

`DerivationTree fc Γ φ` represents a derivation tree showing that formula `φ` is
derivable from the context of assumptions `Γ` using only axioms compatible with
frame class `fc`.
-/
inductive DerivationTree (fc : FrameClass) :
    Context Atom → Formula Atom → Type u where
  /-- Axiom rule: Axiom schema instances are derivable from any context,
      provided the axiom's minimum frame class is compatible with `fc`. -/
  | axiom (Γ : Context Atom) (φ : Formula Atom) (h : Axiom φ)
      (h_fc : h.minFrameClass ≤ fc) : DerivationTree fc Γ φ
  /-- Assumption rule: Formulas in the context are derivable. -/
  | assumption (Γ : Context Atom) (φ : Formula Atom) (h : φ ∈ Γ) :
      DerivationTree fc Γ φ
  /-- Modus ponens: If `Γ ⊢[fc] φ → ψ` and `Γ ⊢[fc] φ` then `Γ ⊢[fc] ψ`. -/
  | modus_ponens (Γ : Context Atom) (φ ψ : Formula Atom)
      (d1 : DerivationTree fc Γ (φ.imp ψ))
      (d2 : DerivationTree fc Γ φ) : DerivationTree fc Γ ψ
  /-- Temporal necessitation: If `⊢[fc] φ` then `⊢[fc] Gφ`. -/
  | temporal_necessitation (φ : Formula Atom)
      (d : DerivationTree fc [] φ) : DerivationTree fc [] φ.all_future
  /-- Temporal duality: If `⊢[fc] φ` then `⊢[fc] swap_temporal φ`. -/
  | temporal_duality (φ : Formula Atom)
      (d : DerivationTree fc [] φ) : DerivationTree fc [] φ.swap_temporal
  /-- Weakening: If `Γ ⊢[fc] φ` and `Γ ⊆ Δ` then `Δ ⊢[fc] φ`. -/
  | weakening (Γ Δ : Context Atom) (φ : Formula Atom)
      (d : DerivationTree fc Γ φ)
      (h : Γ ⊆ Δ) : DerivationTree fc Δ φ

namespace DerivationTree

/-- Lift a derivation tree from frame class `fc₁` to `fc₂` when `fc₁ ≤ fc₂`. -/
def lift {fc₁ fc₂ : FrameClass} (h_le : fc₁ ≤ fc₂)
    {Γ : Context Atom} {φ : Formula Atom} :
    DerivationTree fc₁ Γ φ → DerivationTree fc₂ Γ φ
  | .axiom Γ φ h h_fc => .axiom Γ φ h (le_trans h_fc h_le)
  | .assumption Γ φ h => .assumption Γ φ h
  | .modus_ponens Γ φ ψ d1 d2 => .modus_ponens Γ φ ψ (d1.lift h_le) (d2.lift h_le)
  | .temporal_necessitation φ d => .temporal_necessitation φ (d.lift h_le)
  | .temporal_duality φ d => .temporal_duality φ (d.lift h_le)
  | .weakening Γ Δ φ d h => .weakening Γ Δ φ (d.lift h_le) h

/-- Default notation for derivability at Base frame class. -/
scoped notation:50 Γ " ⊢ " φ => DerivationTree FrameClass.Base Γ φ

/-- Notation for derivability at explicit frame class. -/
scoped notation:50 Γ " ⊢[" fc "] " φ => DerivationTree fc Γ φ

/-- Notation for theorem derivability (empty context) at Base. -/
scoped notation:50 "⊢ " φ => DerivationTree FrameClass.Base ([] : Context _) φ

end DerivationTree

end Cslib.Logic.Temporal
