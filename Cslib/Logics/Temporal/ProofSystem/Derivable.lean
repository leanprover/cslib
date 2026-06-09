/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/
import Cslib.Logics.Temporal.ProofSystem.Derivation

/-! # Derivable - Prop-Valued Derivability Wrapper for Temporal Logic

This module provides a Prop-valued wrapper `Derivable` around the Type-valued
`DerivationTree`, enabling classical reasoning for derivability goals.

## Main Definitions

- `Derivable fc Γ p`: Prop-valued derivability parameterized by frame class `fc`
- Constructor-mirroring lemmas: `ax`, `assume`, `mp`, `temp_nec`, `temp_dual`, `weaken`
- `Derivable.lift`: Frame class monotonicity for Prop-valued derivability
-/

set_option linter.dupNamespace false

namespace Cslib.Logic.Temporal

open Cslib.Logic.Temporal

variable {Atom : Type u}

/-- Prop-valued derivability: `Derivable fc Γ p` holds iff there exists a derivation tree
    for `p` from context `Γ` at frame class `fc`. -/
def Temporal.Derivable (fc : FrameClass) (Γ : Context Atom) (p : Formula Atom) : Prop :=
  Nonempty (DerivationTree fc Γ p)

/-! ## Coercion from DerivationTree -/

/-- Any derivation tree witnesses Prop-valued derivability. -/
theorem Temporal.Derivable.ofTree {fc : FrameClass} {Γ : Context Atom}
    {p : Formula Atom}
    (d : DerivationTree fc Γ p) : Temporal.Derivable fc Γ p :=
  Nonempty.intro d

/-! ## Lift (Frame Class Monotonicity) -/

/-- Lift Prop-valued derivability from `fc₁` to `fc₂` when `fc₁ ≤ fc₂`. -/
theorem Temporal.Derivable.lift {fc₁ fc₂ : FrameClass} (h_le : fc₁ ≤ fc₂)
    {Γ : Context Atom} {p : Formula Atom}
    (h : Temporal.Derivable fc₁ Γ p) : Temporal.Derivable fc₂ Γ p := by
  obtain ⟨d⟩ := h
  exact Nonempty.intro (d.lift h_le)

/-! ## Constructor-Mirroring Lemmas -/

/-- Axiom rule: Any axiom schema instance is derivable (Prop-valued). -/
theorem Temporal.Derivable.ax {fc : FrameClass} (Γ : Context Atom)
    (p : Formula Atom)
    (h : Axiom p) (h_fc : h.minFrameClass ≤ fc) :
    Temporal.Derivable fc Γ p :=
  Nonempty.intro (DerivationTree.axiom Γ p h h_fc)

/-- Assumption rule: Formulas in context are derivable (Prop-valued). -/
theorem Temporal.Derivable.assume {fc : FrameClass} (Γ : Context Atom)
    (p : Formula Atom) (h : p ∈ Γ) : Temporal.Derivable fc Γ p :=
  Nonempty.intro (DerivationTree.assumption Γ p h)

/-- Modus ponens (Prop-valued). -/
theorem Temporal.Derivable.mp {fc : FrameClass} {Γ : Context Atom}
    {p q : Formula Atom}
    (h1 : Temporal.Derivable fc Γ (p.imp q))
    (h2 : Temporal.Derivable fc Γ p) :
    Temporal.Derivable fc Γ q := by
  obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
  exact Nonempty.intro (DerivationTree.modus_ponens Γ p q d1 d2)

/-- Temporal necessitation: If `|-! p` then `|-! Gp` (Prop-valued). -/
theorem Temporal.Derivable.temp_nec {fc : FrameClass} {p : Formula Atom}
    (h : Temporal.Derivable fc [] p) :
    Temporal.Derivable fc [] p.all_future := by
  obtain ⟨d⟩ := h
  exact Nonempty.intro (DerivationTree.temporal_necessitation p d)

/-- Temporal duality: If `|-! p` then `|-! swap_temporal p` (Prop-valued). -/
theorem Temporal.Derivable.temp_dual {fc : FrameClass} {p : Formula Atom}
    (h : Temporal.Derivable fc [] p) :
    Temporal.Derivable fc [] p.swap_temporal := by
  obtain ⟨d⟩ := h
  exact Nonempty.intro (DerivationTree.temporal_duality p d)

/-- Weakening: If `Γ |-! p` and `Γ ⊆ Δ` then `Δ |-! p` (Prop-valued). -/
theorem Temporal.Derivable.weaken {fc : FrameClass}
    {Γ Δ : Context Atom} {p : Formula Atom}
    (h : Temporal.Derivable fc Γ p) (hsub : Γ ⊆ Δ) :
    Temporal.Derivable fc Δ p := by
  obtain ⟨d⟩ := h
  exact Nonempty.intro (DerivationTree.weakening Γ Δ p d hsub)

end Cslib.Logic.Temporal
