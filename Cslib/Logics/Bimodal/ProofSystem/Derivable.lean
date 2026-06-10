/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/
import Cslib.Logics.Bimodal.ProofSystem.Derivation

/-! # Derivable - Prop-Valued Derivability Wrapper for Bimodal Logic

This module provides a Prop-valued wrapper `Derivable` around the Type-valued
`DerivationTree`, enabling classical reasoning for derivability goals.

## Main Definitions

- `Bimodal.Derivable fc Gamma p`: Prop-valued derivability parameterized
  by frame class `fc`
- Constructor-mirroring lemmas: `ax`, `assume`, `mp`, `nec`, `temp_nec`,
  `temp_dual`, `weaken`
- `Derivable.lift`: Frame class monotonicity for Prop-valued derivability
-/

set_option linter.dupNamespace false

namespace Cslib.Logic.Bimodal

open Cslib.Logic.Bimodal

variable {Atom : Type u}

/-- Prop-valued derivability: `Bimodal.Derivable fc Gamma p` holds iff
    there exists a derivation tree for `p` from context `Gamma` at
    frame class `fc`. -/
def Bimodal.Derivable (fc : FrameClass) (Gamma : Context Atom)
    (p : Formula Atom) : Prop :=
  Nonempty (DerivationTree fc Gamma p)

/-! ## Coercion from DerivationTree -/

/-- Any derivation tree witnesses Prop-valued derivability. -/
theorem Bimodal.Derivable.ofTree {fc : FrameClass}
    {Gamma : Context Atom} {p : Formula Atom}
    (d : DerivationTree fc Gamma p) :
    Bimodal.Derivable fc Gamma p :=
  Nonempty.intro d

/-! ## Lift (Frame Class Monotonicity) -/

/-- Lift Prop-valued derivability from `fc1` to `fc2`
    when `fc1 <= fc2`. -/
theorem Bimodal.Derivable.lift {fc₁ fc₂ : FrameClass}
    (h_le : fc₁ ≤ fc₂)
    {Gamma : Context Atom} {p : Formula Atom}
    (h : Bimodal.Derivable fc₁ Gamma p) :
    Bimodal.Derivable fc₂ Gamma p := by
  obtain ⟨d⟩ := h
  exact Nonempty.intro (d.lift h_le)

/-! ## Constructor-Mirroring Lemmas -/

/-- Axiom rule: Any axiom schema instance is derivable
    (Prop-valued). -/
theorem Bimodal.Derivable.ax {fc : FrameClass}
    (Gamma : Context Atom) (p : Formula Atom)
    (h : Axiom p) (h_fc : h.minFrameClass ≤ fc) :
    Bimodal.Derivable fc Gamma p :=
  Nonempty.intro (DerivationTree.axiom Gamma p h h_fc)

/-- Assumption rule: Formulas in context are derivable
    (Prop-valued). -/
theorem Bimodal.Derivable.assume {fc : FrameClass}
    (Gamma : Context Atom) (p : Formula Atom)
    (h : p ∈ Gamma) : Bimodal.Derivable fc Gamma p :=
  Nonempty.intro (DerivationTree.assumption Gamma p h)

/-- Modus ponens (Prop-valued). -/
theorem Bimodal.Derivable.mp {fc : FrameClass}
    {Gamma : Context Atom} {p q : Formula Atom}
    (h1 : Bimodal.Derivable fc Gamma (p.imp q))
    (h2 : Bimodal.Derivable fc Gamma p) :
    Bimodal.Derivable fc Gamma q := by
  obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
  exact Nonempty.intro
    (DerivationTree.modus_ponens Gamma p q d1 d2)

/-- Modal necessitation: If `|-! p` then `|-! box p`
    (Prop-valued). -/
theorem Bimodal.Derivable.nec {fc : FrameClass}
    {p : Formula Atom}
    (h : Bimodal.Derivable fc [] p) :
    Bimodal.Derivable fc [] (Formula.box p) := by
  obtain ⟨d⟩ := h
  exact Nonempty.intro (DerivationTree.necessitation p d)

/-- Temporal necessitation: If `|-! p` then `|-! G p`
    (Prop-valued). -/
theorem Bimodal.Derivable.temp_nec {fc : FrameClass}
    {p : Formula Atom}
    (h : Bimodal.Derivable fc [] p) :
    Bimodal.Derivable fc [] p.allFuture := by
  obtain ⟨d⟩ := h
  exact Nonempty.intro
    (DerivationTree.temporal_necessitation p d)

/-- Temporal duality: If `|-! p` then `|-! swapTemporal p`
    (Prop-valued). -/
theorem Bimodal.Derivable.temp_dual {fc : FrameClass}
    {p : Formula Atom}
    (h : Bimodal.Derivable fc [] p) :
    Bimodal.Derivable fc [] p.swapTemporal := by
  obtain ⟨d⟩ := h
  exact Nonempty.intro
    (DerivationTree.temporal_duality p d)

/-- Weakening: If `Gamma |-! p` and `Gamma <= Delta` then
    `Delta |-! p` (Prop-valued). -/
theorem Bimodal.Derivable.weaken {fc : FrameClass}
    {Gamma Delta : Context Atom} {p : Formula Atom}
    (h : Bimodal.Derivable fc Gamma p)
    (hsub : Gamma ⊆ Delta) :
    Bimodal.Derivable fc Delta p := by
  obtain ⟨d⟩ := h
  exact Nonempty.intro
    (DerivationTree.weakening Gamma Delta p d hsub)

end Cslib.Logic.Bimodal
