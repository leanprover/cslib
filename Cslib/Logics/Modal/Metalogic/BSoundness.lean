/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic B (KB)

This module proves soundness for modal logic B over symmetric Kripke frames.

## Main Results

- `b_axiom_sound`: Each of the 6 BAxiom schemata is valid over symmetric frames.
- `b_soundness`: If `Gamma |- phi` via `DerivationTree BAxiom`, then `phi` is
  satisfied at every world of every symmetric model where `Gamma` is satisfied.
- `b_soundness_derivable`: Soundness for derivable formulas (empty context).

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.b` for semantic validity of B axiom
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## B Axiom Soundness -/

/-- Every axiom of B is valid over symmetric frames. -/
theorem b_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : BAxiom φ) (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World) : Satisfies m w φ := by
  cases h_ax with
  | implyK φ ψ =>
    intro hφ _
    exact hφ
  | implyS φ ψ χ =>
    intro h₁ h₂ h₃
    exact h₁ h₃ (h₂ h₃)
  | efq φ =>
    intro h
    exact absurd h id
  | peirce φ ψ =>
    intro h
    by_contra h_not
    exact h_not (h (fun hφ => absurd hφ h_not))
  | modalK φ ψ =>
    intro h_box_imp h_box_phi w' hr
    exact h_box_imp w' hr (h_box_phi w' hr)
  | modalB φ =>
    -- B axiom: φ → □◇φ where ◇φ = (□(φ → ⊥)) → ⊥
    -- Given hφ : Satisfies m w φ
    -- Need: ∀ w', m.r w w' → Satisfies m w' (◇φ)
    -- Unfolded: ∀ w', m.r w w' → (∀ w'', m.r w' w'' → Satisfies m w'' φ → False) → False
    -- By symmetry, m.r w' w, so h_box_neg w (h_symm w w' hr) hφ gives False
    intro hφ w' hr h_box_neg
    exact h_box_neg w (h_symm w w' hr) hφ

/-! ## B Soundness Wrappers -/

/-- B soundness: every derivable formula from context is valid over symmetric models. -/
theorem b_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@BAxiom Atom) Γ φ)
    (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun ψ h_ax w => b_axiom_sound h_ax m h_symm w) w h_ctx

/-- B soundness for derivable formulas (empty context). -/
theorem b_soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable (@BAxiom Atom) φ)
    (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World) : Satisfies m w φ :=
  soundness_derivable h m (fun ψ h_ax w => b_axiom_sound h_ax m h_symm w) w

end Cslib.Logic.Modal
