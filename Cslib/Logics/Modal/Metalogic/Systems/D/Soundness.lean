/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic D (KD)

This module proves soundness for modal logic D over serial Kripke frames.

## Main Results

- `d_axiom_sound`: Each of the 6 DAxiom schemata is valid over serial frames.
- `d_soundness`: If `Gamma |- phi` via `DerivationTree DAxiom`, then `phi` is
  satisfied at every world of every serial model where `Gamma` is satisfied.
- `d_soundness_derivable`: Soundness for derivable formulas (empty context).

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.d` for semantic validity of D axiom
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## D Axiom Soundness -/

/-- Every axiom of D is valid over serial frames. -/
theorem d_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : DAxiom φ) (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
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
  | modalD φ =>
    -- D axiom: □φ → ◇φ where ◇φ = (□(φ → ⊥)) → ⊥
    -- Given h_box : ∀ w', m.r w w' → Satisfies m w' φ
    -- Need to show: (∀ w', m.r w w' → Satisfies m w' φ → False) → False
    -- By seriality, obtain witness w' with m.r w w'
    intro h_box h_box_neg
    obtain ⟨w', hr⟩ := h_serial.serial w
    exact h_box_neg w' hr (h_box w' hr)

/-! ## D Soundness Theorems -/

/-- D soundness: every derivable formula from context is valid over serial models. -/
theorem d_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@DAxiom Atom) Γ φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => d_axiom_sound h_ax m h_serial w) w h_ctx

/-- D soundness for derivable formulas (empty context). -/
theorem d_soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable (@DAxiom Atom) φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (w : World) : Satisfies m w φ :=
  soundness_derivable h m (fun _ h_ax w => d_axiom_sound h_ax m h_serial w) w

end Cslib.Logic.Modal
