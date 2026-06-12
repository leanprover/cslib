/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic D5 (KD5)

This module proves soundness for modal logic D5 over serial + Euclidean Kripke
frames. D5 = K + D + 5, combining the seriality axiom (D) with the Euclideanness
axiom (5), but without axiom T.

## Main Results

- `d5_axiom_sound`: Each of the 7 D5Axiom schemata is valid over serial,
  Euclidean frames.
- `d5_soundness`: If `Gamma |- phi` via `DerivationTree D5Axiom`, then `phi` is
  satisfied at every world of every serial, Euclidean model where `Gamma` is
  satisfied.
- `d5_soundness_derivable`: Soundness for derivable formulas (empty context).

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.d` for semantic validity of D axiom
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.five` for semantic validity of axiom 5
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## D5 Axiom Soundness -/

/-- Every axiom of D5 is valid over serial, Euclidean frames. -/
theorem d5_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : D5Axiom φ) (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
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
    -- By seriality, obtain witness w' with m.r w w'
    intro h_box h_box_neg
    obtain ⟨w', hr⟩ := h_serial.serial w
    exact h_box_neg w' hr (h_box w' hr)
  | modalFive φ =>
    -- Axiom 5: ◇φ → □◇φ
    -- Unfolded: ((□(φ → ⊥)) → ⊥) → □((□(φ → ⊥)) → ⊥)
    intro h_diam w' hr h_box_neg_w'
    exact h_diam (fun w'' hr' h_phi =>
      h_box_neg_w' w'' (h_eucl w w' w'' hr hr') h_phi)

/-! ## D5 Soundness Theorems -/

/-- D5 soundness: every derivable formula from context is valid over serial,
Euclidean models. -/
theorem d5_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@D5Axiom Atom) Γ φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => d5_axiom_sound h_ax m h_serial h_eucl w) w h_ctx

/-- D5 soundness for derivable formulas (empty context). -/
theorem d5_soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable (@D5Axiom Atom) φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ :=
  soundness_derivable h m
    (fun _ h_ax w => d5_axiom_sound h_ax m h_serial h_eucl w) w

end Cslib.Logic.Modal
