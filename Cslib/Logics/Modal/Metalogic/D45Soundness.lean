/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic D45 (KD45)

This module proves soundness for modal logic D45 over serial + transitive +
Euclidean Kripke frames. D45 = K + D + 4 + 5, combining the seriality axiom (D)
with the transitivity axiom (4) and the Euclideanness axiom (5), but without
axiom T.

## Main Results

- `d45_axiom_sound`: Each of the 8 D45Axiom schemata is valid over serial,
  transitive, Euclidean frames.
- `d45_soundness`: If `Gamma |- phi` via `DerivationTree D45Axiom`, then `phi` is
  satisfied at every world of every serial, transitive, Euclidean model where
  `Gamma` is satisfied.
- `d45_soundness_derivable`: Soundness for derivable formulas (empty context).

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.d` for semantic validity of D axiom
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.four` for semantic validity of 4 axiom
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.five` for semantic validity of 5 axiom
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## D45 Axiom Soundness -/

/-- Every axiom of D45 is valid over serial, transitive, Euclidean frames. -/
theorem d45_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : D45Axiom φ) (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
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
  | modalFour φ =>
    -- 4 axiom: □φ → □□φ
    -- By transitivity
    intro h_box w₁ hr₁ w₂ hr₂
    exact h_box w₂ (h_trans w w₁ w₂ hr₁ hr₂)
  | modalFive φ =>
    -- 5 axiom: ◇φ → □◇φ
    -- By Euclideanness
    intro hdiam v hrv hbox_neg_v
    apply hdiam
    intro u hru hsat
    exact hbox_neg_v u (h_eucl w v u hrv hru) hsat

/-! ## D45 Soundness Theorems -/

/-- D45 soundness: every derivable formula from context is valid over serial,
transitive, Euclidean models. -/
theorem d45_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@D45Axiom Atom) Γ φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => d45_axiom_sound h_ax m h_serial h_trans h_eucl w) w h_ctx

/-- D45 soundness for derivable formulas (empty context). -/
theorem d45_soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable (@D45Axiom Atom) φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ :=
  soundness_derivable h m
    (fun _ h_ax w => d45_axiom_sound h_ax m h_serial h_trans h_eucl w) w

end Cslib.Logic.Modal
