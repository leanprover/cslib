/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic DB (KDB)

This module proves soundness for modal logic DB over serial + symmetric Kripke
frames. DB = K + D + B, combining the seriality axiom (D) with the symmetry
axiom (B), but without axiom T.

## Main Results

- `db_axiom_sound`: Each of the 7 DBAxiom schemata is valid over serial,
  symmetric frames.
- `db_soundness`: If `Gamma |- phi` via `DerivationTree DBAxiom`, then `phi` is
  satisfied at every world of every serial, symmetric model where `Gamma` is
  satisfied.
- `db_soundness_derivable`: Soundness for derivable formulas (empty context).

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.d` for semantic validity of D axiom
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.b` for semantic validity of B axiom
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## DB Axiom Soundness -/

/-- Every axiom of DB is valid over serial, symmetric frames. -/
theorem db_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : DBAxiom φ) (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
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
  | modalD φ =>
    -- D axiom: □φ → ◇φ where ◇φ = (□(φ → ⊥)) → ⊥
    -- By seriality, obtain witness w' with m.r w w'
    intro h_box h_box_neg
    obtain ⟨w', hr⟩ := h_serial.serial w
    exact h_box_neg w' hr (h_box w' hr)
  | modalB φ =>
    -- B axiom: φ → □◇φ where ◇φ = (□(φ → ⊥)) → ⊥
    -- By symmetry, m.r w' w, so h_box_neg w (h_symm w w' hr) hφ gives False
    intro hφ w' hr h_box_neg
    exact h_box_neg w (h_symm w w' hr) hφ

/-! ## DB Soundness Theorems -/

/-- DB soundness: every derivable formula from context is valid over serial,
symmetric models. -/
theorem db_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@DBAxiom Atom) Γ φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => db_axiom_sound h_ax m h_serial h_symm w) w h_ctx

/-- DB soundness for derivable formulas (empty context). -/
theorem db_soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable (@DBAxiom Atom) φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World) : Satisfies m w φ :=
  soundness_derivable h m
    (fun _ h_ax w => db_axiom_sound h_ax m h_serial h_symm w) w

end Cslib.Logic.Modal
