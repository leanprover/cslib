/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic T

This module proves soundness for modal logic T: every formula derivable from
`TAxiom` is valid on reflexive frames.

## Main Results

- `t_axiom_sound`: Each of the 6 T axiom schemata is valid over reflexive frames.
- `t_soundness`: If `Gamma |- phi` via `DerivationTree TAxiom`, then `phi` is
  satisfied at every world of every reflexive model where all of `Gamma` is satisfied.
- `t_soundness_derivable`: If `phi` is T-derivable, then `phi` is valid on all
  reflexive frames.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## T Axiom Soundness (BRV Definition 4.9 for T) -/

/-- Every axiom of T is valid over reflexive frames. -/
theorem t_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : TAxiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
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
  | modalT φ =>
    intro h_box
    exact h_box w (h_refl w)

/-! ## T Soundness Theorems -/

/-- **T Soundness**: If `Gamma |- phi` via `DerivationTree TAxiom`, then `phi` is
satisfied at every world of every reflexive model where all of `Gamma` is satisfied. -/
theorem t_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@TAxiom Atom) Γ φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => t_axiom_sound h_ax m h_refl w) w h_ctx

/-- **T Soundness for derivable formulas**: If `phi` is T-derivable from the empty
context, then `phi` is satisfied at every world of every reflexive model. -/
theorem t_soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable (@TAxiom Atom) φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (w : World) : Satisfies m w φ :=
  soundness_derivable h m (fun _ h_ax w => t_axiom_sound h_ax m h_refl w) w

end Cslib.Logic.Modal
