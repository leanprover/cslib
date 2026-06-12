/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic S4

This module proves soundness for modal logic S4 (= KT4): every formula derivable from
`S4Axiom` is valid on reflexive, transitive frames.

S4 has 7 axiom schemata -- the same as S5 minus the B axiom (`p → □◇p`).
The frame class for S4 is reflexive + transitive (Blackburn et al. Table 4.1, p.195).

## Main Results

- `s4_axiom_sound`: Each of the 7 S4 axiom schemata is valid over reflexive,
  transitive frames (Blackburn Definition 4.9, Table 4.1).
- `s4_soundness`: If `Gamma |- phi` via `DerivationTree S4Axiom`, then `phi` is
  satisfied at every world where all of `Gamma` is satisfied, on reflexive,
  transitive frames.
- `s4_soundness_derivable`: If `phi` is S4-derivable, then `phi` is valid on all
  reflexive, transitive frames.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## S4 Axiom Soundness (BRV Definition 4.9 for S4) -/

/-- Every axiom of S4 is valid over reflexive, transitive frames.

Axiom T (`□φ → φ`) uses reflexivity (Blackburn Theorem 4.28, clause 1);
axiom 4 (`□φ → □□φ`) uses transitivity (Blackburn Theorem 4.27).
Propositional axioms and K are valid on all frames. -/
theorem s4_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : S4Axiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
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
  | modalFour φ =>
    intro h_box w₁ hr₁ w₂ hr₂
    exact h_box w₂ (h_trans w w₁ w₂ hr₁ hr₂)

/-! ## S4 Soundness Theorems -/

/-- **S4 Soundness**: If `Gamma |- phi` via `DerivationTree S4Axiom`, then `phi` is
satisfied at every world where all of `Gamma` is satisfied, on reflexive,
transitive frames. -/
theorem s4_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@S4Axiom Atom) Γ φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => s4_axiom_sound h_ax m h_refl h_trans w) w h_ctx

/-- **S4 Soundness for derivable formulas**: If `phi` is S4-derivable from the empty
context, then `phi` is valid on all reflexive, transitive frames. -/
theorem s4_soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable (@S4Axiom Atom) φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (w : World) : Satisfies m w φ :=
  soundness_derivable h m
    (fun _ h_ax w => s4_axiom_sound h_ax m h_refl h_trans w) w

end Cslib.Logic.Modal
