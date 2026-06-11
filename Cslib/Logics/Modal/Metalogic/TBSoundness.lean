/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic TB

This module proves soundness for modal logic TB (= KTB): every formula derivable from
`TBAxiom` is valid on reflexive, symmetric frames.

TB has 7 axiom schemata -- the same as S4 but with axiom B (`φ → □◇φ`) replacing
axiom 4 (`□φ → □□φ`). The frame class for TB is reflexive + symmetric
(Blackburn et al. Table 4.1).

## Main Results

- `tb_axiom_sound`: Each of the 7 TB axiom schemata is valid over reflexive,
  symmetric frames (Blackburn Definition 4.9, Table 4.1).
- `tb_soundness`: If `Gamma |- phi` via `DerivationTree TBAxiom`, then `phi` is
  satisfied at every world where all of `Gamma` is satisfied, on reflexive,
  symmetric frames.
- `tb_soundness_derivable`: If `phi` is TB-derivable, then `phi` is valid on all
  reflexive, symmetric frames.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## TB Axiom Soundness (BRV Definition 4.9 for TB) -/

/-- Every axiom of TB is valid over reflexive, symmetric frames.

Axiom T (`□φ → φ`) uses reflexivity (Blackburn Theorem 4.28, clause 1);
axiom B (`φ → □◇φ`) uses symmetry (Blackburn Theorem 4.28, clause 2).
Propositional axioms and K are valid on all frames. -/
theorem tb_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : TBAxiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
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
  | modalT φ =>
    intro h_box
    exact h_box w (h_refl w)
  | modalB φ =>
    intro hφ w' hr h_box_neg
    exact h_box_neg w (h_symm w w' hr) hφ

/-! ## TB Soundness Theorems -/

/-- **TB Soundness**: If `Gamma |- phi` via `DerivationTree TBAxiom`, then `phi` is
satisfied at every world where all of `Gamma` is satisfied, on reflexive,
symmetric frames. -/
theorem tb_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@TBAxiom Atom) Γ φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun ψ h_ax w => tb_axiom_sound h_ax m h_refl h_symm w) w h_ctx

/-- **TB Soundness for derivable formulas**: If `phi` is TB-derivable from the empty
context, then `phi` is valid on all reflexive, symmetric frames. -/
theorem tb_soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable (@TBAxiom Atom) φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World) : Satisfies m w φ :=
  soundness_derivable h m
    (fun ψ h_ax w => tb_axiom_sound h_ax m h_refl h_symm w) w

end Cslib.Logic.Modal
