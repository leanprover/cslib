/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic KB5

This module proves soundness for modal logic KB5 (= K + B + 5): every formula
derivable from `KB5Axiom` is valid on symmetric + Euclidean frames.

KB5 has 7 axiom schemata -- the 4 propositional axioms, the K distribution axiom,
the B symmetry axiom (`φ → □◇φ`), and the 5 Euclidean axiom (`◇φ → □◇φ`).
The frame class for KB5 is symmetric + Euclidean.

## Main Results

- `kb5_axiom_sound`: Each of the 7 KB5 axiom schemata is valid over symmetric,
  Euclidean frames.
- `kb5_soundness`: If `Gamma |- phi` via `DerivationTree KB5Axiom`, then `phi` is
  satisfied at every world where all of `Gamma` is satisfied, on symmetric,
  Euclidean frames.
- `kb5_soundness_derivable`: If `phi` is KB5-derivable, then `phi` is valid on all
  symmetric, Euclidean frames.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## KB5 Axiom Soundness (BRV Definition 4.9 for KB5) -/

/-- Every axiom of KB5 is valid over symmetric, Euclidean frames.

Axiom B (`φ → □◇φ`) uses symmetry (Blackburn Theorem 4.28, clause 2);
axiom 5 (`◇φ → □◇φ`) uses Euclideanness.
Propositional axioms and K are valid on all frames. -/
theorem kb5_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : KB5Axiom φ) (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
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
  | modalB φ =>
    -- Goal: φ → □◇φ
    -- Satisfies: Satisfies m w φ → ∀ w', m.r w w' → Satisfies m w' (◇φ)
    -- ◇φ at w' means: (∀ v, m.r w' v → Satisfies m v φ → False) → False
    intro h_phi w' hr h_box_neg
    exact h_box_neg w (h_symm w w' hr) h_phi
  | modalFive φ =>
    -- Goal: ◇φ → □◇φ
    -- ◇φ at w means: (∀ v, m.r w v → Satisfies m v φ → False) → False
    -- □◇φ at w means: ∀ w', m.r w w' → ◇φ at w'
    -- ◇φ at w' means: (∀ v, m.r w' v → Satisfies m v φ → False) → False
    intro h_diam w' hr h_box_neg_w'
    apply h_diam
    intro w'' hr'' h_phi
    exact h_box_neg_w' w'' (h_eucl w w' w'' hr hr'') h_phi

/-! ## KB5 Soundness Theorems -/

/-- **KB5 Soundness**: If `Gamma |- phi` via `DerivationTree KB5Axiom`, then `phi` is
satisfied at every world where all of `Gamma` is satisfied, on symmetric,
Euclidean frames. -/
theorem kb5_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@KB5Axiom Atom) Γ φ)
    (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => kb5_axiom_sound h_ax m h_symm h_eucl w) w h_ctx

/-- **KB5 Soundness for derivable formulas**: If `phi` is KB5-derivable from the empty
context, then `phi` is valid on all symmetric, Euclidean frames. -/
theorem kb5_soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable (@KB5Axiom Atom) φ)
    (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ :=
  soundness_derivable h m
    (fun _ h_ax w => kb5_axiom_sound h_ax m h_symm h_eucl w) w

end Cslib.Logic.Modal
