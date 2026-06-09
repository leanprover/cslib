/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Modal.Metalogic.DerivationTree

/-! # Soundness Theorem for S5 Modal Logic

This module proves that every derivable formula is valid over the class of
reflexive, transitive, Euclidean Kripke frames (S5 frames).

## Main Results

- `axiom_sound`: Each of the 8 axiom schemata is valid over S5 frames.
- `soundness`: If `Γ ⊢ φ` (via `DerivationTree`), then `φ` is satisfied at every
  world of every S5 model where all of `Γ` is satisfied.
- `soundness_derivable`: If `⊢ φ` (derivable from empty context), then `φ` is
  valid in all S5 models.

## Design

The proof is by structural induction on `DerivationTree`. Each constructor case
reduces to either axiom validity (which is proven semantically) or preservation
of validity under the inference rules.

## References

* Cslib/Logics/Modal/Basic.lean — semantic definitions and axiom validity proofs
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Axiom Soundness -/

/-- Every axiom of S5 is valid over S5 frames (reflexive, transitive, Euclidean).

Handles all 8 axiom constructors:
- **Propositional axioms** (implyK, implyS, efq, peirce): Valid in ALL models.
- **Modal axioms** (K, T, 4, B): Valid over S5 frames using the frame conditions. -/
theorem axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : ModalAxiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ := by
  cases h_ax with
  | implyK φ ψ =>
    -- φ → (ψ → φ)
    intro hφ _
    exact hφ
  | implyS φ ψ χ =>
    -- (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
    intro h₁ h₂ h₃
    exact h₁ h₃ (h₂ h₃)
  | efq φ =>
    -- ⊥ → φ
    intro h
    exact absurd h id
  | peirce φ ψ =>
    -- ((φ → ψ) → φ) → φ
    intro h
    by_contra h_not
    exact h_not (h (fun hφ => absurd hφ h_not))
  | modalK φ ψ =>
    -- □(φ → ψ) → (□φ → □ψ)
    intro h_box_imp h_box_phi w' hr
    exact h_box_imp w' hr (h_box_phi w' hr)
  | modalT φ =>
    -- □φ → φ
    intro h_box
    exact h_box w (h_refl w)
  | modalFour φ =>
    -- □φ → □□φ
    intro h_box w₁ hr₁ w₂ hr₂
    exact h_box w₂ (h_trans w w₁ w₂ hr₁ hr₂)
  | modalB φ =>
    -- φ → □◇φ = φ → □(¬□¬φ) = φ → ∀ w', r w w' → ¬(∀ w'', r w' w'' → ¬sat w'' φ)
    -- With symmetry from refl+eucl: r w w' → r w' w
    intro hφ w' hr h_box_neg
    -- h_box_neg : ∀ w'', r w' w'' → Satisfies m w'' (¬φ) = ∀ w'', r w' w'' → ¬Satisfies m w'' φ
    -- Need: contradiction. We have r w w'. By symmetry, r w' w. So h_box_neg w gives ¬Satisfies m w φ.
    -- Symmetry from refl+eucl: r w w' and r w w → r w' w.
    -- h_refl gives r w w. h_eucl w w' w gives r w' w from r w w' and r w w.
    have h_symm : m.r w' w := h_eucl w w' w hr (h_refl w)
    exact h_box_neg w h_symm hφ

/-! ## Main Soundness Theorem -/

/-- **Soundness Theorem**: If `Γ ⊢ φ` (via `DerivationTree`), then for any S5 model `m`
and any world `w` where all formulas in `Γ` are satisfied, `φ` is also satisfied at `w`.

The proof is by structural induction on the derivation tree. -/
theorem soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Γ φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact axiom_sound h_ax m h_refl h_trans h_eucl w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact soundness d₁ m h_refl h_trans h_eucl w h_ctx
      (soundness d₂ m h_refl h_trans h_eucl w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hr
    exact soundness d' m h_refl h_trans h_eucl w' (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact soundness d' m h_refl h_trans h_eucl w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: If `φ` is derivable from the empty context,
then `φ` is satisfied at every world of every S5 model. -/
theorem soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ := by
  obtain ⟨d⟩ := h
  exact soundness d m h_refl h_trans h_eucl w (fun _ h => nomatch h)

end Cslib.Logic.Modal
