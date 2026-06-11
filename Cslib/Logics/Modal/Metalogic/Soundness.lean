/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.DerivationTree

/-! # Soundness Theorem for Normal Modal Logics

This module proves soundness parameterized over an axiom predicate
`Axioms : Proposition Atom -> Prop` with a generic axiom soundness callback.
The parameterized infrastructure supports all normal modal logics; an
S5-specific wrapper instantiates at `ModalAxiom`.

## Main Results

- `axiom_sound`: Each of the 8 S5 axiom schemata is valid over S5 frames.
- `soundness`: Parameterized soundness -- if `Gamma |- phi` (via `DerivationTree Axioms`),
  then `phi` is satisfied at every world where all of `Gamma` is satisfied, given a
  soundness callback for `Axioms`.
- `s5_soundness`: S5-specific wrapper combining `axiom_sound` with `soundness`.

## Design

The parameterized `soundness` theorem takes a callback `h_ax_sound` that proves
each axiom of `Axioms` is valid in the given model. The S5-specific `axiom_sound`
theorem handles the concrete `ModalAxiom` cases.

## References

* Cslib/Logics/Modal/Basic.lean -- semantic definitions and axiom validity proofs
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## S5 Axiom Soundness -/

/-- Every axiom of S5 is valid over S5 frames (reflexive, transitive, Euclidean). -/
theorem axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : ModalAxiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
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
  | modalT φ =>
    intro h_box
    exact h_box w (h_refl w)
  | modalFour φ =>
    intro h_box w₁ hr₁ w₂ hr₂
    exact h_box w₂ (h_trans w w₁ w₂ hr₁ hr₂)
  | modalB φ =>
    intro hφ w' hr h_box_neg
    have h_symm : m.r w' w := h_eucl w w' w hr (h_refl w)
    exact h_box_neg w h_symm hφ

/-! ## Parameterized Soundness Theorem -/

/-- **Parameterized Soundness**: If `Gamma |- phi` (via `DerivationTree Axioms`), then
for any model `m` and any world `w` where all formulas in `Gamma` are satisfied,
`phi` is also satisfied at `w`, given that all axioms in `Axioms` are valid. -/
theorem soundness {Axioms : Proposition Atom → Prop} {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Axioms Γ φ)
    (m : Model World Atom)
    (h_ax_sound : ∀ (ψ : Proposition Atom), Axioms ψ → ∀ (w : World),
      Satisfies m w ψ)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact h_ax_sound ψ h_ax w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact soundness d₁ m h_ax_sound w h_ctx
      (soundness d₂ m h_ax_sound w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hr
    exact soundness d' m h_ax_sound w' (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact soundness d' m h_ax_sound w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Parameterized Soundness for derivable formulas**: If `phi` is derivable from
the empty context, then `phi` is satisfied at every world. -/
theorem soundness_derivable {Axioms : Proposition Atom → Prop} {World : Type*}
    {φ : Proposition Atom} (h : Derivable Axioms φ)
    (m : Model World Atom)
    (h_ax_sound : ∀ (ψ : Proposition Atom), Axioms ψ → ∀ (w : World),
      Satisfies m w ψ)
    (w : World) : Satisfies m w φ := by
  obtain ⟨d⟩ := h
  exact soundness d m h_ax_sound w (fun _ h => nomatch h)

/-! ## S5-specific wrappers -/

/-- S5 soundness: every derivable formula is valid over S5 frames. -/
theorem s5_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@ModalAxiom Atom) Γ φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => axiom_sound h_ax m h_refl h_trans h_eucl w) w h_ctx

/-- S5 soundness for derivable formulas. -/
theorem s5_soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable (@ModalAxiom Atom) φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ :=
  soundness_derivable h m
    (fun _ h_ax w => axiom_sound h_ax m h_refl h_trans h_eucl w) w

end Cslib.Logic.Modal
