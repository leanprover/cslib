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

end Cslib.Logic.Modal
