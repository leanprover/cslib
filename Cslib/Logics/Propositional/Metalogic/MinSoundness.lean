/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Kripke
public import Cslib.Logics.Propositional.ProofSystem.Derivation
public import Cslib.Logics.Propositional.ProofSystem.Axioms

/-! # Soundness Theorem for Minimal Propositional Logic

This module proves soundness for minimal propositional logic (MinPropAxiom):
every derivable formula is minimally valid (MValid).

## Main Results

- `min_axiom_sound`: Each of the 2 axiom schemata (implyK, implyS) is MValid.
- `min_soundness`: If `DerivationTree MinPropAxiom Γ φ`, then `φ` is forced at every
  world of every Kripke model (with arbitrary upward-closed `bot_forces`) where all
  of `Γ` is forced.
- `min_soundness_derivable`: If `Derivable MinPropAxiom φ`, then `MValid φ`.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43 (soundness direction, adapted for minimal logic), Proposition 2.1 (persistence lemma)
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## Axiom Soundness -/

/-- Every axiom of minimal propositional logic is MValid.

The 2 cases are:
- **implyK**: `φ → (ψ → φ)` -- uses persistence to carry `φ` to successor worlds.
- **implyS**: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -- uses transitivity of ≤. -/
theorem min_axiom_sound {φ : PL.Proposition Atom}
    (h_ax : MinPropAxiom φ) : MValid.{_, v} φ := by
  intro World _ val bot_forces v_uc bf_uc w
  cases h_ax with
  | implyK φ ψ =>
    -- Goal: IForces val bf w (φ → (ψ → φ))
    -- = ∀ w' ≥ w, IForces w' φ → ∀ w'' ≥ w', IForces w'' ψ → IForces w'' φ
    intro w' _ hφ w'' hw' _
    exact iforces_persistence v_uc bf_uc hw' hφ
  | implyS φ ψ χ =>
    -- Goal: IForces val bf w ((φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)))
    intro w₁ hw₁ h_pqr w₂ hw₂ h_pq w₃ hw₃ h_p
    have h₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pqr w₃ h₁₃ h_p w₃ (le_refl w₃) (h_pq w₃ hw₃ h_p)

/-! ## Soundness Theorem -/

/-- **Soundness**: If `DerivationTree MinPropAxiom Γ φ`, then for any Kripke model
(with arbitrary upward-closed `bot_forces`) and world `w` where all formulas in `Γ`
are forced, `φ` is also forced at `w`. -/
theorem min_soundness
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree MinPropAxiom Γ φ)
    {World : Type v} [Preorder World]
    (val : World → Atom → Prop)
    (bot_forces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → bot_forces w → bot_forces w')
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → IForces val bot_forces w ψ) :
    IForces val bot_forces w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact min_axiom_sound h_ax World val bot_forces v_uc bf_uc w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact min_soundness d₁ val bot_forces v_uc bf_uc w h_ctx w (le_refl w)
      (min_soundness d₂ val bot_forces v_uc bf_uc w h_ctx)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact min_soundness d' val bot_forces v_uc bf_uc w
      (fun x hx => h_ctx x (h_sub x hx))

/-- Soundness for derivable formulas: if `Derivable MinPropAxiom φ`, then `φ` is
forced at every world of every minimal Kripke model. -/
theorem min_soundness_derivable {φ : PL.Proposition Atom}
    (h : Derivable MinPropAxiom φ) : MValid.{_, v} φ := by
  intro World _ val bot_forces v_uc bf_uc w
  obtain ⟨d⟩ := h
  exact min_soundness d val bot_forces v_uc bf_uc w (fun _ h => nomatch h)

end Cslib.Logic.PL
