/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Kripke
public import Cslib.Logics.Propositional.ProofSystem.Derivation
public import Cslib.Logics.Propositional.ProofSystem.Axioms

/-! # Soundness Theorem for Intuitionistic Propositional Logic

This module proves soundness for intuitionistic propositional logic (IntPropAxiom):
every derivable formula is intuitionistically valid (IValid).

## Main Results

- `int_axiom_sound`: Each of the 3 axiom schemata (implyK, implyS, efq) is IValid.
- `int_soundness`: If `DerivationTree IntPropAxiom Γ φ`, then `φ` is forced at every
  world of every Kripke model where all of `Γ` is forced.
- `int_soundness_derivable`: If `Derivable IntPropAxiom φ`, then `IValid φ`.

## References

* [A. Chagrov, M. Zakharyaschev,
  *Modal Logic*][ChagrovZakharyaschev1997],
  Theorem 2.43 (soundness direction),
  Proposition 2.1 (persistence lemma)
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## Axiom Soundness -/

/-- Every axiom of intuitionistic propositional logic is IValid.

The 3 cases are:
- **implyK**: `φ → (ψ → φ)` -- uses persistence to carry `φ` to successor worlds.
- **implyS**: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -- uses transitivity of ≤.
- **efq**: `⊥ → φ` -- `IForces w ⊥ = bot_forces w`, which is `False` for intuitionistic
  semantics, so the premise is vacuously false. -/
theorem int_axiom_sound {φ : PL.Proposition Atom}
    (h_ax : IntPropAxiom φ) : IValid.{_, v} φ := by
  intro World _ val v_uc w
  cases h_ax with
  | implyK φ ψ =>
    -- Goal: IForces val bf w (φ → (ψ → φ))
    -- = ∀ w' ≥ w, IForces w' φ → ∀ w'' ≥ w', IForces w'' ψ → IForces w'' φ
    intro w' _ hφ w'' hw' _
    exact iforces_persistence v_uc (fun {_ _} _ h => absurd h id) hw' hφ
  | implyS φ ψ χ =>
    -- Goal: IForces val bf w ((φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)))
    intro w₁ hw₁ h_pqr w₂ hw₂ h_pq w₃ hw₃ h_p
    have h₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pqr w₃ h₁₃ h_p w₃ (le_refl w₃) (h_pq w₃ hw₃ h_p)
  | efq φ =>
    -- Goal: IForces val bf w (⊥ → φ) = ∀ w' ≥ w, False → IForces w' φ
    intro _ _ hbot
    exact absurd hbot id

/-! ## Soundness Theorem -/

/-- **Soundness**: If `DerivationTree IntPropAxiom Γ φ`, then for any Kripke model
(with `bot_forces = fun _ => False`) and world `w` where all formulas in `Γ` are
forced, `φ` is also forced at `w`. -/
theorem int_soundness
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree IntPropAxiom Γ φ)
    {World : Type v} [Preorder World]
    (val : World → Atom → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → IForces val (fun _ => False) w ψ) :
    IForces val (fun _ => False) w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact int_axiom_sound h_ax World val v_uc w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    -- d₁ : Γ ⊢ ψ → χ, d₂ : Γ ⊢ ψ
    -- By IH: IForces w (ψ → χ) and IForces w ψ
    -- IForces w (ψ → χ) = ∀ w' ≥ w, IForces w' ψ → IForces w' χ
    -- Apply at w' = w with le_refl
    exact int_soundness d₁ val v_uc w h_ctx w (le_refl w)
      (int_soundness d₂ val v_uc w h_ctx)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact int_soundness d' val v_uc w
      (fun x hx => h_ctx x (h_sub x hx))

/-- Soundness for derivable formulas: if `Derivable IntPropAxiom φ`, then `φ` is
forced at every world of every intuitionistic Kripke model. -/
theorem int_soundness_derivable {φ : PL.Proposition Atom}
    (h : Derivable IntPropAxiom φ) : IValid.{_, v} φ := by
  intro World _ val v_uc w
  obtain ⟨d⟩ := h
  exact int_soundness d val v_uc w (fun _ h => nomatch h)

end Cslib.Logic.PL
