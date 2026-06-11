/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Basic
public import Cslib.Logics.Propositional.ProofSystem.Derivation

/-! # Soundness Theorem for Classical Propositional Logic

This module proves soundness for classical propositional logic (HilbertCl):
every derivable formula is a tautology.

## Main Results

- `prop_axiom_sound`: Each of the 4 axiom schemata is valid under all valuations.
- `prop_soundness`: If `Γ ⊢ φ` (via `DerivationTree PropositionalAxiom`), then `φ`
  is true under any valuation where all of `Γ` is true.
- `prop_soundness_derivable`: If `⊢ φ`, then `φ` is true under all valuations.
- `soundness_tautology`: If `⊢ φ`, then `φ` is a tautology.

## References

* CZ Theorem 1.16 (soundness direction)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- modal soundness pattern
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## Axiom Soundness -/

/-- Every axiom of classical propositional logic is valid under all valuations. -/
theorem prop_axiom_sound {φ : PL.Proposition Atom}
    (h_ax : PropositionalAxiom φ) (v : Valuation Atom) :
    Evaluate v φ := by
  cases h_ax with
  | implyK φ ψ => intro h_phi _; exact h_phi
  | implyS φ ψ χ => intro h1 h2 h3; exact h1 h3 (h2 h3)
  | efq φ => intro h; exact absurd h id
  | peirce φ ψ =>
    intro h; by_contra h_not
    exact h_not (h (fun h_phi => absurd h_phi h_not))

/-! ## Soundness Theorem -/

/-- **Soundness**: If `Γ ⊢ φ` (via `DerivationTree PropositionalAxiom`), then
for any valuation `v` where all formulas in `Γ` evaluate to true, `φ` also
evaluates to true. -/
theorem prop_soundness
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree PropositionalAxiom Γ φ)
    (v : Valuation Atom)
    (h_ctx : ∀ ψ, ψ ∈ Γ → Evaluate v ψ) :
    Evaluate v φ := by
  match d with
  | .ax _ ψ h_ax => exact prop_axiom_sound h_ax v
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact prop_soundness d₁ v h_ctx
      (prop_soundness d₂ v h_ctx)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact prop_soundness d' v
      (fun x hx => h_ctx x (h_sub x hx))

/-- Soundness for derivable formulas: if `⊢ φ`, then `φ` is true
under all valuations. -/
theorem prop_soundness_derivable {φ : PL.Proposition Atom}
    (h : Derivable PropositionalAxiom φ) (v : Valuation Atom) :
    Evaluate v φ := by
  obtain ⟨d⟩ := h
  exact prop_soundness d v (fun _ h => nomatch h)

/-- Soundness at the tautology level: every derivable formula is a
tautology. -/
theorem soundness_tautology {φ : PL.Proposition Atom}
    (h : Derivable PropositionalAxiom φ) : Tautology φ :=
  fun v => prop_soundness_derivable h v

end Cslib.Logic.PL
