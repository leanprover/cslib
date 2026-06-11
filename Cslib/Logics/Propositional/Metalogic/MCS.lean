/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Metalogic.DeductionTheorem

/-! # Maximal Consistent Sets for Propositional Logic

This module instantiates the generic MCS framework (from `Consistency.lean`)
parameterized over an axiom predicate `Axioms : PL.Proposition Atom -> Prop` and proves
propositional-specific MCS properties needed for completeness results.

## Parameterization Design

- **Generic properties** (lindenbaum, closed_under_derivation, etc.) take `{Axioms}`
  and, where needed, explicit `h_implyK`/`h_implyS` for the deduction theorem.
- **Propositional-specific properties** (`prop_mcs_bot_not_mem`, etc.) are parameterized
  over `{Axioms}` with `h_implyK`/`h_implyS` where the deduction theorem is needed.

## Backward Compatibility

All definitions are parameterized. Classical-specific usage passes `PropositionalAxiom`
and the corresponding constructor proofs.

## References

* Cslib/Logics/Modal/Metalogic/MCS.lean -- modal MCS pattern
* Cslib/Foundations/Logic/Metalogic/Consistency.lean -- generic MCS framework
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

variable {Atom : Type*}

/-! ## Abbreviations for readability -/

/-- Set consistency for a parameterized propositional derivation system. -/
abbrev PropSetConsistent (Axioms : PL.Proposition Atom → Prop)
    (S : Set (PL.Proposition Atom)) : Prop :=
  Metalogic.SetConsistent (propDerivationSystem Axioms) S

/-- Set maximal consistency for a parameterized propositional derivation system. -/
abbrev PropSetMaximalConsistent (Axioms : PL.Proposition Atom → Prop)
    (S : Set (PL.Proposition Atom)) : Prop :=
  Metalogic.SetMaximalConsistent (propDerivationSystem Axioms) S

/-! ## Generic MCS Properties (parameterized) -/

/-- Lindenbaum's lemma for propositional logic: every consistent set extends
to an MCS. -/
theorem prop_lindenbaum {Axioms : PL.Proposition Atom → Prop}
    {S : Set (PL.Proposition Atom)}
    (hS : PropSetConsistent Axioms S) :
    ∃ M : Set (PL.Proposition Atom), S ⊆ M ∧ PropSetMaximalConsistent Axioms M :=
  Metalogic.set_lindenbaum (propDerivationSystem Axioms) hS

/-- Derivable formulas are in MCS. -/
theorem prop_closed_under_derivation
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent Axioms S)
    {L : List (PL.Proposition Atom)} (h_sub : ∀ ψ ∈ L, ψ ∈ S)
    {φ : PL.Proposition Atom}
    (h_deriv : (propDerivationSystem Axioms).Deriv L φ) : φ ∈ S :=
  Metalogic.SetMaximalConsistent.closed_under_derivation
    (propDerivationSystem Axioms)
    (prop_has_deduction_theorem h_implyK h_implyS)
    h_mcs h_sub h_deriv

/-- Implication property: if `φ → ψ ∈ S` and `φ ∈ S`, then `ψ ∈ S`. -/
theorem prop_implication_property
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent Axioms S)
    {φ ψ : PL.Proposition Atom}
    (h_imp : Proposition.imp φ ψ ∈ S) (h_phi : φ ∈ S) : ψ ∈ S :=
  Metalogic.SetMaximalConsistent.implication_property
    (propDerivationSystem Axioms)
    (prop_has_deduction_theorem h_implyK h_implyS)
    h_mcs h_imp h_phi

/-- Negation completeness: for any formula `φ`, either `φ ∈ S` or `¬φ ∈ S`. -/
theorem prop_negation_complete
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent Axioms S)
    (φ : PL.Proposition Atom) : φ ∈ S ∨ Proposition.neg φ ∈ S :=
  Metalogic.SetMaximalConsistent.negation_complete
    (propDerivationSystem Axioms)
    (prop_has_deduction_theorem h_implyK h_implyS)
    h_mcs φ

/-! ## Propositional-Specific MCS Properties -/

/-- `⊥ ∉ S` for any MCS `S`. -/
theorem prop_mcs_bot_not_mem
    {Axioms : PL.Proposition Atom → Prop}
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent Axioms S) :
    Proposition.bot ∉ S := by
  intro h_bot
  exact h_mcs.1 [Proposition.bot]
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h_bot)
    (by simp only [propDerivationSystem, Deriv]
        exact ⟨.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))⟩)

/-- If `φ ∉ S` (MCS), then `¬φ ∈ S`. -/
theorem prop_mcs_neg_of_not_mem
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent Axioms S)
    {φ : PL.Proposition Atom} (h_not : φ ∉ S) : Proposition.neg φ ∈ S := by
  rcases prop_negation_complete h_implyK h_implyS h_mcs φ with h | h
  · exact absurd h h_not
  · exact h

/-- If `¬φ ∈ S` (MCS), then `φ ∉ S`. -/
theorem prop_mcs_not_mem_of_neg
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent Axioms S)
    {φ : PL.Proposition Atom} (h_neg : Proposition.neg φ ∈ S) : φ ∉ S := by
  intro h_phi
  exact prop_mcs_bot_not_mem h_mcs
    (prop_implication_property h_implyK h_implyS h_mcs h_neg h_phi)

/-- `φ ∈ S ↔ ¬φ ∉ S` for MCS `S`. -/
theorem prop_mcs_mem_iff_neg_not_mem
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent Axioms S)
    {φ : PL.Proposition Atom} : φ ∈ S ↔ Proposition.neg φ ∉ S := by
  constructor
  · intro h hn
    exact prop_mcs_bot_not_mem h_mcs
      (prop_implication_property h_implyK h_implyS h_mcs hn h)
  · intro h
    rcases prop_negation_complete h_implyK h_implyS h_mcs φ with h' | h'
    · exact h'
    · exact absurd h' h

end Cslib.Logic.PL
