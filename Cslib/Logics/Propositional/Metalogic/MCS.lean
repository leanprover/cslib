/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Metalogic.DeductionTheorem

/-! # Maximal Consistent Sets for Propositional Logic

This module instantiates the generic MCS framework (from `Consistency.lean`) for
propositional logic and proves propositional-specific MCS properties needed for
completeness results.

## Main Results

### Generic MCS properties (instantiated from Consistency.lean)
- `prop_lindenbaum`: Every consistent set extends to a maximally consistent set.
- `prop_closed_under_derivation`: Derivable formulas are in MCS.
- `prop_implication_property`: Modus ponens reflected in membership.
- `prop_negation_complete`: Either `φ` or `¬φ` is in every MCS.

### Propositional-specific properties
- `prop_mcs_bot_not_mem`: `⊥ ∉ S` for any MCS `S`.
- `prop_mcs_neg_of_not_mem`: If `φ ∉ S`, then `¬φ ∈ S`.
- `prop_mcs_not_mem_of_neg`: If `¬φ ∈ S`, then `φ ∉ S`.
- `prop_mcs_mem_iff_neg_not_mem`: `φ ∈ S ↔ ¬φ ∉ S`.

## References

* Cslib/Logics/Modal/Metalogic/MCS.lean -- modal MCS pattern
* Cslib/Foundations/Logic/Metalogic/Consistency.lean -- generic MCS framework
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

variable {Atom : Type*}

/-! ## Abbreviations for readability -/

/-- Set consistency for the classical propositional derivation system. -/
abbrev PropSetConsistent (S : Set (PL.Proposition Atom)) : Prop :=
  Metalogic.SetConsistent (propDerivationSystem PropositionalAxiom) S

/-- Set maximal consistency for the classical propositional derivation system. -/
abbrev PropSetMaximalConsistent (S : Set (PL.Proposition Atom)) : Prop :=
  Metalogic.SetMaximalConsistent (propDerivationSystem PropositionalAxiom) S

/-! ## Generic MCS Properties (instantiated) -/

/-- Lindenbaum's lemma for propositional logic: every consistent set extends
to an MCS. -/
theorem prop_lindenbaum {S : Set (PL.Proposition Atom)}
    (hS : PropSetConsistent S) :
    ∃ M : Set (PL.Proposition Atom), S ⊆ M ∧ PropSetMaximalConsistent M :=
  Metalogic.set_lindenbaum (propDerivationSystem PropositionalAxiom) hS

/-- Derivable formulas are in MCS. -/
theorem prop_closed_under_derivation
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent S)
    {L : List (PL.Proposition Atom)} (h_sub : ∀ ψ ∈ L, ψ ∈ S)
    {φ : PL.Proposition Atom}
    (h_deriv : (propDerivationSystem PropositionalAxiom).Deriv L φ) : φ ∈ S :=
  Metalogic.SetMaximalConsistent.closed_under_derivation
    (propDerivationSystem PropositionalAxiom) cl_prop_has_deduction_theorem
    h_mcs h_sub h_deriv

/-- Implication property: if `φ → ψ ∈ S` and `φ ∈ S`, then `ψ ∈ S`. -/
theorem prop_implication_property
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent S)
    {φ ψ : PL.Proposition Atom}
    (h_imp : Proposition.imp φ ψ ∈ S) (h_phi : φ ∈ S) : ψ ∈ S :=
  Metalogic.SetMaximalConsistent.implication_property
    (propDerivationSystem PropositionalAxiom) cl_prop_has_deduction_theorem
    h_mcs h_imp h_phi

/-- Negation completeness: for any formula `φ`, either `φ ∈ S` or `¬φ ∈ S`. -/
theorem prop_negation_complete
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent S)
    (φ : PL.Proposition Atom) : φ ∈ S ∨ Proposition.neg φ ∈ S :=
  Metalogic.SetMaximalConsistent.negation_complete
    (propDerivationSystem PropositionalAxiom) cl_prop_has_deduction_theorem
    h_mcs φ

/-! ## Propositional-Specific MCS Properties -/

/-- `⊥ ∉ S` for any MCS `S`. -/
theorem prop_mcs_bot_not_mem
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent S) :
    Proposition.bot ∉ S := by
  intro h_bot
  exact h_mcs.1 [Proposition.bot]
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h_bot)
    (by simp only [propDerivationSystem, Deriv]
        exact ⟨.assumption _ _
          (List.mem_cons.mpr (Or.inl rfl))⟩)

/-- If `φ ∉ S` (MCS), then `¬φ ∈ S`. -/
theorem prop_mcs_neg_of_not_mem
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent S)
    {φ : PL.Proposition Atom} (h_not : φ ∉ S) : Proposition.neg φ ∈ S := by
  rcases prop_negation_complete h_mcs φ with h | h
  · exact absurd h h_not
  · exact h

/-- If `¬φ ∈ S` (MCS), then `φ ∉ S`. -/
theorem prop_mcs_not_mem_of_neg
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent S)
    {φ : PL.Proposition Atom} (h_neg : Proposition.neg φ ∈ S) : φ ∉ S := by
  intro h_phi
  exact prop_mcs_bot_not_mem h_mcs
    (prop_implication_property h_mcs h_neg h_phi)

/-- `φ ∈ S ↔ ¬φ ∉ S` for MCS `S`. -/
theorem prop_mcs_mem_iff_neg_not_mem
    {S : Set (PL.Proposition Atom)} (h_mcs : PropSetMaximalConsistent S)
    {φ : PL.Proposition Atom} : φ ∈ S ↔ Proposition.neg φ ∉ S := by
  constructor
  · intro h hn
    exact prop_mcs_bot_not_mem h_mcs
      (prop_implication_property h_mcs hn h)
  · intro h
    rcases prop_negation_complete h_mcs φ with h' | h'
    · exact h'
    · exact absurd h' h

end Cslib.Logic.PL
