/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Syntax.Formula
import Cslib.Logics.Bimodal.Syntax.Subformulas
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Basic

/-!
# Core Subformula Closure: Finset-Based Closure, Negation Closure, and Membership Lemmas

Core subformula closure as Finset, closureWithNeg, and subformula membership lemmas.
-/

namespace Cslib.Logic.Bimodal

open Cslib.Logic.Bimodal.Formula

variable {Atom : Type*} [DecidableEq Atom]

/-!
## Subformula Closure as Finset

Convert the List-based subformulas to a Finset for finite set operations.
-/

/--
Subformula closure of a formula as a Finset.

This converts the List-based `Formula.subformulas` to a Finset,
enabling finite set operations and cardinality reasoning.
-/
def subformulaClosure (phi : Formula Atom) : Finset (Formula Atom) :=
  (Formula.subformulas phi).toFinset

/--
The formula itself is in its subformula closure.
-/
theorem self_mem_subformulaClosure (phi : Formula Atom) : phi ∈ subformulaClosure phi := by
  unfold subformulaClosure
  simp only [List.mem_toFinset]
  exact Formula.self_mem_subformulas phi

/--
Membership in subformula closure is decidable.
-/
instance (phi : Formula Atom) : DecidablePred (· ∈ subformulaClosure phi) :=
  fun psi => Finset.decidableMem psi (subformulaClosure phi)

/--
Size of the subformula closure (useful for termination measures).
-/
def subformulaClosureCard (phi : Formula Atom) : Nat := (subformulaClosure phi).card

/-!
## Closure with Negations

For negation completeness in MCS, we extend closure with negations.
-/

/--
Closure extended with negations of all members.

For each formula psi in the subformula closure, we include both psi
and its negation. This ensures closure-restricted MCS can have
negation completeness.
-/
def closureWithNeg (phi : Formula Atom) : Finset (Formula Atom) :=
  (subformulaClosure phi) ∪ (subformulaClosure phi).image Formula.neg

/--
Subformula closure is a subset of closureWithNeg.
-/
theorem subformulaClosure_subset_closureWithNeg (phi : Formula Atom) :
    subformulaClosure phi ⊆ closureWithNeg phi := by
  intro psi h
  unfold closureWithNeg
  exact Finset.mem_union_left _ h

/--
Negation of a closure member is in closureWithNeg.
-/
theorem neg_mem_closureWithNeg (phi psi : Formula Atom)
    (h : psi ∈ subformulaClosure phi) :
    psi.neg ∈ closureWithNeg phi := by
  unfold closureWithNeg
  apply Finset.mem_union_right
  exact Finset.mem_image_of_mem Formula.neg h

/--
The formula itself is in closureWithNeg.
-/
theorem self_mem_closureWithNeg (phi : Formula Atom) : phi ∈ closureWithNeg phi :=
  subformulaClosure_subset_closureWithNeg phi (self_mem_subformulaClosure phi)

/--
The negation of the formula is in closureWithNeg.
-/
theorem neg_self_mem_closureWithNeg (phi : Formula Atom) :
    phi.neg ∈ closureWithNeg phi :=
  neg_mem_closureWithNeg phi phi (self_mem_subformulaClosure phi)

/--
Membership in closureWithNeg is decidable.
-/
instance (phi : Formula Atom) : DecidablePred (· ∈ closureWithNeg phi) :=
  fun psi => Finset.decidableMem psi (closureWithNeg phi)

/--
Size of the closure with negations (useful for termination measures).
-/
def closureWithNegCard (phi : Formula Atom) : Nat := (closureWithNeg phi).card

/-!
## Subformula Membership Lemmas

These lemmas enable reasoning about when subformulas are in the closure.
-/

/--
Left component of implication is in closure.
-/
theorem closure_imp_left (phi psi chi : Formula Atom)
    (h : Formula.imp psi chi ∈ subformulaClosure phi) :
    psi ∈ subformulaClosure phi := by
  unfold subformulaClosure at h ⊢
  simp only [List.mem_toFinset] at h ⊢
  exact Formula.mem_subformulas_of_imp_left h

/--
Right component of implication is in closure.
-/
theorem closure_imp_right (phi psi chi : Formula Atom)
    (h : Formula.imp psi chi ∈ subformulaClosure phi) :
    chi ∈ subformulaClosure phi := by
  unfold subformulaClosure at h ⊢
  simp only [List.mem_toFinset] at h ⊢
  exact Formula.mem_subformulas_of_imp_right h

/--
Inner formula of Box is in closure.
-/
theorem closure_box (phi psi : Formula Atom)
    (h : Formula.box psi ∈ subformulaClosure phi) :
    psi ∈ subformulaClosure phi := by
  unfold subformulaClosure at h ⊢
  simp only [List.mem_toFinset] at h ⊢
  exact Formula.mem_subformulas_of_box h

/--
Inner formula of all_past is in closure.
-/
theorem closure_all_past (phi psi : Formula Atom)
    (h : Formula.all_past psi ∈ subformulaClosure phi) :
    psi ∈ subformulaClosure phi := by
  unfold subformulaClosure at h ⊢
  simp only [List.mem_toFinset] at h ⊢
  exact Formula.mem_subformulas_of_all_past h

/--
Inner formula of all_future is in closure.
-/
theorem closure_all_future (phi psi : Formula Atom)
    (h : Formula.all_future psi ∈ subformulaClosure phi) :
    psi ∈ subformulaClosure phi := by
  unfold subformulaClosure at h ⊢
  simp only [List.mem_toFinset] at h ⊢
  exact Formula.mem_subformulas_of_all_future h

/--
Left component of Until is in closure.
-/
theorem closure_untl_left (phi psi chi : Formula Atom)
    (h : Formula.untl psi chi ∈ subformulaClosure phi) :
    psi ∈ subformulaClosure phi := by
  unfold subformulaClosure at h ⊢
  simp only [List.mem_toFinset] at h ⊢
  exact Formula.mem_subformulas_of_untl_left h

/--
Right component of Until is in closure.
-/
theorem closure_untl_right (phi psi chi : Formula Atom)
    (h : Formula.untl psi chi ∈ subformulaClosure phi) :
    chi ∈ subformulaClosure phi := by
  unfold subformulaClosure at h ⊢
  simp only [List.mem_toFinset] at h ⊢
  exact Formula.mem_subformulas_of_untl_right h

/--
Left component of Since is in closure.
-/
theorem closure_snce_left (phi psi chi : Formula Atom)
    (h : Formula.snce psi chi ∈ subformulaClosure phi) :
    psi ∈ subformulaClosure phi := by
  unfold subformulaClosure at h ⊢
  simp only [List.mem_toFinset] at h ⊢
  exact Formula.mem_subformulas_of_snce_left h

/--
Right component of Since is in closure.
-/
theorem closure_snce_right (phi psi chi : Formula Atom)
    (h : Formula.snce psi chi ∈ subformulaClosure phi) :
    chi ∈ subformulaClosure phi := by
  unfold subformulaClosure at h ⊢
  simp only [List.mem_toFinset] at h ⊢
  exact Formula.mem_subformulas_of_snce_right h

/--
If P(chi) is in closureWithNeg phi, then chi is in subformulaClosure phi.

P(chi) = neg(H(neg chi)) = (H(neg chi)).imp bot.
If P(chi) is in subformulaClosure, we extract chi via closure_snce_left.
If P(chi) = psi.neg for psi in subformulaClosure, constructor mismatch (snce vs imp).
-/
theorem some_past_in_closureWithNeg_inner_in_subformulaClosure (phi chi : Formula Atom)
    (h : Formula.some_past chi ∈ closureWithNeg phi) :
    chi ∈ subformulaClosure phi := by
  unfold closureWithNeg at h
  simp only [Finset.mem_union, Finset.mem_image] at h
  rcases h with h_sub | ⟨psi, _, h_psi_neg_eq⟩
  · exact closure_snce_left phi _ _ h_sub
  · unfold Formula.some_past Formula.top at h_psi_neg_eq
    exact absurd h_psi_neg_eq (by intro h; cases h)

/--
If F(chi) is in closureWithNeg phi, then chi is in subformulaClosure phi.

Symmetric to some_past_in_closureWithNeg_inner_in_subformulaClosure.
F(chi) = neg(G(neg chi)) = (G(neg chi)).imp bot.
-/
theorem some_future_in_closureWithNeg_inner_in_subformulaClosure (phi chi : Formula Atom)
    (h : Formula.some_future chi ∈ closureWithNeg phi) :
    chi ∈ subformulaClosure phi := by
  unfold closureWithNeg at h
  simp only [Finset.mem_union, Finset.mem_image] at h
  rcases h with h_sub | ⟨psi, _, h_psi_neg_eq⟩
  · exact closure_untl_left phi _ _ h_sub
  · unfold Formula.some_future Formula.top at h_psi_neg_eq
    exact absurd h_psi_neg_eq (by intro h; cases h)

end Cslib.Logic.Bimodal
