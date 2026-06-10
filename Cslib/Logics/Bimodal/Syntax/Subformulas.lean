/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Syntax.Formula
import Mathlib.Data.List.Basic

/-!
# Subformula Definitions for Bimodal Logic

This module provides the subformula closure for bimodal formulas.
These definitions are used in the finite model property proof and
decidability procedures.

## Main Definitions

- `Formula.subformulas`: Collect all subformulas of a formula (including itself)
- `Formula.subformulaCount`: Count of distinct subformulas

## Main Results

- `Formula.self_mem_subformulas`: A formula is in its own subformula list
- `Formula.subformulas_trans`: Subformula relation is transitive
- Membership lemmas for each constructor
-/

namespace Cslib.Logic.Bimodal

namespace Formula

variable {Atom : Type*}

/--
Collect all subformulas of a formula (including the formula itself).

This is used to bound the size of finite models and tableaux.
The subformula property ensures that expansion only produces
formulas from the subformula closure.
-/
def subformulas : Formula Atom → List (Formula Atom)
  | φ@(.atom _) => [φ]
  | φ@.bot => [φ]
  | φ@(.imp ψ χ) => φ :: (subformulas ψ ++ subformulas χ)
  | φ@(.box ψ) => φ :: subformulas ψ
  | φ@(.untl ψ χ) => φ :: (subformulas ψ ++ subformulas χ)
  | φ@(.snce ψ χ) => φ :: (subformulas ψ ++ subformulas χ)

/-- Count of distinct subformulas (used for termination). -/
def subformulaCount [DecidableEq (Formula Atom)] (φ : Formula Atom) : Nat :=
  (subformulas φ).eraseDups.length

/-- Subformulas include the formula itself. -/
theorem self_mem_subformulas (φ : Formula Atom) : φ ∈ subformulas φ := by
  cases φ <;> simp [subformulas]

/-- Subformulas of imp include the left component. -/
theorem imp_left_mem_subformulas (ψ χ : Formula Atom) : ψ ∈ subformulas (.imp ψ χ) := by
  simp only [subformulas, List.mem_cons, List.mem_append]
  right
  left
  exact self_mem_subformulas ψ

/-- Subformulas of imp include the right component. -/
theorem imp_right_mem_subformulas (ψ χ : Formula Atom) : χ ∈ subformulas (.imp ψ χ) := by
  simp only [subformulas, List.mem_cons, List.mem_append]
  right
  right
  exact self_mem_subformulas χ

/-- Subformulas of box include the inner formula. -/
theorem box_inner_mem_subformulas (ψ : Formula Atom) : ψ ∈ subformulas (.box ψ) := by
  simp only [subformulas, List.mem_cons]
  right
  exact self_mem_subformulas ψ

/-- Subformulas of allPast include the inner formula. -/
theorem allPast_inner_mem_subformulas (ψ : Formula Atom) :
    ψ ∈ subformulas (allPast ψ) := by
  simp only [somePast, neg, top, subformulas, List.mem_cons, List.mem_append]
  right; left; right; left; right; left
  exact self_mem_subformulas ψ

/-- Subformulas of allFuture include the inner formula. -/
theorem allFuture_inner_mem_subformulas (ψ : Formula Atom) :
    ψ ∈ subformulas (allFuture ψ) := by
  simp only [someFuture, neg, top, subformulas, List.mem_cons, List.mem_append]
  right; left; right; left; right; left
  exact self_mem_subformulas ψ

/--
Transitivity of the subformula relation.

If chi is a subformula of psi, and psi is a subformula of phi,
then chi is a subformula of phi.
-/
theorem subformulas_trans {chi psi phi : Formula Atom}
    (h1 : chi ∈ subformulas psi) (h2 : psi ∈ subformulas phi) :
    chi ∈ subformulas phi := by
  induction phi with
  | atom p =>
    simp only [subformulas, List.mem_singleton] at h2
    subst h2
    exact h1
  | bot =>
    simp only [subformulas, List.mem_singleton] at h2
    subst h2
    exact h1
  | imp a b iha ihb =>
    simp only [subformulas, List.mem_cons, List.mem_append] at h2
    rcases h2 with rfl | ha | hb
    · exact h1
    · simp only [subformulas, List.mem_cons, List.mem_append]
      right; left
      exact iha ha
    · simp only [subformulas, List.mem_cons, List.mem_append]
      right; right
      exact ihb hb
  | box a iha =>
    simp only [subformulas, List.mem_cons] at h2
    rcases h2 with rfl | h2
    · exact h1
    · simp only [subformulas, List.mem_cons]
      right
      exact iha h2
  | untl a b iha ihb =>
    simp only [subformulas, List.mem_cons, List.mem_append] at h2
    rcases h2 with rfl | ha | hb
    · exact h1
    · simp only [subformulas, List.mem_cons, List.mem_append]
      right; left
      exact iha ha
    · simp only [subformulas, List.mem_cons, List.mem_append]
      right; right
      exact ihb hb
  | snce a b iha ihb =>
    simp only [subformulas, List.mem_cons, List.mem_append] at h2
    rcases h2 with rfl | ha | hb
    · exact h1
    · simp only [subformulas, List.mem_cons, List.mem_append]
      right; left
      exact iha ha
    · simp only [subformulas, List.mem_cons, List.mem_append]
      right; right
      exact ihb hb

/--
Direct membership: left side of implication is in subformulas of the implication.
This is the key lemma for closure_imp_left.
-/
theorem mem_subformulas_of_imp_left {ψ χ phi : Formula Atom}
    (h : Formula.imp ψ χ ∈ subformulas phi) : ψ ∈ subformulas phi := by
  have h_left : ψ ∈ subformulas (Formula.imp ψ χ) := imp_left_mem_subformulas ψ χ
  exact subformulas_trans h_left h

/--
Direct membership: right side of implication is in subformulas of the implication.
This is the key lemma for closure_imp_right.
-/
theorem mem_subformulas_of_imp_right {ψ χ phi : Formula Atom}
    (h : Formula.imp ψ χ ∈ subformulas phi) : χ ∈ subformulas phi := by
  have h_right : χ ∈ subformulas (Formula.imp ψ χ) := imp_right_mem_subformulas ψ χ
  exact subformulas_trans h_right h

/--
Direct membership: inner formula of box is in subformulas.
-/
theorem mem_subformulas_of_box {ψ phi : Formula Atom}
    (h : Formula.box ψ ∈ subformulas phi) : ψ ∈ subformulas phi := by
  have h_inner : ψ ∈ subformulas (Formula.box ψ) := box_inner_mem_subformulas ψ
  exact subformulas_trans h_inner h

/--
Direct membership: inner formula of allPast is in subformulas.
-/
theorem mem_subformulas_of_allPast {ψ phi : Formula Atom}
    (h : (allPast ψ) ∈ subformulas phi) : ψ ∈ subformulas phi := by
  have h_inner : ψ ∈ subformulas (allPast ψ) := allPast_inner_mem_subformulas ψ
  exact subformulas_trans h_inner h

/--
Direct membership: inner formula of allFuture is in subformulas.
-/
theorem mem_subformulas_of_allFuture {ψ phi : Formula Atom}
    (h : (allFuture ψ) ∈ subformulas phi) : ψ ∈ subformulas phi := by
  have h_inner : ψ ∈ subformulas (allFuture ψ) := allFuture_inner_mem_subformulas ψ
  exact subformulas_trans h_inner h

/-- Subformulas of untl include the left component. -/
theorem untl_left_mem_subformulas (ψ χ : Formula Atom) : ψ ∈ subformulas (.untl ψ χ) := by
  simp only [subformulas, List.mem_cons, List.mem_append]
  right; left
  exact self_mem_subformulas ψ

/-- Subformulas of untl include the right component. -/
theorem untl_right_mem_subformulas (ψ χ : Formula Atom) : χ ∈ subformulas (.untl ψ χ) := by
  simp only [subformulas, List.mem_cons, List.mem_append]
  right; right
  exact self_mem_subformulas χ

/-- Subformulas of snce include the left component. -/
theorem snce_left_mem_subformulas (ψ χ : Formula Atom) : ψ ∈ subformulas (.snce ψ χ) := by
  simp only [subformulas, List.mem_cons, List.mem_append]
  right; left
  exact self_mem_subformulas ψ

/-- Subformulas of snce include the right component. -/
theorem snce_right_mem_subformulas (ψ χ : Formula Atom) : χ ∈ subformulas (.snce ψ χ) := by
  simp only [subformulas, List.mem_cons, List.mem_append]
  right; right
  exact self_mem_subformulas χ

/-- Direct membership: left of untl is in subformulas. -/
theorem mem_subformulas_of_untl_left {ψ χ phi : Formula Atom}
    (h : Formula.untl ψ χ ∈ subformulas phi) : ψ ∈ subformulas phi := by
  exact subformulas_trans (untl_left_mem_subformulas ψ χ) h

/-- Direct membership: right of untl is in subformulas. -/
theorem mem_subformulas_of_untl_right {ψ χ phi : Formula Atom}
    (h : Formula.untl ψ χ ∈ subformulas phi) : χ ∈ subformulas phi := by
  exact subformulas_trans (untl_right_mem_subformulas ψ χ) h

/-- Direct membership: left of snce is in subformulas. -/
theorem mem_subformulas_of_snce_left {ψ χ phi : Formula Atom}
    (h : Formula.snce ψ χ ∈ subformulas phi) : ψ ∈ subformulas phi := by
  exact subformulas_trans (snce_left_mem_subformulas ψ χ) h

/-- Direct membership: right of snce is in subformulas. -/
theorem mem_subformulas_of_snce_right {ψ χ phi : Formula Atom}
    (h : Formula.snce ψ χ ∈ subformulas phi) : χ ∈ subformulas phi := by
  exact subformulas_trans (snce_right_mem_subformulas ψ χ) h

end Formula

end Cslib.Logic.Bimodal
