/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Separation.Defs
import Mathlib.Data.Set.Finite.Basic

set_option linter.style.emptyLine false

/-!
# Formula Operations for Separation

Provides substitution, DNF/CNF signatures, and freshness infrastructure
needed by the separation proof.

## Key Definitions

- `subst_formula`: Substitute a formula for an atom
- `IntStructure.withAtom`: Modify valuation at a single atom
- `subst_correctness`: Substitution preserves truth under modified valuation
- `fresh_atom`, `fresh_atoms`: Generate fresh atoms not appearing in a formula

## References

- GHR94, Chapter 10.2: Substitution is used in Lemmas 10.2.5-10.2.8
-/

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Substitution -/

/-- Substitute a formula for an atom in a formula.
    Replaces every occurrence of `target` with `replacement`. -/
def subst_formula [DecidableEq Atom]
    (phi : Formula Atom) (target : Atom)
    (replacement : Formula Atom) : Formula Atom :=
  match phi with
  | .atom a =>
    if a = target then replacement else .atom a
  | .bot => .bot
  | .imp psi1 psi2 =>
    .imp (subst_formula psi1 target replacement)
      (subst_formula psi2 target replacement)
  | .box psi =>
    .box (subst_formula psi target replacement)
  | .untl psi1 psi2 =>
    .untl (subst_formula psi1 target replacement)
      (subst_formula psi2 target replacement)
  | .snce psi1 psi2 =>
    .snce (subst_formula psi1 target replacement)
      (subst_formula psi2 target replacement)

/-- Modify an IntStructure's valuation at a single atom. -/
def IntStructure.withAtom [DecidableEq Atom]
    (M : IntStructure Atom) (a : Atom)
    (valSet : Set Int) : IntStructure Atom where
  val b := if b = a then valSet else M.val b

/-- Substitution preserves truth when the atom is interpreted as
    the replacement. -/
theorem subst_correctness [DecidableEq Atom]
    (phi : Formula Atom) (target : Atom)
    (replacement : Formula Atom)
    (M : IntStructure Atom) (t : Int) :
    int_truth M t (subst_formula phi target replacement) ↔
    int_truth
      (M.withAtom target
        {s | int_truth M s replacement}) t phi := by
  induction phi generalizing t with
  | atom a =>
    simp only [subst_formula]
    split
    · next h =>
      subst h
      simp [int_truth, IntStructure.withAtom]
    · next h =>
      simp [int_truth, IntStructure.withAtom, h]
  | bot => exact Iff.rfl
  | imp p q ihp ihq =>
    constructor
    · intro h hp
      exact (ihq t).mp (h ((ihp t).mpr hp))
    · intro h hp
      exact (ihq t).mpr (h ((ihp t).mp hp))
  | box p _ih => exact Iff.rfl
  | untl p q ihp ihq =>
    constructor
    · rintro ⟨s, hts, hp, hq⟩
      exact ⟨s, hts, (ihp s).mp hp,
        fun r hr1 hr2 => (ihq r).mp (hq r hr1 hr2)⟩
    · rintro ⟨s, hts, hp, hq⟩
      exact ⟨s, hts, (ihp s).mpr hp,
        fun r hr1 hr2 => (ihq r).mpr (hq r hr1 hr2)⟩
  | snce p q ihp ihq =>
    constructor
    · rintro ⟨s, hst, hp, hq⟩
      exact ⟨s, hst, (ihp s).mp hp,
        fun r hr1 hr2 => (ihq r).mp (hq r hr1 hr2)⟩
    · rintro ⟨s, hst, hp, hq⟩
      exact ⟨s, hst, (ihp s).mpr hp,
        fun r hr1 hr2 => (ihq r).mpr (hq r hr1 hr2)⟩

/-! ## Normal Form Signatures -/

/-- A literal is either a formula or its negation. -/
inductive Literal (Atom : Type*) where
  | pos (phi : Formula Atom) : Literal Atom
  | neg (phi : Formula Atom) : Literal Atom

/-- Convert a literal to its underlying formula. -/
def Literal.toFormula : Literal Atom -> Formula Atom
  | .pos phi => phi
  | .neg phi => Formula.neg phi

/-- A clause is a list of literals. -/
abbrev Clause (Atom : Type*) := List (Literal Atom)

/-- Convert a conjunctive clause to a formula. -/
def clause_to_conj : Clause Atom -> Formula Atom
  | [] => Formula.neg .bot  -- True
  | [l] => l.toFormula
  | l :: ls => Formula.and l.toFormula (clause_to_conj ls)

/-- Convert a disjunctive clause to a formula. -/
def clause_to_disj : Clause Atom -> Formula Atom
  | [] => .bot
  | [l] => l.toFormula
  | l :: ls =>
    Formula.or l.toFormula (clause_to_disj ls)

/-- Convert a DNF representation to a formula. -/
def from_DNF : List (Clause Atom) -> Formula Atom
  | [] => .bot
  | [c] => clause_to_conj c
  | c :: cs =>
    Formula.or (clause_to_conj c) (from_DNF cs)

/-- Convert a CNF representation to a formula. -/
def from_CNF : List (Clause Atom) -> Formula Atom
  | [] => Formula.neg .bot  -- True
  | [c] => clause_to_disj c
  | c :: cs =>
    Formula.and (clause_to_disj c) (from_CNF cs)

/-- Trivial DNF embedding. -/
def to_DNF (phi : Formula Atom) : List (Clause Atom) :=
  [[Literal.pos phi]]

/-- Trivial CNF embedding. -/
def to_CNF (phi : Formula Atom) : List (Clause Atom) :=
  [[Literal.pos phi]]

/-- DNF conversion preserves integer-time equivalence. -/
theorem dnf_equiv (phi : Formula Atom) :
    int_equiv phi (from_DNF (to_DNF phi)) := by
  -- to_DNF phi = [[Literal.pos phi]]
  change int_equiv phi (from_DNF [[Literal.pos phi]])
  simp only [from_DNF, clause_to_conj,
    Literal.toFormula]
  exact int_equiv_refl phi

/-- CNF conversion preserves integer-time equivalence. -/
theorem cnf_equiv (phi : Formula Atom) :
    int_equiv phi (from_CNF (to_CNF phi)) := by
  -- to_CNF phi = [[Literal.pos phi]]
  change int_equiv phi (from_CNF [[Literal.pos phi]])
  simp only [from_CNF, clause_to_disj,
    Literal.toFormula]
  exact int_equiv_refl phi

/-! ## Freshness Infrastructure -/

/-- For any finset of atoms and natural number n, there exist
    n distinct atoms not in the finset. -/
theorem exists_n_fresh_atoms [DecidableEq Atom] [Infinite Atom]
    (fs : Finset Atom) (n : Nat) :
    ∃ L : List Atom,
      L.length = n ∧ L.Nodup ∧
        ∀ a ∈ L, a ∉ fs := by
  induction n with
  | zero =>
    exact ⟨[], rfl, List.nodup_nil,
      fun _ h => by simp at h⟩
  | succ k ih =>
    obtain ⟨L, hlen, hnodup, hfresh⟩ := ih
    obtain ⟨a, ha⟩ := Finset.exists_notMem
      (fs ∪ L.toFinset)
    simp only [Finset.mem_union, not_or] at ha
    refine ⟨a :: L, by simp [hlen], ?_, ?_⟩
    · exact List.Nodup.cons
        (List.mem_toFinset.not.mp ha.2) hnodup
    · intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ha.1
      · exact hfresh b hb

section FreshnessOps
variable [DecidableEq Atom] [Infinite Atom]

/-- Generate a fresh atom not appearing in a formula. -/
noncomputable def fresh_atom
    (phi : Formula Atom) : Atom :=
  (Finset.exists_notMem phi.atoms).choose

/-- The fresh atom does not appear in the formula. -/
theorem fresh_atom_not_in
    (phi : Formula Atom) :
    fresh_atom phi ∉ phi.atoms :=
  (Finset.exists_notMem phi.atoms).choose_spec

/-- Generate n fresh atoms not appearing in a formula. -/
noncomputable def fresh_atoms
    (phi : Formula Atom) (n : Nat) : List Atom :=
  (exists_n_fresh_atoms phi.atoms n).choose

/-- All atoms in fresh_atoms are distinct from atoms in phi. -/
theorem fresh_atoms_disjoint
    (phi : Formula Atom) (n : Nat) :
    ∀ a ∈ fresh_atoms phi n, a ∉ phi.atoms :=
  (exists_n_fresh_atoms phi.atoms n).choose_spec.2.2

end FreshnessOps

section FreshnessProperties
variable [Infinite Atom]

/-- Fresh atoms are pairwise distinct. -/
theorem fresh_atoms_nodup [DecidableEq Atom]
    (phi : Formula Atom) (n : Nat) :
    (fresh_atoms phi n).Nodup :=
  (exists_n_fresh_atoms phi.atoms n).choose_spec.2.1

/-- The number of fresh atoms equals n. -/
theorem fresh_atoms_length [DecidableEq Atom]
    (phi : Formula Atom) (n : Nat) :
    (fresh_atoms phi n).length = n :=
  (exists_n_fresh_atoms phi.atoms n).choose_spec.1

end FreshnessProperties

/-! ## Multi-Substitution -/

/-- Apply a list of substitutions sequentially. -/
def multi_subst [DecidableEq Atom]
    (phi : Formula Atom)
    (subs : List (Atom × Formula Atom)) :
    Formula Atom :=
  subs.foldl (fun acc ⟨a, f⟩ => subst_formula acc a f)
    phi

/-- Multi-substitution with empty list is identity. -/
theorem multi_subst_nil [DecidableEq Atom]
    (phi : Formula Atom) :
    multi_subst phi [] = phi := rfl

/-- Multi-substitution with single entry is subst_formula. -/
theorem multi_subst_singleton [DecidableEq Atom]
    (phi : Formula Atom) (a : Atom)
    (f : Formula Atom) :
    multi_subst phi [(a, f)] = subst_formula phi a f :=
  rfl

end Cslib.Logic.Bimodal.Metalogic.Separation
