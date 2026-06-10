/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Separation.Defs
public import Mathlib.Data.Set.Finite.Basic

set_option linter.style.emptyLine false

/-!
# Formula Operations for Separation

Provides substitution, DNF/CNF signatures, and freshness infrastructure
needed by the separation proof.

## Key Definitions

- `substFormula`: Substitute a formula for an atom
- `IntStructure.withAtom`: Modify valuation at a single atom
- `subst_correctness`: Substitution preserves truth under modified valuation
- `freshAtom`, `freshAtoms`: Generate fresh atoms not appearing in a formula

## References

- GHR94, Chapter 10.2: Substitution is used in Lemmas 10.2.5-10.2.8
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Substitution -/

/-- Substitute a formula for an atom in a formula.
    Replaces every occurrence of `target` with `replacement`. -/
def substFormula [DecidableEq Atom]
    (phi : Formula Atom) (target : Atom)
    (replacement : Formula Atom) : Formula Atom :=
  match phi with
  | .atom a =>
    if a = target then replacement else .atom a
  | .bot => .bot
  | .imp psi1 psi2 =>
    .imp (substFormula psi1 target replacement)
      (substFormula psi2 target replacement)
  | .box psi =>
    .box (substFormula psi target replacement)
  | .untl psi1 psi2 =>
    .untl (substFormula psi1 target replacement)
      (substFormula psi2 target replacement)
  | .snce psi1 psi2 =>
    .snce (substFormula psi1 target replacement)
      (substFormula psi2 target replacement)

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
    intTruth M t (substFormula phi target replacement) ↔
    intTruth
      (M.withAtom target
        {s | intTruth M s replacement}) t phi := by
  induction phi generalizing t with
  | atom a =>
    simp only [substFormula]
    split
    · next h =>
      subst h
      simp [intTruth, IntStructure.withAtom]
    · next h =>
      simp [intTruth, IntStructure.withAtom, h]
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
def clauseToConj : Clause Atom -> Formula Atom
  | [] => Formula.neg .bot  -- True
  | [l] => l.toFormula
  | l :: ls => Formula.and l.toFormula (clauseToConj ls)

/-- Convert a disjunctive clause to a formula. -/
def clauseToDisj : Clause Atom -> Formula Atom
  | [] => .bot
  | [l] => l.toFormula
  | l :: ls =>
    Formula.or l.toFormula (clauseToDisj ls)

/-- Convert a DNF representation to a formula. -/
def fromDNF : List (Clause Atom) -> Formula Atom
  | [] => .bot
  | [c] => clauseToConj c
  | c :: cs =>
    Formula.or (clauseToConj c) (fromDNF cs)

/-- Convert a CNF representation to a formula. -/
def fromCNF : List (Clause Atom) -> Formula Atom
  | [] => Formula.neg .bot  -- True
  | [c] => clauseToDisj c
  | c :: cs =>
    Formula.and (clauseToDisj c) (fromCNF cs)

/-- Trivial DNF embedding. -/
def toDNF (phi : Formula Atom) : List (Clause Atom) :=
  [[Literal.pos phi]]

/-- Trivial CNF embedding. -/
def toCNF (phi : Formula Atom) : List (Clause Atom) :=
  [[Literal.pos phi]]

/-- DNF conversion preserves integer-time equivalence. -/
theorem dnf_equiv (phi : Formula Atom) :
    intEquiv phi (fromDNF (toDNF phi)) := by
  -- toDNF phi = [[Literal.pos phi]]
  change intEquiv phi (fromDNF [[Literal.pos phi]])
  simp only [fromDNF, clauseToConj,
    Literal.toFormula]
  exact int_equiv_refl phi

/-- CNF conversion preserves integer-time equivalence. -/
theorem cnf_equiv (phi : Formula Atom) :
    intEquiv phi (fromCNF (toCNF phi)) := by
  -- toCNF phi = [[Literal.pos phi]]
  change intEquiv phi (fromCNF [[Literal.pos phi]])
  simp only [fromCNF, clauseToDisj,
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
noncomputable def freshAtom
    (phi : Formula Atom) : Atom :=
  (Finset.exists_notMem phi.atoms).choose

/-- The fresh atom does not appear in the formula. -/
theorem fresh_atom_not_in
    (phi : Formula Atom) :
    freshAtom phi ∉ phi.atoms :=
  (Finset.exists_notMem phi.atoms).choose_spec

/-- Generate n fresh atoms not appearing in a formula. -/
noncomputable def freshAtoms
    (phi : Formula Atom) (n : Nat) : List Atom :=
  (exists_n_fresh_atoms phi.atoms n).choose

/-- All atoms in freshAtoms are distinct from atoms in phi. -/
theorem fresh_atoms_disjoint
    (phi : Formula Atom) (n : Nat) :
    ∀ a ∈ freshAtoms phi n, a ∉ phi.atoms :=
  (exists_n_fresh_atoms phi.atoms n).choose_spec.2.2

end FreshnessOps

section FreshnessProperties
variable [Infinite Atom]

/-- Fresh atoms are pairwise distinct. -/
theorem fresh_atoms_nodup [DecidableEq Atom]
    (phi : Formula Atom) (n : Nat) :
    (freshAtoms phi n).Nodup :=
  (exists_n_fresh_atoms phi.atoms n).choose_spec.2.1

/-- The number of fresh atoms equals n. -/
theorem fresh_atoms_length [DecidableEq Atom]
    (phi : Formula Atom) (n : Nat) :
    (freshAtoms phi n).length = n :=
  (exists_n_fresh_atoms phi.atoms n).choose_spec.1

end FreshnessProperties

/-! ## Multi-Substitution -/

/-- Apply a list of substitutions sequentially. -/
def multiSubst [DecidableEq Atom]
    (phi : Formula Atom)
    (subs : List (Atom × Formula Atom)) :
    Formula Atom :=
  subs.foldl (fun acc ⟨a, f⟩ => substFormula acc a f)
    phi

/-- Multi-substitution with empty list is identity. -/
theorem multi_subst_nil [DecidableEq Atom]
    (phi : Formula Atom) :
    multiSubst phi [] = phi := rfl

/-- Multi-substitution with single entry is substFormula. -/
theorem multi_subst_singleton [DecidableEq Atom]
    (phi : Formula Atom) (a : Atom)
    (f : Formula Atom) :
    multiSubst phi [(a, f)] = substFormula phi a f :=
  rfl

end Cslib.Logic.Bimodal.Metalogic.Separation
