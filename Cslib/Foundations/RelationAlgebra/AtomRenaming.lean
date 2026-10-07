/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Cycles
public import Mathlib.Data.Fintype.Perm

/-!
# Structural enumeration of atom renamings

An identity- and converse-preserving atom permutation independently permutes symmetric atoms
and converse pairs, and may exchange the two atoms in each pair. This characterizes the
renaming group using `j! * k! * 2^k` choices, avoiding enumeration of all functions on atoms.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

variable {j k : ℕ}

/-- The independent choices specifying an identity- and converse-preserving atom permutation. -/
structure AtomPermutation (j k : ℕ) where
  /-- The permutation of the symmetric diversity atoms. -/
  symmetric : Equiv.Perm (Fin j)
  /-- The permutation of the nonsymmetric converse pairs. -/
  pairs : Equiv.Perm (Fin k)
  /-- Whether to exchange the two atoms of a source pair. -/
  flips : Fin k → Bool

namespace AtomPermutation

/-- The structural choices form a product of two permutation types and a Boolean vector. -/
def equivProduct : AtomPermutation j k ≃
    Equiv.Perm (Fin j) × Equiv.Perm (Fin k) × (Fin k → Bool) where
  toFun p := ⟨p.symmetric, p.pairs, p.flips⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (AtomPermutation j k) :=
  letI : Fintype (Equiv.Perm (Fin j)) := fintypePerm
  letI : Fintype (Equiv.Perm (Fin k)) := fintypePerm
  Fintype.ofEquiv _ equivProduct.symm

instance : DecidableEq (AtomPermutation j k) :=
  fun _ _ => decidable_of_iff _ equivProduct.injective.eq_iff

/-- The structural renaming of diversity atoms. -/
def diversity (p : AtomPermutation j k) : DiversityAtom j k → DiversityAtom j k
  | .inl i => .inl (p.symmetric i)
  | .inr (i, b) => .inr (p.pairs i, b ^^ p.flips i)

/-- Extend a structural diversity renaming by fixing identity. -/
def rename (p : AtomPermutation j k) : Atom j k → Atom j k := Option.map p.diversity

/-- Structural diversity renamings are injective. -/
theorem diversity_injective (p : AtomPermutation j k) : Function.Injective p.diversity := by
  rintro (i | ⟨i, b⟩) (l | ⟨l, c⟩) h
  · exact congrArg Sum.inl (p.symmetric.injective (Sum.inl.inj h))
  · contradiction
  · contradiction
  · have h' := Sum.inr.inj h
    have hil : i = l := p.pairs.injective (congrArg Prod.fst h')
    subst l
    have hbc : b = c := by
      have ht := congrArg Prod.snd h'
      cases hb : p.flips i <;> simpa only [hb, Bool.xor_false, Bool.xor_true,
        Bool.not_inj_iff] using ht
    exact congrArg (fun b => Sum.inr (i, b)) hbc

/-- Structural atom renamings satisfy the laws used by classification. -/
theorem laws (p : AtomPermutation j k) :
    Function.Injective p.rename ∧ p.rename none = none ∧
      ∀ x, p.rename x.converse = (p.rename x).converse := by
  refine ⟨Option.map_injective p.diversity_injective, rfl, ?_⟩
  rintro (_ | (i | ⟨i, b⟩))
  · rfl
  · rfl
  · cases b <;> cases h : p.flips i <;>
      simp [rename, diversity, Atom.converse, DiversityAtom.converse, h]

/-- The structural renaming space has the expected factorial size. -/
theorem card : Fintype.card (AtomPermutation j k) = j.factorial * k.factorial * 2 ^ k := by
  rw [Fintype.card_congr (equivProduct (j := j) (k := k))]
  simp [Fintype.card_perm, Nat.mul_assoc]

end AtomPermutation

/-- Every admissible atom map comes from permutations of symmetric atoms and pairs, and flips. -/
theorem exists_atomPermutation (f : Atom j k → Atom j k) (hinj : Function.Injective f)
    (hn : f none = none) (hc : ∀ x, f x.converse = (f x).converse) :
    ∃ p : AtomPermutation j k, f = p.rename := by
  classical
  have hnone (x : DiversityAtom j k) : f (some x) ≠ none := by
    intro h
    have := hinj (h.trans hn.symm)
    simp at this
  have hsym : ∀ i : Fin j, ∃ l : Fin j, f (some (.inl i)) = some (.inl l) := by
    intro i
    cases hfi : f (some (.inl i)) with
    | none => exact False.elim (hnone (.inl i) hfi)
    | some atom =>
      rcases atom with l | ⟨l, b⟩
      · exact ⟨l, rfl⟩
      · have he := hc (some (.inl i))
        change f (some (.inl i)) = (f (some (.inl i))).converse at he
        cases b <;> simp [hfi, Atom.converse, DiversityAtom.converse] at he
  choose sym hsym using hsym
  have hpair : ∀ i : Fin k, ∃ l : Fin k, ∃ b : Bool,
      f (some (.inr (i, false))) = some (.inr (l, b)) := by
    intro i
    cases hfi : f (some (.inr (i, false))) with
    | none => exact False.elim (hnone (.inr (i, false)) hfi)
    | some atom =>
      rcases atom with l | ⟨l, b⟩
      · have he := hc (some (.inr (i, false)))
        change f (some (.inr (i, true))) = (f (some (.inr (i, false)))).converse at he
        have heq : f (some (.inr (i, true))) = f (some (.inr (i, false))) := by
          simpa only [hfi, Atom.converse_some, DiversityAtom.converse] using he
        have := hinj heq
        simp at this
      · exact ⟨l, b, rfl⟩
  choose pairs flips hpair using hpair
  have hpair' (i : Fin k) (b : Bool) :
      f (some (.inr (i, b))) = some (.inr (pairs i, b ^^ flips i)) := by
    cases b
    · simpa only [Bool.false_xor] using hpair i
    · have he := hc (some (.inr (i, false)))
      change f (some (.inr (i, true))) = (f (some (.inr (i, false)))).converse at he
      simpa only [hpair, Atom.converse_some, DiversityAtom.converse, Bool.true_xor] using he
  have hsym_inj : Function.Injective sym := by
    intro i l hil
    have he : f (some (.inl i)) = f (some (.inl l)) := by rw [hsym, hsym, hil]
    simpa only [Option.some.injEq, Sum.inl.injEq] using hinj he
  have hpairs_inj : Function.Injective pairs := by
    intro i l hil
    have he : f (some (.inr (i, flips i))) = f (some (.inr (l, flips l))) := by
      rw [hpair', hpair', hil]
      simp only [Bool.xor_self]
    have heq := hinj he
    exact (Prod.mk.inj (Sum.inr.inj (Option.some.inj heq))).1
  let symmetric : Equiv.Perm (Fin j) :=
    Equiv.ofBijective sym ⟨hsym_inj, Finite.surjective_of_injective hsym_inj⟩
  let pairPermutation : Equiv.Perm (Fin k) :=
    Equiv.ofBijective pairs ⟨hpairs_inj, Finite.surjective_of_injective hpairs_inj⟩
  refine ⟨⟨symmetric, pairPermutation, flips⟩, ?_⟩
  funext x
  rcases x with _ | (i | ⟨i, b⟩)
  · exact hn
  · exact hsym i
  · exact hpair' i b

/-- Checking the smaller structural family suffices to certify all admissible atom renamings. -/
theorem renamings_exhaustive_of_atomPermutations {p : ℕ}
    (renames : Fin p → Atom j k → Atom j k)
    (cover : ∀ permutation : AtomPermutation j k,
      ∃ q, permutation.rename = renames q) :
    ∀ f : Atom j k → Atom j k, Function.Injective f → f none = none →
      (∀ x, f x.converse = (f x).converse) → ∃ q, f = renames q := by
  intro f hinj hn hc
  obtain ⟨permutation, rfl⟩ := exists_atomPermutation f hinj hn hc
  exact cover permutation

end Cslib.RelationAlgebra
