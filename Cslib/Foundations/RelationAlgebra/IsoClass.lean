/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure

/-!
# Isomorphism classes of finite relation algebras

`IsoClass.ofAtoms k` counts each isomorphism type of relation algebras with `k` Boolean atoms
once. Representatives are lawful atom structures on `Fin k`. Their identity can be any set of
atoms allowed by the relation algebra axioms.

The unlabelled enumeration in [James Koussas, *Finite Relation Algebras*,
Corollary 24](https://arxiv.org/pdf/2202.01959#page=9) gives the same asymptotic formula for
the integral and unrestricted counts.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

namespace AtomStructure

instance {α : Type*} [Finite α] : Finite (AtomStructure α) :=
  Finite.of_injective (fun A => (A.conv, A.id, A.cycles)) fun _ _ h =>
    AtomStructure.ext congr(Prod.fst $h) congr(Prod.fst (Prod.snd $h)) congr(Prod.snd (Prod.snd $h))

instance {α : Type*} (A : {A : AtomStructure α // LawfulAtomStructure A}) :
    LawfulAtomStructure A.val := A.property

/-- Atom structures are identified when their complex algebras are isomorphic. -/
instance setoid (α : Type*) : Setoid {A : AtomStructure α // LawfulAtomStructure A} where
  r A B := Nonempty (RelationAlgebraEquiv (ComplexAlgebra A.val) (ComplexAlgebra B.val))
  iseqv := ⟨fun _ => ⟨.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

end AtomStructure

namespace IsoClass

/-- The isomorphism classes of finite relation algebras with exactly `k` atoms. -/
abbrev ofAtoms (k : ℕ) := Quotient (AtomStructure.setoid (Fin k))

/-- Represent a finite relation algebra by labelling its atoms. -/
noncomputable def ofAlgebra {A : Type*} [RelationAlgebra A] [Finite A] {k : ℕ}
    (h : Nat.card {a : A // IsAtom a} = k) : ofAtoms k :=
  letI := CompleteAtomicRelationAlgebra.ofFinite A
  ⟦⟨(atomStructure A).map (Finite.equivFinOfCardEq h), inferInstance⟩⟧

private noncomputable def labelledEquiv {A : Type*} [RelationAlgebra A] [Finite A] {k : ℕ}
    (h : Nat.card {a : A // IsAtom a} = k) :
    letI := CompleteAtomicRelationAlgebra.ofFinite A
    RelationAlgebraEquiv A (ComplexAlgebra ((atomStructure A).map (Finite.equivFinOfCardEq h))) :=
  letI := CompleteAtomicRelationAlgebra.ofFinite A
  complexAlgebraEquiv.trans (ComplexAlgebra.mapEquiv _ _)

theorem ofAlgebra_eq_iff {A B : Type*} [RelationAlgebra A] [Finite A] [RelationAlgebra B]
    [Finite B] {k : ℕ} (hA : Nat.card {a : A // IsAtom a} = k)
    (hB : Nat.card {b : B // IsAtom b} = k) :
    ofAlgebra hA = ofAlgebra hB ↔ Nonempty (RelationAlgebraEquiv A B) := by
  refine Quotient.eq.trans ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_⟩
  · exact ⟨(labelledEquiv hA).trans (e.trans (labelledEquiv hB).symm)⟩
  · exact ⟨(labelledEquiv hA).symm.trans (e.trans (labelledEquiv hB))⟩

/-- Integrality is invariant under a change of representative. -/
def IsIntegral {k : ℕ} (q : ofAtoms k) : Prop :=
  Quotient.liftOn q (fun A => RelationAlgebra.IsIntegral (ComplexAlgebra A.val)) fun _ _ ⟨e⟩ =>
    propext ⟨e.symm.toHom.isIntegral_of_injective e.symm.toHom_injective,
      e.toHom.isIntegral_of_injective e.toHom_injective⟩

@[simp]
theorem isIntegral_ofAlgebra {A : Type*} [RelationAlgebra A] [Finite A] {k : ℕ}
    (h : Nat.card {a : A // IsAtom a} = k) :
    IsIntegral (ofAlgebra h) ↔ RelationAlgebra.IsIntegral A :=
  let e := labelledEquiv h
  ⟨e.toHom.isIntegral_of_injective e.toHom_injective,
    e.symm.toHom.isIntegral_of_injective e.symm.toHom_injective⟩

theorem ofAlgebra_complexAlgebra {k : ℕ} (S : AtomStructure (Fin k)) [LawfulAtomStructure S] :
    ofAlgebra ((ComplexAlgebra.card_atoms S).trans (Nat.card_fin k)) = ⟦⟨S, inferInstance⟩⟧ :=
  Quotient.sound ⟨(labelledEquiv _).symm⟩

theorem card_integral_atoms {s n k : ℕ} (h : 1 + s + 2 * n = k)
    (g : Set (IntegralAtom.Cycle (Fin s) (Fin n))) :
    Nat.card {a : ComplexAlgebra (IntegralAtom.ofCycles g) // IsAtom a} = k := by
  rw [ComplexAlgebra.card_atoms, Nat.card_congr IntegralAtom.equivOptionSum]
  simpa [Nat.card_eq_fintype_card, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    Nat.mul_comm] using h

/-- Forget integrality while retaining the total number of atoms. -/
noncomputable def ofIntegral {k : ℕ} : IntegralAtom.IsoClass.ofAtoms k → ofAtoms k
  | ⟨_, ⟨_, h⟩, q⟩ => Quotient.liftOn q (fun g => ofAlgebra (card_integral_atoms h g.val))
      fun _ _ e => (ofAlgebra_eq_iff ..).mpr e

theorem ofIntegral_injective {k : ℕ} : Function.Injective (ofIntegral (k := k)) := by
  rintro ⟨s, ⟨n, h⟩, q⟩ ⟨t, ⟨m, h'⟩, q'⟩ he
  induction q using Quotient.ind with | _ g
  induction q' using Quotient.ind with | _ g'
  obtain ⟨e⟩ := (ofAlgebra_eq_iff ..).mp he
  have hs := e.ncard_symmetricDiversityAtoms
  simp only [IntegralAtom.ncard_symmetricDiversityAtoms_ofCycles, Nat.card_fin] at hs
  subst t
  obtain rfl : n = m := by omega
  have heq : (⟦g⟧ : IntegralAtom.IsoClass.ofSymmNsymm s n) = ⟦g'⟧ := Quotient.sound ⟨e⟩
  rw [heq]

instance (k : ℕ) : Finite (IntegralAtom.IsoClass.ofAtoms k) :=
  Finite.of_injective _ ofIntegral_injective

/-- The existing integral classes are exactly the integral part of the general quotient. -/
theorem range_ofIntegral {k : ℕ} : Set.range (ofIntegral (k := k)) = {q | IsIntegral q} := by
  ext q
  constructor
  · rintro ⟨⟨s, ⟨n, h⟩, q⟩, rfl⟩
    induction q using Quotient.ind with | _ g
    exact (isIntegral_ofAlgebra _).mpr (IntegralAtom.isIntegral_ofCycles g.val)
  · induction q using Quotient.ind with | _ S
    intro (hI : RelationAlgebra.IsIntegral (ComplexAlgebra S.val))
    let A := ComplexAlgebra S.val
    let s := (symmetricDiversityAtoms A).ncard
    obtain ⟨n, hn⟩ := even_ncard_nonsymmetricDiversityAtoms (α := A)
    have hn' : (nonsymmetricDiversityAtoms A).ncard = 2 * n := by omega
    have hk := (ComplexAlgebra.card_atoms S.val).trans (Nat.card_fin k)
    have h : 1 + s + 2 * n = k := by
      rw [← hn', ← ncard_setOf_isAtom_of_isIntegral hI]
      exact hk
    obtain ⟨g, inst, ⟨e⟩⟩ := IntegralAtom.exists_ofCycles_of_isIntegral hI rfl hn'
    refine ⟨⟨s, ⟨n, h⟩, ⟦⟨g, inst⟩⟧⟩, ?_⟩
    exact ((ofAlgebra_eq_iff _ hk).mpr ⟨e.symm⟩).trans (ofAlgebra_complexAlgebra S.val)

theorem card_integral_le (k : ℕ) :
    Nat.card (IntegralAtom.IsoClass.ofAtoms k) ≤ Nat.card (ofAtoms k) :=
  Nat.card_le_card_of_injective ofIntegral ofIntegral_injective

/-- The general count splits into the existing integral count and its complement. -/
theorem card_integral_add_card_nonintegral (k : ℕ) : Nat.card (IntegralAtom.IsoClass.ofAtoms k) +
    Nat.card {q : ofAtoms k // ¬ IsIntegral q} = Nat.card (ofAtoms k) := by
  classical
  rw [Nat.card_congr (Equiv.ofInjective ofIntegral (@ofIntegral_injective k)), range_ofIntegral]
  exact Set.ncard_add_ncard_compl {q : ofAtoms k | IsIntegral q}

/-- The diagonal algebra, in which all atoms lie below the identity, supplies a class
at every size, including the trivial algebra at size zero. -/
theorem card_ofAtoms_pos (k : ℕ) : 0 < Nat.card (ofAtoms k) := by
  let D : AtomStructure (Fin k) :=
    ⟨id, Set.univ, {c | c.1 = c.2.1 ∧ c.2.1 = c.2.2}⟩
  have lawful : LawfulAtomStructure D := {
    assoc := by simp only [D, Set.mem_ofPred_eq]; grind
    id_cycle_right := by simp [D]
    exists_id_cycle_right r := ⟨r, Set.mem_univ _, rfl, rfl⟩
    cycle_left := by simp [D] }
  exact Finite.card_pos_iff.mpr ⟨⟦⟨D, lawful⟩⟧⟩

end IsoClass

end Cslib.RelationAlgebra
