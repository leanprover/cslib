/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCatalogueProfiles
public import Mathlib.Data.Fintype.EquivFin

/-!
# Counting integral relation algebras by canonical cycle masks

A canonical mask is an associative choice of Peircean cycles whose numeric profile is least
under atom renaming. Counting these masks counts isomorphism classes without requiring a
separate declaration for every algebra. The classification theorem applies to arbitrary
relation algebras with the prescribed signature, not just explicitly presented cycle tables.
-/

@[expose] public section

namespace Cslib.RelationAlgebra

open Code

variable {j k r p : ℕ}

/-- The cycles selected by a numeric profile. -/
def maskCycles (reps : Fin r → Cycle j k) (mask : ℕ) : Finset (Cycle j k) :=
  selectedCycles reps (fun i => bitAt mask i)

/-- Read the profile of a cycle table after renaming its atoms. -/
def renamedMask (reps : Fin r → Cycle j k) (cycles : Finset (Cycle j k))
    (rename : Atom j k → Atom j k) : ℕ :=
  choiceMask fun i => decide (cycleClosure cycles
    (rename (some (reps i).1)) (rename (some (reps i).2.1))
    (rename (some (reps i).2.2)))

/-- An associative mask which is least under all the supplied atom renamings. -/
def IsCanonicalMask (reps : Fin r → Cycle j k)
    (renames : Fin p → Atom j k → Atom j k) (mask : ℕ) : Prop :=
  AtomCompositionAssociative (maskCycles reps mask) ∧
    ∀ q, mask ≤ renamedMask reps (maskCycles reps mask) (renames q)

instance (reps : Fin r → Cycle j k) (renames : Fin p → Atom j k → Atom j k)
    (mask : ℕ) : Decidable (IsCanonicalMask reps renames mask) := by
  unfold IsCanonicalMask
  infer_instance

/-- Canonical profiles, with the bound on their number of bits. -/
abbrev CanonicalMask (reps : Fin r → Cycle j k)
    (renames : Fin p → Atom j k → Atom j k) :=
  {mask : Fin (2 ^ r) // IsCanonicalMask reps renames mask.val}

/-- The algebra table represented by a canonical profile. -/
def CanonicalMask.table {reps : Fin r → Cycle j k}
    {renames : Fin p → Atom j k → Atom j k} (mask : CanonicalMask reps renames) :
    IntegralCycleTable j k :=
  ⟨maskCycles reps mask.val.val, mask.property.1⟩

/-- The number of canonical profiles for a cycle basis and a family of atom renamings. -/
def canonicalMaskCount (reps : Fin r → Cycle j k)
    (renames : Fin p → Atom j k → Atom j k) : ℕ :=
  Fintype.card (CanonicalMask reps renames)

/-- Re-encoding the bits of a bounded mask recovers that mask. -/
theorem choiceMask_bitAt {mask : ℕ} (hm : mask < 2 ^ r) :
    choiceMask (fun i : Fin r => bitAt mask i) = mask := by
  apply eq_of_testBit_eq_of_lt (choiceMask_lt _) hm
  intro i hi
  simpa only [← bitAt_eq_testBit] using
    (bitAt_choiceMask (fun l : Fin r => bitAt mask l) ⟨i, hi⟩)

/-- The identity profile of a selected mask is the original mask. -/
theorem renamedMask_id (reps : Fin r → Cycle j k)
    (distinct : ∀ i l, (some (reps i).1, some (reps i).2.1, some (reps i).2.2) ∈
      cycleOrbit (reps l) ↔ i = l) {mask : ℕ} (hm : mask < 2 ^ r) :
    renamedMask reps (maskCycles reps mask) id = mask := by
  simp only [renamedMask, maskCycles, id_eq, cycleClosure_selectedCycles_rep reps distinct,
    Bool.decide_eq_true]
  exact choiceMask_bitAt hm

/-- A verified action on the cycle basis computes the profile after atom renaming. -/
theorem renamedMask_eq_permuteProfile (reps : Fin r → Cycle j k)
    (distinct : ∀ i l, (some (reps i).1, some (reps i).2.1, some (reps i).2.2) ∈
      cycleOrbit (reps l) ↔ i = l)
    (rename : DiversityAtom j k → DiversityAtom j k) (permutation : Fin r → Fin r)
    (horbit : ∀ i, (some (rename (reps i).1), some (rename (reps i).2.1),
      some (rename (reps i).2.2)) ∈ cycleOrbit (reps (permutation i)))
    {mask : ℕ} (hm : mask < 2 ^ r) :
    renamedMask reps (maskCycles reps mask) (Option.map rename) =
      Code.permuteProfile mask permutation := by
  exact profileCode_eq_of_orbit_renaming reps (maskCycles reps mask) rename permutation
    horbit mask (renamedMask_id reps distinct hm)

/-- Associativity is preserved when an injective finite atom relabelling is pulled back. -/
theorem AtomRelabelling.associative {S T : Finset (Cycle j k)}
    {f : Atom j k → Atom j k} (hf : AtomRelabelling S T f)
    (ha : AtomCompositionAssociative T) : AtomCompositionAssociative S := by
  have hs := Finite.surjective_of_injective hf.1
  have hex (a b c d : Atom j k) :
      (∃ u, cycleClosure S a b u ∧ cycleClosure S u c d) ↔
        ∃ u, cycleClosure T (f a) (f b) u ∧ cycleClosure T u (f c) (f d) := by
    constructor
    · rintro ⟨u, h₁, h₂⟩
      exact ⟨f u, (hf.2.2.2 _ _ _).mp h₁, (hf.2.2.2 _ _ _).mp h₂⟩
    · rintro ⟨u, h₁, h₂⟩
      obtain ⟨u, rfl⟩ := hs u
      exact ⟨u, (hf.2.2.2 _ _ _).mpr h₁, (hf.2.2.2 _ _ _).mpr h₂⟩
  intro a b c d
  rw [hex]
  refine (ha (f a) (f b) (f c) (f d)).trans ?_
  constructor
  · rintro ⟨u, h₁, h₂⟩
    obtain ⟨u, rfl⟩ := hs u
    exact ⟨u, (hf.2.2.2 _ _ _).mpr h₁, (hf.2.2.2 _ _ _).mpr h₂⟩
  · rintro ⟨u, h₁, h₂⟩
    exact ⟨f u, (hf.2.2.2 _ _ _).mp h₁, (hf.2.2.2 _ _ _).mp h₂⟩

/-- The renamed profile describes the pullback of the original table. -/
theorem atomRelabelling_renamedMask (reps : Fin r → Cycle j k)
    (cover : ∀ c : Cycle j k, ∃ i,
      (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (reps i))
    (distinct : ∀ i l, (some (reps i).1, some (reps i).2.1, some (reps i).2.2) ∈
      cycleOrbit (reps l) ↔ i = l)
    (cycles : Finset (Cycle j k)) (f : Atom j k → Atom j k)
    (hinj : Function.Injective f) (hn : f none = none)
    (hc : ∀ x, f x.converse = (f x).converse) :
    AtomRelabelling (maskCycles reps (renamedMask reps cycles f)) cycles f := by
  apply atomRelabelling_of_cycle_basis reps cover hinj hn hc
  intro i
  rw [maskCycles, cycleClosure_selectedCycles_rep reps distinct, renamedMask,
    bitAt_choiceMask, decide_eq_true_iff]

/-- Related masks have matching profiles after their atom relabelling. -/
theorem mask_eq_renamedMask (reps : Fin r → Cycle j k)
    (distinct : ∀ i l, (some (reps i).1, some (reps i).2.1, some (reps i).2.2) ∈
      cycleOrbit (reps l) ↔ i = l) {mask : ℕ} (hm : mask < 2 ^ r)
    {cycles : Finset (Cycle j k)} {f : Atom j k → Atom j k}
    (hf : AtomRelabelling (maskCycles reps mask) cycles f) :
    mask = renamedMask reps cycles f := by
  rw [← renamedMask_id reps distinct hm]
  unfold renamedMask
  simp only [id_eq, hf.2.2.2]

/-- Every integral table has an isomorphic table with a canonical profile. -/
theorem exists_canonicalMask (reps : Fin r → Cycle j k)
    (cover : ∀ c : Cycle j k, ∃ i,
      (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (reps i))
    (distinct : ∀ i l, (some (reps i).1, some (reps i).2.1, some (reps i).2.2) ∈
      cycleOrbit (reps l) ↔ i = l)
    (renames : Fin p → Atom j k → Atom j k)
    (laws : ∀ q, Function.Injective (renames q) ∧ renames q none = none ∧
      ∀ x, renames q x.converse = (renames q x).converse)
    (T : IntegralCycleTable j k) :
    ∃ mask : CanonicalMask reps renames,
      Nonempty (RelationAlgebraEquiv (Complex T) (Complex mask.table)) := by
  classical
  let property (mask : ℕ) : Prop :=
    ∃ (_ : mask < 2 ^ r) (ha : AtomCompositionAssociative (maskCycles reps mask)),
      Nonempty (RelationAlgebraEquiv (Complex T) (Complex ⟨maskCycles reps mask, ha⟩))
  have inhabited : ∃ mask, property mask := by
    obtain ⟨bits, hbits⟩ := exists_selectedCycles reps cover T.cycles
    have he : maskCycles reps (choiceMask bits) = selectedCycles reps bits := by
      simp only [maskCycles, bitAt_choiceMask]
    have ha : AtomCompositionAssociative (maskCycles reps (choiceMask bits)) := by
      rw [he]
      exact (atomCompositionAssociative_congr hbits).mpr T.associative
    refine ⟨choiceMask bits, choiceMask_lt bits, ha, ?_⟩
    let U : IntegralCycleTable j k := ⟨maskCycles reps (choiceMask bits), ha⟩
    have hf : AtomRelabelling U.cycles T.cycles id := by
      refine ⟨Function.injective_id, rfl, fun _ => rfl, ?_⟩
      simpa only [U, he, id_eq] using hbits
    exact ⟨(Complex.equivOfRelabelling U T id hf).symm⟩
  let mask := Nat.find inhabited
  obtain ⟨hm, ha, ⟨e⟩⟩ := Nat.find_spec inhabited
  have hmin : ∀ q, mask ≤ renamedMask reps (maskCycles reps mask) (renames q) := by
    intro q
    let other := renamedMask reps (maskCycles reps mask) (renames q)
    have hf := atomRelabelling_renamedMask reps cover distinct (maskCycles reps mask)
      (renames q) (laws q).1 (laws q).2.1 (laws q).2.2
    have ho : AtomCompositionAssociative (maskCycles reps other) := hf.associative ha
    apply Nat.find_min' inhabited
    refine ⟨choiceMask_lt _, ho, ?_⟩
    exact ⟨e.trans (Complex.equivOfRelabelling ⟨maskCycles reps other, ho⟩
      ⟨maskCycles reps mask, ha⟩ (renames q) hf).symm⟩
  exact ⟨⟨⟨mask, hm⟩, ha, hmin⟩, ⟨e⟩⟩

/-- Isomorphic canonical profiles are equal when the renaming family is exhaustive. -/
theorem CanonicalMask.eq_of_equiv (reps : Fin r → Cycle j k)
    (distinct : ∀ i l, (some (reps i).1, some (reps i).2.1, some (reps i).2.2) ∈
      cycleOrbit (reps l) ↔ i = l)
    (renames : Fin p → Atom j k → Atom j k)
    (exhaustive : ∀ f : Atom j k → Atom j k, Function.Injective f → f none = none →
      (∀ x, f x.converse = (f x).converse) → ∃ q, f = renames q)
    (S T : CanonicalMask reps renames)
    (e : RelationAlgebraEquiv (Complex S.table) (Complex T.table)) : S = T := by
  have le_of_equiv (S T : CanonicalMask reps renames)
      (e : RelationAlgebraEquiv (Complex S.table) (Complex T.table)) :
      T.val.val ≤ S.val.val := by
    obtain ⟨f, hf⟩ := Complex.exists_relabelling S.table T.table e
    obtain ⟨q, rfl⟩ := exhaustive f hf.1 hf.2.1 hf.2.2.1
    have he := mask_eq_renamedMask reps distinct S.val.isLt hf
    exact (T.property.2 q).trans_eq he.symm
  apply Subtype.ext
  apply Fin.ext
  exact le_antisymm (le_of_equiv T S e.symm) (le_of_equiv S T e)

/-- Canonical profiles classify arbitrary relation algebras of the specified signature. -/
theorem canonicalMask_classification (reps : Fin r → Cycle j k)
    (cover : ∀ c : Cycle j k, ∃ i,
      (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (reps i))
    (distinct : ∀ i l, (some (reps i).1, some (reps i).2.1, some (reps i).2.2) ∈
      cycleOrbit (reps l) ↔ i = l)
    (renames : Fin p → Atom j k → Atom j k)
    (laws : ∀ q, Function.Injective (renames q) ∧ renames q none = none ∧
      ∀ x, renames q x.converse = (renames q x).converse)
    (exhaustive : ∀ f : Atom j k → Atom j k, Function.Injective f → f none = none →
      (∀ x, f x.converse = (f x).converse) → ∃ q, f = renames q)
    (A : Type*) [RelationAlgebra A] (h : HasSignature A 1 j k) :
    ∃! mask : CanonicalMask reps renames,
      Nonempty (RelationAlgebraEquiv A (Complex mask.table)) := by
  classical
  let : Finite A := h.1
  let e := AtomLabelling.ofHasSignature h
  obtain ⟨mask, ⟨iso⟩⟩ := exists_canonicalMask reps cover distinct renames laws e.table
  let isoA := e.relationAlgebraEquiv.trans iso
  refine ⟨mask, ⟨isoA⟩, ?_⟩
  rintro other ⟨isoOther⟩
  exact CanonicalMask.eq_of_equiv reps distinct renames exhaustive other mask
    (isoOther.symm.trans isoA)

/-- Integral cycle tables are equivalent when their complex algebras are isomorphic. -/
def IntegralCycleTable.isomorphismSetoid (j k : ℕ) : Setoid (IntegralCycleTable j k) where
  r S T := Nonempty (RelationAlgebraEquiv (Complex S) (Complex T))
  iseqv :=
    ⟨fun _ => ⟨RelationAlgebraEquiv.refl _⟩,
      fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Isomorphism classes of integral tables with signature `⟨1, j, k⟩`. -/
abbrev IsomorphismClass (j k : ℕ) := Quotient (IntegralCycleTable.isomorphismSetoid j k)

/-- The number of isomorphism classes of integral tables of the given signature. -/
noncomputable def isomorphismClassCount (j k : ℕ) : ℕ := Nat.card (IsomorphismClass j k)

/-- Each isomorphism class has exactly one canonical cycle mask. -/
theorem canonicalMask_mk_bijective (reps : Fin r → Cycle j k)
    (cover : ∀ c : Cycle j k, ∃ i,
      (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (reps i))
    (distinct : ∀ i l, (some (reps i).1, some (reps i).2.1, some (reps i).2.2) ∈
      cycleOrbit (reps l) ↔ i = l)
    (renames : Fin p → Atom j k → Atom j k)
    (laws : ∀ q, Function.Injective (renames q) ∧ renames q none = none ∧
      ∀ x, renames q x.converse = (renames q x).converse)
    (exhaustive : ∀ f : Atom j k → Atom j k, Function.Injective f → f none = none →
      (∀ x, f x.converse = (f x).converse) → ∃ q, f = renames q) :
    Function.Bijective (fun mask : CanonicalMask reps renames =>
      Quotient.mk (IntegralCycleTable.isomorphismSetoid j k) mask.table) := by
  constructor
  · intro S T h
    obtain ⟨e⟩ := Quotient.exact h
    exact CanonicalMask.eq_of_equiv reps distinct renames exhaustive S T e
  · intro cls
    refine Quotient.inductionOn cls fun T => ?_
    obtain ⟨mask, ⟨e⟩⟩ := exists_canonicalMask reps cover distinct renames laws T
    exact ⟨mask, Quotient.sound ⟨e.symm⟩⟩

/-- Counting canonical profiles gives the isomorphism class count. -/
theorem isomorphismClassCount_eq_canonicalMaskCount (reps : Fin r → Cycle j k)
    (cover : ∀ c : Cycle j k, ∃ i,
      (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (reps i))
    (distinct : ∀ i l, (some (reps i).1, some (reps i).2.1, some (reps i).2.2) ∈
      cycleOrbit (reps l) ↔ i = l)
    (renames : Fin p → Atom j k → Atom j k)
    (laws : ∀ q, Function.Injective (renames q) ∧ renames q none = none ∧
      ∀ x, renames q x.converse = (renames q x).converse)
    (exhaustive : ∀ f : Atom j k → Atom j k, Function.Injective f → f none = none →
      (∀ x, f x.converse = (f x).converse) → ∃ q, f = renames q) :
    isomorphismClassCount j k = canonicalMaskCount reps renames := by
  let e := Equiv.ofBijective _
    (canonicalMask_mk_bijective reps cover distinct renames laws exhaustive)
  rw [isomorphismClassCount, ← Nat.card_congr e, Nat.card_eq_fintype_card]
  rfl

/-- A correct Boolean predicate can be counted directly on the bounded natural masks. -/
theorem canonicalMaskCount_eq_card_filter (reps : Fin r → Cycle j k)
    (renames : Fin p → Atom j k → Atom j k) (accept : ℕ → Bool)
    (haccept : ∀ mask < 2 ^ r,
      accept mask = true ↔ IsCanonicalMask reps renames mask) :
    canonicalMaskCount reps renames =
      ((Finset.range (2 ^ r)).filter fun mask => accept mask).card := by
  let e : CanonicalMask reps renames ≃
      {mask // mask ∈ (Finset.range (2 ^ r)).filter fun mask => accept mask} :=
    { toFun := fun mask => ⟨mask.val.val, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr mask.val.isLt, (haccept _ mask.val.isLt).mpr mask.property⟩⟩
      invFun := fun mask =>
        let hm := Finset.mem_range.mp (Finset.mem_filter.mp mask.property).1
        ⟨⟨mask.val, hm⟩, (haccept _ hm).mp (Finset.mem_filter.mp mask.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

end Cslib.RelationAlgebra
