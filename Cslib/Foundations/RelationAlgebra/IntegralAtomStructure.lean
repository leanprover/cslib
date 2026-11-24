/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.AtomStructure
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Data.Set.Card.Arithmetic

/-!
# Integral atom structures

This module abstractly defines the atoms of an integral relation algebra, along with a
characterization of its identity and non-identity cycles that form an atom structure when
shown to be associative.

## References

* [Steven Givant, *Introduction to Relation Algebras*][Givant2017a], Section 4.2
* [Steven Givant, *Advanced Topics in Relation Algebras*][Givant2017b], Section 19.3
* [Peter Jipsen, *Small relation algebras*](https://www1.chapman.edu/~jipsen/gap/ramaddux.html)

-/

@[expose] public section

namespace Cslib.RelationAlgebra

/--
The atoms of an integral atom structure: the identity atom, `s` symmetric diversity (non-identity)
atoms, and `n` pairs of nonsymmetric atoms.
-/
inductive IntegralAtom (s n : ℕ) : Type where
  /-- The identity atom. -/
  | one
  /-- A symmetric diversity atom. -/
  | symm (i : Fin s)
  /-- A nonsymmetric atom. `nsymm i true` is the converse of `nsymm i false`. -/
  | nsymm (i : Fin n) (conv : Bool)
  deriving DecidableEq

namespace IntegralAtom

variable {s n : ℕ}

/-- `IntegralAtom n s` as a sum. -/
def equivOptionSum : IntegralAtom s n ≃ Option (Fin s ⊕ Fin n × Bool) where
  toFun
    | one => none
    | symm i => some (.inl i)
    | nsymm i b => some (.inr (i, b))
  invFun
    | none => one
    | some (.inl i) => symm i
    | some (.inr (i, b)) => nsymm i b
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | ⟨_, _⟩) <;> rfl

instance : Fintype (IntegralAtom s n) := .ofEquiv _ equivOptionSum.symm

/-- The converse of an atom, where just nonsymmetric atoms are flipped. -/
def conv : IntegralAtom s n → IntegralAtom s n
  | one => one
  | symm i => symm i
  | nsymm i b => nsymm i (!b)

/-- An integral cycle is a triple of integral atoms. -/
abbrev Cycle (s n : ℕ) := IntegralAtom s n × IntegralAtom s n × IntegralAtom s n

/-- The left cycle transformation: `t ≤ r * u` implies `u ≤ conv r * t` -/
def Cycle.left : Cycle s n → Cycle s n
  | (r, u, t) => (conv r, t, u)

/-- The right cycle transformation: `t ≤ r * u` implies `r ≤ t * conv u` -/
def Cycle.right : Cycle s n → Cycle s n
  | (r, u, t) => (t, conv u, r)

/-- A cycle without identity. -/
abbrev Cycle.IsDiversity : Cycle s n → Prop
  | (r, u, t) => r ≠ one ∧ u ≠ one ∧ t ≠ one

/-- The union of the Peircean orbits of the generators and all identity cycles. -/
inductive CycleClosure (g : Set (Cycle s n)) : Cycle s n → Prop
  | of {c : Cycle s n} : c ∈ g → CycleClosure g c
  | id (a : IntegralAtom s n) : CycleClosure g (a, one, a)
  | left {c : Cycle s n} : CycleClosure g c → CycleClosure g c.left
  | right {c : Cycle s n} : CycleClosure g c → CycleClosure g c.right

@[simp, grind =]
theorem conv_one : conv (one : IntegralAtom s n) = one := rfl

@[simp, grind =]
theorem conv_symm (i : Fin s) : conv (symm i : IntegralAtom s n) = symm i := rfl

@[simp, grind =]
theorem conv_nsymm (i : Fin n) (b : Bool) : conv (nsymm i b : IntegralAtom s n) = nsymm i !b := rfl

@[simp, grind =]
theorem conv_conv (a : IntegralAtom s n) : conv (conv a) = a := by
  cases a <;> simp

private theorem CycleClosure.id_cycle_aux {g : Set (Cycle s n)} (hg : ∀ c ∈ g, c.IsDiversity)
    {r u t : IntegralAtom s n} (h : CycleClosure g (r, u, t)) :
    (r = one → t = u) ∧ (u = one → t = r) ∧ (t = one → u = conv r) := by
  generalize hc : (r, u, t) = c at h
  induction h generalizing r u t <;> grind [Cycle.left, Cycle.right, conv_conv]

theorem CycleClosure.id_cycle_left {g : Set (Cycle s n)} (hg : ∀ c ∈ g, c.IsDiversity)
    {u t : IntegralAtom s n} (h : CycleClosure g (one, u, t)) : t = u :=
  (h.id_cycle_aux hg).1 rfl

theorem CycleClosure.id_cycle_right {g : Set (Cycle s n)} (hg : ∀ c ∈ g, c.IsDiversity)
    {r t : IntegralAtom s n} (h : CycleClosure g (r, one, t)) : t = r :=
  (h.id_cycle_aux hg).2.1 rfl

theorem CycleClosure.id_cycle_conv {g : Set (Cycle s n)} (hg : ∀ c ∈ g, c.IsDiversity)
    {r u : IntegralAtom s n} (h : CycleClosure g (r, u, one)) : u = conv r :=
  (h.id_cycle_aux hg).2.2 rfl

theorem cycleClosure_one_iff {g : Set (Cycle s n)} (hg : ∀ c ∈ g, c.IsDiversity)
    {r p : IntegralAtom s n} : CycleClosure g (r, one, p) ↔ p = r :=
  ⟨fun h => h.id_cycle_right hg, fun h => h ▸ .id p⟩

/-- Construct an `AtomStructure` from diversity cycle generators. -/
def ofCycles (g : Set (Cycle s n)) : AtomStructure (IntegralAtom s n) where
  conv := conv
  id := {one}
  cycles := {c | CycleClosure g c}

@[simp]
theorem ofCycles_conv (g : Set (Cycle s n)) (a : IntegralAtom s n) :
    (ofCycles g).conv a = conv a := rfl

@[simp]
theorem mem_ofCycles_id {g : Set (Cycle s n)} {a : IntegralAtom s n} :
    a ∈ (ofCycles g).id ↔ a = one := .rfl

@[simp]
theorem mem_ofCycles_cycles {g : Set (Cycle s n)} {c : Cycle s n} :
    c ∈ (ofCycles g).cycles ↔ CycleClosure g c := .rfl

theorem lawfulAtomStructure_ofCycles (g : Set (Cycle s n))
    (hassoc : ∀ {r q p u t}, CycleClosure g (r, q, p) → CycleClosure g (u, t, q) →
      ∃ q', CycleClosure g (q', t, p) ∧ CycleClosure g (r, u, q'))
    (hg : ∀ c ∈ g, c.IsDiversity) :
    LawfulAtomStructure (ofCycles g) where
  assoc := hassoc
  id_cycle_right hs h := (cycleClosure_one_iff hg).mp (hs ▸ h)
  exists_id_cycle_right r := ⟨one, rfl, .id r⟩
  cycle_left := .left

/-- The complex algebra constructed from diversity cycles is integral. -/
@[simp]
theorem isIntegral_ofCycles (g : Set (Cycle s n)) [LawfulAtomStructure (ofCycles g)] :
    IsIntegral (ComplexAlgebra (ofCycles g)) :=
  (ComplexAlgebra.isIntegral_iff _).mpr ⟨one, rfl⟩

theorem preimage_singleton_symmetricDiversityAtoms (g : Set (Cycle s n))
    [LawfulAtomStructure (ofCycles g)] :
    singleton ⁻¹' symmetricDiversityAtoms (ComplexAlgebra (ofCycles g)) = Set.range symm := by
  ext a
  cases a <;> simp

theorem preimage_singleton_nonsymmetricDiversityAtoms (g : Set (Cycle s n))
    [LawfulAtomStructure (ofCycles g)] :
    singleton ⁻¹' nonsymmetricDiversityAtoms (ComplexAlgebra (ofCycles g)) =
      Set.range (Function.uncurry nsymm) := by
  ext a
  cases a <;> simp

theorem ncard_symmetricDiversityAtoms_ofCycles (g : Set (Cycle s n))
    [LawfulAtomStructure (ofCycles g)] :
    (symmetricDiversityAtoms (ComplexAlgebra (ofCycles g))).ncard = s := by
  rw [← ComplexAlgebra.ncard_preimage_singleton fun _ => And.left,
    preimage_singleton_symmetricDiversityAtoms,
    Set.ncard_range_of_injective fun _ _ => symm.inj, Nat.card_fin]

theorem ncard_nonsymmetricDiversityAtoms_ofCycles (g : Set (Cycle s n))
    [LawfulAtomStructure (ofCycles g)] :
    (nonsymmetricDiversityAtoms (ComplexAlgebra (ofCycles g))).ncard = 2 * n := by
  rw [← ComplexAlgebra.ncard_preimage_singleton fun _ => And.left,
    preimage_singleton_nonsymmetricDiversityAtoms,
    Set.ncard_range_of_injective (by simp [Function.Injective])]
  simp [mul_comm]

end IntegralAtom

/-- A bundled type for finite integral relation algebras. This is useful for stating theorems about
the number of algebras up to isomorphism. -/
structure IntegralAlgebra where
  /-- The underlying type of the algebra. -/
  carrier : Type
  [relationAlgebra : RelationAlgebra carrier]
  [finite : Finite carrier]
  isIntegral : IsIntegral carrier

attribute [instance] IntegralAlgebra.relationAlgebra IntegralAlgebra.finite

namespace IntegralAlgebra

protected instance setoid : Setoid IntegralAlgebra where
  r A B := Nonempty (RelationAlgebraEquiv A.carrier B.carrier)
  iseqv := ⟨fun _ => ⟨.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Isomorphism classes of finite integral relation algebras. -/
abbrev IsoClass : Type 1 := Quotient IntegralAlgebra.setoid

namespace IsoClass

/-- The set of isomorphism classes with `s` symmetric diversity atoms and `m` nonsymmetric
atoms. Note for nonsymmetric atoms this is a count of atoms, not pairs. Use the `ofSymmNsymm` abbrev
to avoid confusion with the usual convention.
-/
def ofCounts (s m : ℕ) : Set IsoClass :=
  {q | ∃ A : IntegralAlgebra, ⟦A⟧ = q ∧ (symmetricDiversityAtoms A.carrier).ncard = s ∧
    (nonsymmetricDiversityAtoms A.carrier).ncard = m}

@[simp]
theorem mk_mem_ofCounts_iff {A : IntegralAlgebra} {s m : ℕ} :
    ⟦A⟧ ∈ ofCounts s m ↔ (symmetricDiversityAtoms A.carrier).ncard = s ∧
      (nonsymmetricDiversityAtoms A.carrier).ncard = m := by
  constructor
  · rintro ⟨B, hB, rfl, rfl⟩
    obtain ⟨e⟩ := Quotient.exact hB
    exact ⟨e.ncard_symmetricDiversityAtoms.symm, e.ncard_nonsymmetricDiversityAtoms.symm⟩
  · exact fun h => ⟨A, rfl, h⟩

/-- The set of isomorphism classes with `k` atoms. -/
def ofAtoms (k : ℕ) : Set IsoClass :=
  {q | ∃ A : IntegralAlgebra, ⟦A⟧ = q ∧ {a : A.carrier | IsAtom a}.ncard = k}

theorem mem_ofAtoms_iff {k : ℕ} {q : IsoClass} :
    q ∈ ofAtoms k ↔ ∃ s m, 1 + s + m = k ∧ q ∈ ofCounts s m := by
  simp [ofAtoms, ofCounts, ncard_setOf_isAtom_of_isIntegral (IntegralAlgebra.isIntegral _),
    and_comm]

@[simp]
theorem ofAtoms_zero : ofAtoms 0 = ∅ := by
  ext q
  simp [mem_ofAtoms_iff]

theorem ofCounts_eq_empty_of_odd {s m : ℕ} (hm : Odd m) : ofCounts s m = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro _ ⟨A, rfl, -, hA⟩
  exact Nat.not_even_iff_odd.mpr hm (hA ▸ even_ncard_nonsymmetricDiversityAtoms)

theorem pairwiseDisjoint_ofCounts {t : Set (ℕ × ℕ)} :
    t.PairwiseDisjoint fun (s, m) => ofCounts s m := by
  rintro ⟨s, m⟩ - ⟨s', m'⟩ - h
  rw [Function.onFun, Set.disjoint_left]
  refine Quotient.ind fun A hA hA' => h ?_
  obtain ⟨hs, hm⟩ := mk_mem_ofCounts_iff.mp hA
  obtain ⟨hs', hm'⟩ := mk_mem_ofCounts_iff.mp hA'
  exact Prod.ext (hs.symm.trans hs') (hm.symm.trans hm')

theorem encard_ofAtoms_succ (k : ℕ) :
    (ofAtoms (k + 1)).encard = ∑ p ∈ Finset.antidiagonal k, (ofCounts p.1 p.2).encard := by
  rw [← finsum_mem_coe_finset, ← (Finset.finite_toSet _).encard_biUnion pairwiseDisjoint_ofCounts]
  congr 1 with q
  simp [mem_ofAtoms_iff]
  grind

/-- The set of isomorphism classes with `s` symmetric diversity atoms and `n` pairs of nonsymmetric
atoms. This is an abbrev for the convenience of matching the usual convention without making proofs
more complicated. -/
abbrev ofSymmNsymm (s n : ℕ) : Set IsoClass := ofCounts s (2 * n)

theorem mk_complexAlgebra_ofCycles_mem_ofSymmNsymm {s n : ℕ} (g : Set (IntegralAtom.Cycle s n))
    [LawfulAtomStructure (IntegralAtom.ofCycles g)] :
    ⟦⟨ComplexAlgebra (IntegralAtom.ofCycles g), IntegralAtom.isIntegral_ofCycles g⟩⟧ ∈
      ofSymmNsymm s n :=
  mk_mem_ofCounts_iff.mpr ⟨IntegralAtom.ncard_symmetricDiversityAtoms_ofCycles g,
    IntegralAtom.ncard_nonsymmetricDiversityAtoms_ofCycles g⟩

theorem_wanted exists_ofCycles_of_mem_ofSymmNsymm {s n : ℕ} {q : IsoClass}
    (hq : q ∈ ofSymmNsymm s n) :
    ∃ (g : Set (IntegralAtom.Cycle s n)) (_ : LawfulAtomStructure (IntegralAtom.ofCycles g)),
      ⟦⟨ComplexAlgebra (IntegralAtom.ofCycles g), IntegralAtom.isIntegral_ofCycles g⟩⟧ = q

/-- The isomorphism classes with `s` symmetric diversity atoms and `n` pairs of nonsymmetric atoms 
are exactly those of the complex algebras of `IntegralAtom.ofCycles`. -/
theorem_wanted mem_ofSymmNsymm_iff {s n : ℕ} {q : IsoClass} :
    q ∈ ofSymmNsymm s n ↔
      ∃ (g : Set (IntegralAtom.Cycle s n)) (_ : LawfulAtomStructure (IntegralAtom.ofCycles g)),
        ⟦⟨ComplexAlgebra (IntegralAtom.ofCycles g), IntegralAtom.isIntegral_ofCycles g⟩⟧ = q :=
  ⟨fun hq => ❰exists_ofCycles_of_mem_ofSymmNsymm❱ hq,
    fun ⟨g, _, h⟩ => h ▸ mk_complexAlgebra_ofCycles_mem_ofSymmNsymm g⟩

theorem encard_ofAtoms_succ_eq_sum_ofSymmNsymm (k : ℕ) :
    (ofAtoms (k + 1)).encard =
      ∑ i ∈ Finset.range (k / 2 + 1), (ofSymmNsymm (k % 2 + 2 * i) (k / 2 - i)).encard := by
  rw [encard_ofAtoms_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine (Finset.sum_of_injOn (k % 2 + 2 * ·) ?_ ?_ (fun j hj hj' => ?_) fun i hi => ?_).symm
  · grind [Set.InjOn]
  · grind [Set.MapsTo]
  · rw [ofCounts_eq_empty_of_odd, Set.encard_empty]
    by_contra hodd
    exact hj' ⟨(j - k % 2) / 2, by grind, by grind⟩
  · grind

/-!
### Counts of isomorphism classes

The following statements are all of the known counts of isomorphism classes of finite integral
relation algebras, by symmetric and nonsymmetric atoms as well as overall.

They will certainly be too computationally expensive to prove here, but we
provide their statements as a reference. Proofs of the `ofAtoms` statements can start with
`simp [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ]` and then use each of
the `ofSymmNsymm` results.
-/

theorem_wanted encard_ofSymmNsymm_zero_zero : (ofSymmNsymm 0 0).encard = 1

theorem_wanted encard_ofAtoms_one : (ofAtoms 1).encard = 1 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm] using (❰encard_ofSymmNsymm_zero_zero❱)

theorem_wanted encard_ofSymmNsymm_one_zero : (ofSymmNsymm 1 0).encard = 2

theorem_wanted encard_ofAtoms_two : (ofAtoms 2).encard = 2 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm] using (❰encard_ofSymmNsymm_one_zero❱)

theorem_wanted encard_ofSymmNsymm_zero_one : (ofSymmNsymm 0 1).encard = 3

theorem_wanted encard_ofSymmNsymm_two_zero : (ofSymmNsymm 2 0).encard = 7

theorem_wanted encard_ofAtoms_three : (ofAtoms 3).encard = 10 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(❰encard_ofSymmNsymm_zero_one❱) + $(❰encard_ofSymmNsymm_two_zero❱))

theorem_wanted encard_ofSymmNsymm_one_one : (ofSymmNsymm 1 1).encard = 37

theorem_wanted encard_ofSymmNsymm_three_zero : (ofSymmNsymm 3 0).encard = 65

theorem_wanted encard_ofAtoms_four : (ofAtoms 4).encard = 102 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(❰encard_ofSymmNsymm_one_one❱) + $(❰encard_ofSymmNsymm_three_zero❱))

theorem_wanted encard_ofSymmNsymm_zero_two : (ofSymmNsymm 0 2).encard = 83

theorem_wanted encard_ofSymmNsymm_two_one : (ofSymmNsymm 2 1).encard = 1316

theorem_wanted encard_ofSymmNsymm_four_zero : (ofSymmNsymm 4 0).encard = 3013

theorem_wanted encard_ofAtoms_five : (ofAtoms 5).encard = 4412 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(❰encard_ofSymmNsymm_zero_two❱) + $(❰encard_ofSymmNsymm_two_one❱) +
      $(❰encard_ofSymmNsymm_four_zero❱))

theorem_wanted encard_ofSymmNsymm_one_two : (ofSymmNsymm 1 2).encard = 47965

theorem_wanted encard_ofSymmNsymm_three_one : (ofSymmNsymm 3 1).encard = 988464

theorem_wanted encard_ofSymmNsymm_five_zero : (ofSymmNsymm 5 0).encard = 3849920

theorem_wanted encard_ofAtoms_six : (ofAtoms 6).encard = 4886349 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(❰encard_ofSymmNsymm_one_two❱) + $(❰encard_ofSymmNsymm_three_one❱) +
      $(❰encard_ofSymmNsymm_five_zero❱))

theorem_wanted encard_ofSymmNsymm_zero_three : (ofSymmNsymm 0 3).encard = 4492953

theorem_wanted encard_ofSymmNsymm_two_two : (ofSymmNsymm 2 2).encard = 2186435732

theorem_wanted encard_ofSymmNsymm_four_one : (ofSymmNsymm 4 1).encard = 50265788140

theorem_wanted encard_ofSymmNsymm_six_zero : (ofSymmNsymm 6 0).encard = 292352449486

theorem_wanted encard_ofAtoms_seven : (ofAtoms 7).encard = 344809166311 := by
  simpa [encard_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    mod_cast congr($(❰encard_ofSymmNsymm_zero_three❱) + $(❰encard_ofSymmNsymm_two_two❱) +
      $(❰encard_ofSymmNsymm_four_one❱) + $(❰encard_ofSymmNsymm_six_zero❱))

theorem_wanted encard_ofSymmNsymm_one_three : (ofSymmNsymm 1 3).encard = 52506245239168

end IsoClass

end IntegralAlgebra

end Cslib.RelationAlgebra
