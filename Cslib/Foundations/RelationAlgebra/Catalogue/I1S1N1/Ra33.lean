/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FiniteRepresentation
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Max

/-!
# Catalogue algebra ⟨1, 1, 1⟩, number 33

Entry 33 in the ⟨1, 1, 1⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab abb ab~b~ bbb~ aaa bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The algebra is represented on finitely supported integer-indexed sequences over `ZMod 6`.
The least nonzero coefficient determines the label: odd coefficients are symmetric, while
coefficients 2 and 4 give the converse pair.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra33

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := Sum.inl 0
  let b : DiversityAtom 1 1 := Sum.inr (0, false)
  let b' : DiversityAtom 1 1 := Sum.inr (0, true)
  {(a, a, b), (a, b, b), (a, b', b'), (b, b, b'), (a, a, a), (b, b, b)}

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 1 1 where
  cycles := cycles
  associative := by decide +kernel

/-- The finite relation algebra determined by this table. -/
abbrev Algebra : Type := Complex table

/-- This algebra has the signature of its catalogue row. -/
theorem signature : HasSignature Algebra 1 1 1 :=
  Complex.hasSignature table

/-- Atomic multiplication is characterized exactly by the listed cycles and their closure. -/
theorem cycles_iff (x y z : Atom 1 1) :
    Complex.atom table z ≤ Complex.atom table x * Complex.atom table y ↔
      cycleClosure cycles x y z :=
  Complex.atom_le_mul_iff table x y z

/-- The additive group of finitely supported sequences over the six-element cyclic group. -/
abbrev Base := ℤ →₀ ZMod 6

/-- The first nonzero coefficient class in the six-element cyclic group. -/
def coefficientLabel (x : ZMod 6) : Atom 1 1 :=
  if x = 0 then none
  else if x = 2 then some (.inr (0, false))
  else if x = 4 then some (.inr (0, true))
  else some (.inl 0)

private theorem coefficientLabel_zero : coefficientLabel 0 = none := by decide

private theorem coefficientLabel_eq_none (x : ZMod 6) : coefficientLabel x = none ↔ x = 0 := by
  revert x
  decide +kernel

private theorem coefficientLabel_neg (x : ZMod 6) :
    coefficientLabel (-x) = Atom.converse (coefficientLabel x) := by
  revert x
  decide +kernel

private def Leading (f : Base) (i : ℤ) : Prop := f i ≠ 0 ∧ ∀ t < i, f t = 0

private theorem exists_leading (f : Base) (hf : f ≠ 0) : ∃ i, Leading f i := by
  have hs := Finsupp.support_nonempty_iff.mpr hf
  refine ⟨f.support.min' hs, ?_, ?_⟩
  · exact Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
  · intro t ht
    by_contra hn
    have hle := Finset.min'_le f.support t (Finsupp.mem_support_iff.mpr hn)
    exact (not_lt_of_ge hle) ht

private theorem leading_unique {f : Base} {i t : ℤ}
    (hi : Leading f i) (ht : Leading f t) : i = t := by
  apply le_antisymm
  · by_contra hn
    exact ht.1 (hi.2 _ (lt_of_not_ge hn))
  · by_contra hn
    exact hi.1 (ht.2 _ (lt_of_not_ge hn))

private theorem leading_ne_zero {f : Base} {i : ℤ} (hi : Leading f i) : f ≠ 0 := by
  intro h
  exact hi.1 (by rw [h]; rfl)

/-- Classify a finitely supported sequence by its least nonzero coefficient. -/
noncomputable def lexLabel (f : Base) : Atom 1 1 :=
  if h : f = 0 then none
  else coefficientLabel (f (Classical.choose (show ∃ i, f i ≠ 0 ∧ ∀ t < i, f t = 0 from by
    exact exists_leading f h)))

private theorem label_of_leading {f : Base} {i : ℤ} (hi : Leading f i) :
    lexLabel f = coefficientLabel (f i) := by
  rw [lexLabel, dite_eq_right (leading_ne_zero hi)]
  congr 2
  exact leading_unique (Classical.choose_spec (exists_leading f (leading_ne_zero hi))) hi

private theorem label_zero : lexLabel 0 = none := by simp [lexLabel]

private theorem label_eq_none (f : Base) : lexLabel f = none ↔ f = 0 := by
  by_cases hf : f = 0
  · simp [hf, label_zero]
  · obtain ⟨i, hi⟩ := exists_leading f hf
    rw [label_of_leading hi, coefficientLabel_eq_none]
    exact iff_of_false hi.1 hf

private theorem leading_single (i : ℤ) (x : ZMod 6) (hx : x ≠ 0) :
    Leading (Finsupp.single i x) i := by
  refine ⟨by simpa using hx, ?_⟩
  intro t ht
  simp [ne_of_gt ht]

private theorem label_single (i : ℤ) (x : ZMod 6) :
    lexLabel (Finsupp.single i x) = coefficientLabel x := by
  by_cases hx : x = 0
  · simp [hx, label_zero, coefficientLabel_zero]
  · simpa using label_of_leading (leading_single i x hx)

private theorem leading_neg {f : Base} {i : ℤ} (hi : Leading f i) : Leading (-f) i := by
  exact ⟨by simpa using hi.1, fun t ht => by simp [hi.2 t ht]⟩

private theorem label_neg (f : Base) : lexLabel (-f) = Atom.converse (lexLabel f) := by
  by_cases hf : f = 0
  · simp [hf, label_zero]
  · obtain ⟨i, hi⟩ := exists_leading f hf
    rw [label_of_leading (leading_neg hi), label_of_leading hi]
    exact coefficientLabel_neg (f i)

private theorem leading_add_left {f g : Base} {i t : ℤ}
    (hi : Leading f i) (ht : Leading g t) (hit : i < t) : Leading (f + g) i := by
  refine ⟨by simpa [ht.2 i hit] using hi.1, ?_⟩
  intro p hp
  simp [hi.2 p hp, ht.2 p (hp.trans hit)]

private theorem leading_add_same {f g : Base} {i : ℤ}
    (hi : Leading f i) (hg : Leading g i) (h : f i + g i ≠ 0) : Leading (f + g) i := by
  exact ⟨h, fun t ht => by simp [hi.2 t ht, hg.2 t ht]⟩

private theorem cycle_endpoints (a b : Atom 1 1) (ha : a ≠ none) (hb : b ≠ none) :
    cycleClosure table.cycles a b a ∧ cycleClosure table.cycles a b b := by
  revert a b
  decide +kernel

private theorem cycle_coeff_add (p q : ZMod 6) (hp : p ≠ 0) (hq : q ≠ 0)
    (hadd : p + q ≠ 0) :
    cycleClosure table.cycles (coefficientLabel p) (coefficientLabel q)
      (coefficientLabel (p + q)) := by
  revert p q
  decide +kernel

private theorem cycle_coeff_cancel (p q : ZMod 6) (hp : p ≠ 0) (hq : q ≠ 0)
    (hadd : p + q = 0) (c : Atom 1 1) :
    cycleClosure table.cycles (coefficientLabel p) (coefficientLabel q) c := by
  revert p q c
  decide +kernel

private theorem coefficient_surjective (a : Atom 1 1) (ha : a ≠ none) :
    ∃ p : ZMod 6, p ≠ 0 ∧ coefficientLabel p = a := by
  revert a
  decide +kernel

private theorem cycle_decompose (a b : Atom 1 1) (c : ZMod 6)
    (ha : a ≠ none) (hb : b ≠ none) (hc : c ≠ 0)
    (h : cycleClosure table.cycles a b (coefficientLabel c)) :
    (∃ p : ZMod 6, p ≠ 0 ∧ coefficientLabel p = a ∧ coefficientLabel (-p) = b) ∨
    a = coefficientLabel c ∨ b = coefficientLabel c ∨
    ∃ p : ZMod 6, p ≠ 0 ∧ c - p ≠ 0 ∧ coefficientLabel p = a ∧
      coefficientLabel (c - p) = b := by
  revert a b c
  decide +kernel

private theorem cycle_zero_decompose (a b : Atom 1 1) (ha : a ≠ none) (hb : b ≠ none)
    (h : cycleClosure table.cycles a b none) :
    ∃ p : ZMod 6, p ≠ 0 ∧ coefficientLabel p = a ∧ coefficientLabel (-p) = b := by
  revert a b
  decide +kernel

private theorem label_add_cycle (f g : Base) :
    cycleClosure table.cycles (lexLabel f) (lexLabel g) (lexLabel (f + g)) := by
  by_cases hf : f = 0
  · simp [hf, label_zero]
  by_cases hg : g = 0
  · simp [hg, label_zero]
  obtain ⟨i, hi⟩ := exists_leading f hf
  obtain ⟨t, ht⟩ := exists_leading g hg
  rcases lt_trichotomy i t with hit | rfl | hti
  · rw [label_of_leading (leading_add_left hi ht hit), Finsupp.add_apply, ht.2 i hit, add_zero,
      ← label_of_leading hi]
    exact (cycle_endpoints _ _ (mt (label_eq_none f).mp hf) (mt (label_eq_none g).mp hg)).1
  · by_cases hsum : f i + g i = 0
    · rw [label_of_leading hi, label_of_leading ht]
      exact cycle_coeff_cancel _ _ hi.1 ht.1 hsum _
    · rw [label_of_leading hi, label_of_leading ht,
        label_of_leading (leading_add_same hi ht hsum)]
      exact cycle_coeff_add _ _ hi.1 ht.1 hsum
  · have hs : Leading (f + g) t := by
      simpa [add_comm] using leading_add_left ht hi hti
    rw [label_of_leading hs, Finsupp.add_apply, hi.2 t hti, zero_add,
      ← label_of_leading ht]
    exact (cycle_endpoints _ _ (mt (label_eq_none f).mp hf) (mt (label_eq_none g).mp hg)).2

private theorem label_sub_single_after {f : Base} {i t : ℤ}
    (hi : Leading f i) (hit : i < t) (p : ZMod 6) :
    lexLabel (f - Finsupp.single t p) = lexLabel f := by
  have hs : Leading (f - Finsupp.single t p) i := by
    refine ⟨by simpa [ne_of_gt hit] using hi.1, ?_⟩
    intro q hq
    simp [hi.2 q hq, ne_of_gt (hq.trans hit)]
  rw [label_of_leading hs, label_of_leading hi]
  simp [ne_of_gt hit]

private theorem label_sub_single_before {f : Base} {i t : ℤ}
    (hi : Leading f i) (hti : t < i) (p : ZMod 6) (hp : p ≠ 0) :
    lexLabel (f - Finsupp.single t p) = coefficientLabel (-p) := by
  have hs : Leading (f - Finsupp.single t p) t := by
    refine ⟨by simpa [hi.2 t hti] using hp, ?_⟩
    intro q hq
    simp [hi.2 q (hq.trans hti), ne_of_gt hq]
  rw [label_of_leading hs]
  simp [hi.2 t hti]

private theorem label_sub_single_same {f : Base} {i : ℤ}
    (hi : Leading f i) (p : ZMod 6) (hp : f i - p ≠ 0) :
    lexLabel (f - Finsupp.single i p) = coefficientLabel (f i - p) := by
  have hs : Leading (f - Finsupp.single i p) i := by
    refine ⟨by simpa using hp, ?_⟩
    intro q hq
    simp [hi.2 q hq, ne_of_gt hq]
  rw [label_of_leading hs]
  simp

private theorem label_composition (a b : Atom 1 1) (f : Base) :
    cycleClosure table.cycles a b (lexLabel f) ↔
      ∃ h, lexLabel h = a ∧ lexLabel (f - h) = b := by
  constructor
  · intro h
    by_cases ha : a = none
    · subst a
      rw [cycleClosure_none_left] at h
      exact ⟨0, label_zero, by simpa using h.symm⟩
    by_cases hb : b = none
    · subst b
      rw [cycleClosure_none_right] at h
      exact ⟨f, h.symm, by simp [label_zero]⟩
    by_cases hf : f = 0
    · subst f
      rw [label_zero] at h
      obtain ⟨p, _, hp, hn⟩ := cycle_zero_decompose a b ha hb h
      refine ⟨Finsupp.single 0 p, ?_, ?_⟩
      · simpa [label_single] using hp
      · simpa [label_neg, label_single, ← coefficientLabel_neg] using hn
    obtain ⟨i, hi⟩ := exists_leading f hf
    rw [label_of_leading hi] at h
    rcases cycle_decompose a b (f i) ha hb hi.1 h with ⟨p, hp, hpa, hpb⟩ | hfa | hfb |
      ⟨p, hp, hcp, hpa, hpb⟩
    · refine ⟨Finsupp.single (i - 1) p, ?_, ?_⟩
      · simpa [label_single] using hpa
      · rw [label_sub_single_before hi (by omega) p hp]
        exact hpb
    · obtain ⟨q, _, hq⟩ := coefficient_surjective b hb
      refine ⟨f - Finsupp.single (i + 1) q, ?_, ?_⟩
      · rw [label_sub_single_after hi (by omega), label_of_leading hi]
        exact hfa.symm
      · simpa [label_single] using hq
    · obtain ⟨p, _, hp⟩ := coefficient_surjective a ha
      refine ⟨Finsupp.single (i + 1) p, ?_, ?_⟩
      · simpa [label_single] using hp
      · rw [label_sub_single_after hi (by omega), label_of_leading hi]
        exact hfb.symm
    · refine ⟨Finsupp.single i p, ?_, ?_⟩
      · simpa [label_single] using hpa
      · rw [label_sub_single_same hi p hcp]
        exact hpb
  · rintro ⟨h, rfl, rfl⟩
    simpa using label_add_cycle h (f - h)

/-- The group representation by the first nonzero coefficient of a finite sequence. -/
noncomputable def representation : GroupAtomRepresentation table (Multiplicative Base) where
  label g := lexLabel g.toAdd
  surjective a := by
    by_cases ha : a = none
    · exact ⟨1, by simpa [label_zero] using ha.symm⟩
    · obtain ⟨p, _, hp⟩ := coefficient_surjective a ha
      exact ⟨Multiplicative.ofAdd (Finsupp.single 0 p), by simpa [label_single] using hp⟩
  identity g := by exact label_eq_none g.toAdd
  converse g := by exact label_neg g.toAdd
  composition a b g := by
    rw [label_composition]
    constructor
    · rintro ⟨h, ha, hb⟩
      refine ⟨Multiplicative.ofAdd h, ha, ?_⟩
      simpa [sub_eq_add_neg, add_comm] using hb
    · rintro ⟨h, ha, hb⟩
      refine ⟨h.toAdd, ha, ?_⟩
      simpa [sub_eq_add_neg, add_comm] using hb

/-- This catalogue algebra has a representation on an infinite group. -/
theorem representable : Representable Algebra :=
  representation.representable

end Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra33
