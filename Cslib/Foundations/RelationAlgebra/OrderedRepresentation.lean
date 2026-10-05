/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FiniteRepresentation
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic

/-!
# Representations built from a dense order and finite fibers

Two- and three-point fibers over the rationals give four small relation algebras.
The symmetric diversity atom can relate either distinct points in one fiber or points
in different fibers; the remaining two diversity atoms record rational order.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.OrderedRepresentation

/-- The finite fiber has two points, or three when `large` is true. -/
abbrev Fiber (large : Bool) := Fin (2 + large.toNat)

private theorem exists_ne (large : Bool) (i : Fiber large) : ∃ j : Fiber large, i ≠ j := by
  cases large <;> revert i <;> decide +kernel

private theorem exists_third (large : Bool) (i j : Fiber large) :
    (∃ k : Fiber large, i ≠ k ∧ k ≠ j) ↔ large = true ∨ i = j := by
  cases large <;> revert i j <;> decide +kernel

private theorem atom_cases (a : Atom 1 1) :
    a = none ∨ a = some (.inl 0) ∨ a = some (.inr (0, false)) ∨
      a = some (.inr (0, true)) := by
  revert a
  decide +kernel

/-- The cycles obtained by replacing each rational point with a finite fiber. -/
def clusteredCycles (large : Bool) : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := .inl 0
  let b : DiversityAtom 1 1 := .inr (0, false)
  let b' : DiversityAtom 1 1 := .inr (0, true)
  {(a, b, b), (a, b', b'), (b, b, b)} ∪ if large then {(a, a, a)} else ∅

/-- Label equal rational coordinates by equality or symmetric diversity; order the others. -/
def clusteredLabel {large : Bool} (x y : ℚ × Fiber large) : Atom 1 1 :=
  if x.1 = y.1 then if x.2 = y.2 then none else some (.inl 0)
  else if x.1 < y.1 then some (.inr (0, false)) else some (.inr (0, true))

@[simp] private theorem clusteredLabel_eq_none {large : Bool} (x y : ℚ × Fiber large) :
    clusteredLabel x y = none ↔ x = y := by
  unfold clusteredLabel
  rw [Prod.ext_iff]
  split_ifs <;> simp_all

@[simp] private theorem clusteredLabel_eq_symmetric {large : Bool} (x y : ℚ × Fiber large) :
    clusteredLabel x y = some (.inl 0) ↔ x.1 = y.1 ∧ x.2 ≠ y.2 := by
  unfold clusteredLabel
  split_ifs <;> simp_all

@[simp] private theorem clusteredLabel_eq_forward {large : Bool} (x y : ℚ × Fiber large) :
    clusteredLabel x y = some (.inr (0, false)) ↔ x.1 < y.1 := by
  unfold clusteredLabel
  split_ifs <;> simp_all

@[simp] private theorem clusteredLabel_eq_backward {large : Bool} (x y : ℚ × Fiber large) :
    clusteredLabel x y = some (.inr (0, true)) ↔ y.1 < x.1 := by
  unfold clusteredLabel
  split_ifs with hxy hcoord hlt
  · simp [hxy]
  · simp [hxy]
  · simp [not_lt_of_gt hlt]
  · simp only [true_iff]
    exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hxy)

private theorem clusteredLabel_converse {large : Bool} (x y : ℚ × Fiber large) :
    clusteredLabel y x = Atom.converse (clusteredLabel x y) := by
  rcases lt_trichotomy x.1 y.1 with h | h | h
  · simp [clusteredLabel, ne_of_lt h, ne_of_gt h, not_lt_of_gt h, h,
      Atom.converse, DiversityAtom.converse]
  · by_cases h' : x.2 = y.2
    · simp [clusteredLabel, h, h', Atom.converse]
    · simp [clusteredLabel, h, h', Ne.symm h', Atom.converse, DiversityAtom.converse]
  · simp [clusteredLabel, ne_of_lt h, ne_of_gt h, not_lt_of_gt h, h,
      Atom.converse, DiversityAtom.converse]

private theorem clustered_ss (large : Bool) (c : Atom 1 1) :
    cycleClosure (clusteredCycles large) (some (.inl 0)) (some (.inl 0)) c ↔
      c = none ∨ large = true ∧ c = some (.inl 0) := by
  cases large <;> revert c <;> decide +kernel

private theorem clustered_sf (large : Bool) (c : Atom 1 1) :
    cycleClosure (clusteredCycles large) (some (.inl 0)) (some (.inr (0, false))) c ↔
      c = some (.inr (0, false)) := by
  cases large <;> revert c <;> decide +kernel

private theorem clustered_sb (large : Bool) (c : Atom 1 1) :
    cycleClosure (clusteredCycles large) (some (.inl 0)) (some (.inr (0, true))) c ↔
      c = some (.inr (0, true)) := by
  cases large <;> revert c <;> decide +kernel

private theorem clustered_fs (large : Bool) (c : Atom 1 1) :
    cycleClosure (clusteredCycles large) (some (.inr (0, false))) (some (.inl 0)) c ↔
      c = some (.inr (0, false)) := by
  cases large <;> revert c <;> decide +kernel

private theorem clustered_bs (large : Bool) (c : Atom 1 1) :
    cycleClosure (clusteredCycles large) (some (.inr (0, true))) (some (.inl 0)) c ↔
      c = some (.inr (0, true)) := by
  cases large <;> revert c <;> decide +kernel

private theorem clustered_ff (large : Bool) (c : Atom 1 1) :
    cycleClosure (clusteredCycles large) (some (.inr (0, false))) (some (.inr (0, false))) c ↔
      c = some (.inr (0, false)) := by
  cases large <;> revert c <;> decide +kernel

private theorem clustered_bb (large : Bool) (c : Atom 1 1) :
    cycleClosure (clusteredCycles large) (some (.inr (0, true))) (some (.inr (0, true))) c ↔
      c = some (.inr (0, true)) := by
  cases large <;> revert c <;> decide +kernel

private theorem clustered_fb (large : Bool) (c : Atom 1 1) :
    cycleClosure (clusteredCycles large) (some (.inr (0, false))) (some (.inr (0, true))) c := by
  cases large <;> revert c <;> decide +kernel

private theorem clustered_bf (large : Bool) (c : Atom 1 1) :
    cycleClosure (clusteredCycles large) (some (.inr (0, true))) (some (.inr (0, false))) c := by
  cases large <;> revert c <;> decide +kernel

/-- A representation with a symmetric atom inside each finite fiber of the rational order. -/
def clustered (large : Bool) (T : IntegralCycleTable 1 1)
    (hcycles : T.cycles = clusteredCycles large) : AtomRepresentation T (ℚ × Fiber large) where
  label := clusteredLabel
  surjective := by
    intro a
    rcases atom_cases a with rfl | rfl | rfl | rfl
    · exact ⟨((0, 0), (0, 0)), by simp⟩
    · exact ⟨((0, 0), (0, 1)), by cases large <;> decide⟩
    · exact ⟨((0, 0), (1, 0)), by simp⟩
    · exact ⟨((1, 0), (0, 0)), by simp⟩
  identity x y := by exact clusteredLabel_eq_none x y
  converse x y := by exact clusteredLabel_converse x y
  composition a b x y := by
    rw [hcycles]
    rcases atom_cases a with rfl | rfl | rfl | rfl <;>
      rcases atom_cases b with rfl | rfl | rfl | rfl
    all_goals simp only [cycleClosure_none_left, cycleClosure_none_right,
      clustered_ss, clustered_sf, clustered_sb, clustered_fs, clustered_bs,
      clustered_ff, clustered_bb, clustered_fb, clustered_bf, clusteredLabel_eq_none,
      clusteredLabel_eq_symmetric, clusteredLabel_eq_forward, clusteredLabel_eq_backward,
      true_iff]
    · rw [eq_comm (a := none), clusteredLabel_eq_none]
      simp
    · rw [eq_comm (b := clusteredLabel x y), clusteredLabel_eq_symmetric]
      simp
    · rw [eq_comm (b := clusteredLabel x y), clusteredLabel_eq_forward]
      simp
    · rw [eq_comm (b := clusteredLabel x y), clusteredLabel_eq_backward]
      simp
    · rw [eq_comm (b := clusteredLabel x y), clusteredLabel_eq_symmetric]
      simp
    · constructor
      · intro h
        have hxy : x.1 = y.1 := by
          rcases h with rfl | ⟨_, h, _⟩
          · rfl
          · exact h
        have hi : large = true ∨ x.2 = y.2 := by
          rcases h with rfl | ⟨h, _⟩
          · exact Or.inr rfl
          · exact Or.inl h
        obtain ⟨i, hxi, hiy⟩ := (exists_third large x.2 y.2).mpr hi
        exact ⟨(x.1, i), ⟨rfl, hxi⟩, hxy, hiy⟩
      · rintro ⟨z, ⟨hxz, hxi⟩, hzy, hiy⟩
        have hxy := hxz.trans hzy
        rcases (exists_third large x.2 y.2).mp ⟨z.2, hxi, hiy⟩ with h | h
        · by_cases hi : x.2 = y.2
          · exact Or.inl (Prod.ext hxy hi)
          · exact Or.inr ⟨h, hxy, hi⟩
        · exact Or.inl (Prod.ext hxy h)
    · constructor
      · intro h
        obtain ⟨i, hi⟩ := exists_ne large x.2
        exact ⟨(x.1, i), ⟨rfl, hi⟩, h⟩
      · rintro ⟨z, ⟨hxz, _⟩, hzy⟩
        exact hxz ▸ hzy
    · constructor
      · intro h
        obtain ⟨i, hi⟩ := exists_ne large x.2
        exact ⟨(x.1, i), ⟨rfl, hi⟩, h⟩
      · rintro ⟨z, ⟨hxz, _⟩, hzy⟩
        exact hxz ▸ hzy
    · rw [eq_comm (b := clusteredLabel x y), clusteredLabel_eq_forward]
      simp
    · constructor
      · intro h
        obtain ⟨i, hi⟩ := exists_ne large y.2
        exact ⟨(y.1, i), h, rfl, Ne.symm hi⟩
      · rintro ⟨z, hxz, hzy, _⟩
        exact hzy ▸ hxz
    · constructor
      · intro h
        obtain ⟨z, hxz, hzy⟩ := exists_between h
        exact ⟨(z, 0), hxz, hzy⟩
      · rintro ⟨z, hxz, hzy⟩
        exact hxz.trans hzy
    · obtain ⟨z, hz⟩ := exists_gt (max x.1 y.1)
      exact ⟨(z, 0), (le_max_left _ _).trans_lt hz, (le_max_right _ _).trans_lt hz⟩
    · rw [eq_comm (b := clusteredLabel x y), clusteredLabel_eq_backward]
      simp
    · constructor
      · intro h
        obtain ⟨i, hi⟩ := exists_ne large y.2
        exact ⟨(y.1, i), h, rfl, Ne.symm hi⟩
      · rintro ⟨z, hxz, hzy, _⟩
        exact hzy ▸ hxz
    · obtain ⟨z, hz⟩ := exists_lt (min x.1 y.1)
      exact ⟨(z, 0), hz.trans_le (min_le_left _ _), hz.trans_le (min_le_right _ _)⟩
    · constructor
      · intro h
        obtain ⟨z, hyz, hzx⟩ := exists_between h
        exact ⟨(z, 0), hzx, hyz⟩
      · rintro ⟨z, hzx, hyz⟩
        exact hyz.trans hzx

/-- The cycles of disjoint rational orders, with one symmetric atom between them. -/
def separatedCycles (large : Bool) : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := .inl 0
  let b : DiversityAtom 1 1 := .inr (0, false)
  {(a, a, b), (b, b, b)} ∪ if large then {(a, a, a)} else ∅

/-- Label different fibers by symmetric diversity and order points within one fiber. -/
def separatedLabel {large : Bool} (x y : ℚ × Fiber large) : Atom 1 1 :=
  if x.2 = y.2 then
    if x.1 = y.1 then none
    else if x.1 < y.1 then some (.inr (0, false)) else some (.inr (0, true))
  else some (.inl 0)

@[simp] private theorem separatedLabel_eq_none {large : Bool} (x y : ℚ × Fiber large) :
    separatedLabel x y = none ↔ x = y := by
  unfold separatedLabel
  rw [Prod.ext_iff]
  split_ifs <;> simp_all

@[simp] private theorem separatedLabel_eq_symmetric {large : Bool} (x y : ℚ × Fiber large) :
    separatedLabel x y = some (.inl 0) ↔ x.2 ≠ y.2 := by
  unfold separatedLabel
  split_ifs <;> simp_all

@[simp] private theorem separatedLabel_eq_forward {large : Bool} (x y : ℚ × Fiber large) :
    separatedLabel x y = some (.inr (0, false)) ↔ x.2 = y.2 ∧ x.1 < y.1 := by
  unfold separatedLabel
  split_ifs <;> simp_all

@[simp] private theorem separatedLabel_eq_backward {large : Bool} (x y : ℚ × Fiber large) :
    separatedLabel x y = some (.inr (0, true)) ↔ x.2 = y.2 ∧ y.1 < x.1 := by
  unfold separatedLabel
  split_ifs with hcoord hxy hlt
  · simp [hxy]
  · simp [not_lt_of_gt hlt]
  · simp only [hcoord, true_and, true_iff]
    exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hxy)
  · simp [hcoord]

private theorem separatedLabel_converse {large : Bool} (x y : ℚ × Fiber large) :
    separatedLabel y x = Atom.converse (separatedLabel x y) := by
  by_cases hcoord : x.2 = y.2
  · rcases lt_trichotomy x.1 y.1 with h | h | h
    · simp [separatedLabel, hcoord, ne_of_lt h, ne_of_gt h, not_lt_of_gt h, h,
        Atom.converse, DiversityAtom.converse]
    · simp [separatedLabel, hcoord, h, Atom.converse]
    · simp [separatedLabel, hcoord, ne_of_lt h, ne_of_gt h, not_lt_of_gt h, h,
        Atom.converse, DiversityAtom.converse]
  · simp [separatedLabel, hcoord, Ne.symm hcoord, Atom.converse, DiversityAtom.converse]

private theorem separated_ss (large : Bool) (c : Atom 1 1) :
    cycleClosure (separatedCycles large) (some (.inl 0)) (some (.inl 0)) c ↔
      large = true ∨ c ≠ some (.inl 0) := by
  cases large <;> revert c <;> decide +kernel

private theorem separated_sf (large : Bool) (c : Atom 1 1) :
    cycleClosure (separatedCycles large) (some (.inl 0)) (some (.inr (0, false))) c ↔
      c = some (.inl 0) := by
  cases large <;> revert c <;> decide +kernel

private theorem separated_sb (large : Bool) (c : Atom 1 1) :
    cycleClosure (separatedCycles large) (some (.inl 0)) (some (.inr (0, true))) c ↔
      c = some (.inl 0) := by
  cases large <;> revert c <;> decide +kernel

private theorem separated_fs (large : Bool) (c : Atom 1 1) :
    cycleClosure (separatedCycles large) (some (.inr (0, false))) (some (.inl 0)) c ↔
      c = some (.inl 0) := by
  cases large <;> revert c <;> decide +kernel

private theorem separated_bs (large : Bool) (c : Atom 1 1) :
    cycleClosure (separatedCycles large) (some (.inr (0, true))) (some (.inl 0)) c ↔
      c = some (.inl 0) := by
  cases large <;> revert c <;> decide +kernel

private theorem separated_ff (large : Bool) (c : Atom 1 1) :
    cycleClosure (separatedCycles large) (some (.inr (0, false))) (some (.inr (0, false))) c ↔
      c = some (.inr (0, false)) := by
  cases large <;> revert c <;> decide +kernel

private theorem separated_bb (large : Bool) (c : Atom 1 1) :
    cycleClosure (separatedCycles large) (some (.inr (0, true))) (some (.inr (0, true))) c ↔
      c = some (.inr (0, true)) := by
  cases large <;> revert c <;> decide +kernel

private theorem separated_fb (large : Bool) (c : Atom 1 1) :
    cycleClosure (separatedCycles large) (some (.inr (0, false))) (some (.inr (0, true))) c ↔
      c ≠ some (.inl 0) := by
  cases large <;> revert c <;> decide +kernel

private theorem separated_bf (large : Bool) (c : Atom 1 1) :
    cycleClosure (separatedCycles large) (some (.inr (0, true))) (some (.inr (0, false))) c ↔
      c ≠ some (.inl 0) := by
  cases large <;> revert c <;> decide +kernel

/-- A representation with a symmetric atom between disjoint copies of the rational order. -/
def separated (large : Bool) (T : IntegralCycleTable 1 1)
    (hcycles : T.cycles = separatedCycles large) : AtomRepresentation T (ℚ × Fiber large) where
  label := separatedLabel
  surjective := by
    intro a
    rcases atom_cases a with rfl | rfl | rfl | rfl
    · exact ⟨((0, 0), (0, 0)), by simp⟩
    · exact ⟨((0, 0), (0, 1)), by cases large <;> decide⟩
    · exact ⟨((0, 0), (1, 0)), by simp⟩
    · exact ⟨((1, 0), (0, 0)), by simp⟩
  identity x y := by exact separatedLabel_eq_none x y
  converse x y := by exact separatedLabel_converse x y
  composition a b x y := by
    rw [hcycles]
    rcases atom_cases a with rfl | rfl | rfl | rfl <;>
      rcases atom_cases b with rfl | rfl | rfl | rfl
    all_goals simp only [cycleClosure_none_left, cycleClosure_none_right,
      separated_ss, separated_sf, separated_sb, separated_fs, separated_bs,
      separated_ff, separated_bb, separated_fb, separated_bf, separatedLabel_eq_none,
      separatedLabel_eq_symmetric, separatedLabel_eq_forward, separatedLabel_eq_backward,
      ne_eq, not_not]
    · rw [eq_comm (a := none), separatedLabel_eq_none]
      simp
    · rw [eq_comm (b := separatedLabel x y), separatedLabel_eq_symmetric]
      simp
    · rw [eq_comm (b := separatedLabel x y), separatedLabel_eq_forward]
      simp
    · rw [eq_comm (b := separatedLabel x y), separatedLabel_eq_backward]
      simp
    · rw [eq_comm (b := separatedLabel x y), separatedLabel_eq_symmetric]
      simp
    · constructor
      · intro h
        obtain ⟨i, hxi, hiy⟩ := (exists_third large x.2 y.2).mpr h
        exact ⟨(0, i), hxi, hiy⟩
      · rintro ⟨z, hxi, hiy⟩
        exact (exists_third large x.2 y.2).mp ⟨z.2, hxi, hiy⟩
    · constructor
      · intro h
        obtain ⟨z, hz⟩ := exists_lt y.1
        exact ⟨(z, y.2), h, rfl, hz⟩
      · rintro ⟨z, hxz, hzy, _⟩
        exact hzy ▸ hxz
    · constructor
      · intro h
        obtain ⟨z, hz⟩ := exists_gt y.1
        exact ⟨(z, y.2), h, rfl, hz⟩
      · rintro ⟨z, hxz, hzy, _⟩
        exact hzy ▸ hxz
    · rw [eq_comm (b := separatedLabel x y), separatedLabel_eq_forward]
      simp
    · constructor
      · intro h
        obtain ⟨z, hz⟩ := exists_gt x.1
        exact ⟨(z, x.2), ⟨rfl, hz⟩, h⟩
      · rintro ⟨z, ⟨hxz, _⟩, hzy⟩
        exact hxz ▸ hzy
    · constructor
      · rintro ⟨hxy, h⟩
        obtain ⟨z, hxz, hzy⟩ := exists_between h
        exact ⟨(z, x.2), ⟨rfl, hxz⟩, hxy, hzy⟩
      · rintro ⟨z, ⟨hxi, hxz⟩, hiy, hzy⟩
        exact ⟨hxi.trans hiy, hxz.trans hzy⟩
    · constructor
      · intro hxy
        obtain ⟨z, hz⟩ := exists_gt (max x.1 y.1)
        exact ⟨(z, x.2), ⟨rfl, (le_max_left _ _).trans_lt hz⟩,
          hxy, (le_max_right _ _).trans_lt hz⟩
      · rintro ⟨z, ⟨hxi, _⟩, hiy, _⟩
        exact hxi.trans hiy
    · rw [eq_comm (b := separatedLabel x y), separatedLabel_eq_backward]
      simp
    · constructor
      · intro h
        obtain ⟨z, hz⟩ := exists_lt x.1
        exact ⟨(z, x.2), ⟨rfl, hz⟩, h⟩
      · rintro ⟨z, ⟨hxz, _⟩, hzy⟩
        exact hxz ▸ hzy
    · constructor
      · intro hxy
        obtain ⟨z, hz⟩ := exists_lt (min x.1 y.1)
        exact ⟨(z, x.2), ⟨rfl, hz.trans_le (min_le_left _ _)⟩,
          hxy, hz.trans_le (min_le_right _ _)⟩
      · rintro ⟨z, ⟨hxi, _⟩, hiy, _⟩
        exact hxi.trans hiy
    · constructor
      · rintro ⟨hxy, h⟩
        obtain ⟨z, hyz, hzx⟩ := exists_between h
        exact ⟨(z, x.2), ⟨rfl, hzx⟩, hxy, hyz⟩
      · rintro ⟨z, ⟨hxi, hzx⟩, hiy, hyz⟩
        exact ⟨hxi.trans hiy, hyz.trans hzx⟩

end Cslib.RelationAlgebra.OrderedRepresentation
