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
# Catalogue algebra ⟨1, 0, 1⟩, number 2

Entry 2 in the ⟨1, 0, 1⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aaa`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The algebra is represented by equality and the two strict order relations on the rationals.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S0N1.Ra02

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 0 1) :=
  let a : DiversityAtom 0 1 := Sum.inr (0, false)
  {(a, a, a)}

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 0 1 where
  cycles := cycles
  associative := by decide +kernel

/-- The finite relation algebra determined by this table. -/
abbrev Algebra : Type := Complex table

/-- This algebra has the signature of its catalogue row. -/
theorem signature : HasSignature Algebra 1 0 1 :=
  Complex.hasSignature table

/-- Atomic multiplication is characterized exactly by the listed cycles and their closure. -/
theorem cycles_iff (x y z : Atom 0 1) :
    Complex.atom table z ≤ Complex.atom table x * Complex.atom table y ↔
      cycleClosure cycles x y z :=
  Complex.atom_le_mul_iff table x y z

/-- Label rational pairs by equality, increasing order, or decreasing order. -/
def rationalLabel (x y : ℚ) : Atom 0 1 :=
  if x = y then none else if x < y then some (.inr (0, false)) else some (.inr (0, true))

@[simp] private theorem rationalLabel_eq_none (x y : ℚ) : rationalLabel x y = none ↔ x = y := by
  unfold rationalLabel
  split_ifs <;> simp_all

@[simp] private theorem rationalLabel_eq_forward (x y : ℚ) :
    rationalLabel x y = some (.inr (0, false)) ↔ x < y := by
  unfold rationalLabel
  split_ifs <;> simp_all

@[simp] private theorem rationalLabel_eq_backward (x y : ℚ) :
    rationalLabel x y = some (.inr (0, true)) ↔ y < x := by
  unfold rationalLabel
  split_ifs with hxy hlt
  · subst y
    simp
  · simp [not_lt_of_gt hlt]
  · simp only [true_iff]
    exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hxy)

private theorem rationalLabel_converse (x y : ℚ) :
    rationalLabel y x = Atom.converse (rationalLabel x y) := by
  rcases lt_trichotomy x y with h | h | h
  · simp [rationalLabel, ne_of_lt h, ne_of_gt h, not_lt_of_gt h, h,
      Atom.converse, DiversityAtom.converse]
  · subst y
    simp [rationalLabel, Atom.converse]
  · simp [rationalLabel, ne_of_lt h, ne_of_gt h, not_lt_of_gt h, h,
      Atom.converse, DiversityAtom.converse]

private theorem forward_forward (c : Atom 0 1) :
    cycleClosure table.cycles (some (.inr (0, false))) (some (.inr (0, false))) c ↔
      c = some (.inr (0, false)) := by
  revert c
  decide +kernel

private theorem backward_backward (c : Atom 0 1) :
    cycleClosure table.cycles (some (.inr (0, true))) (some (.inr (0, true))) c ↔
      c = some (.inr (0, true)) := by
  revert c
  decide +kernel

private theorem forward_backward (c : Atom 0 1) :
    cycleClosure table.cycles (some (.inr (0, false))) (some (.inr (0, true))) c := by
  revert c
  decide +kernel

private theorem backward_forward (c : Atom 0 1) :
    cycleClosure table.cycles (some (.inr (0, true))) (some (.inr (0, false))) c := by
  revert c
  decide +kernel

private theorem atom_cases (a : Atom 0 1) :
    a = none ∨ a = some (.inr (0, false)) ∨ a = some (.inr (0, true)) := by
  revert a
  decide +kernel

/-- The representation by equality and strict order on the rational numbers. -/
def representation : AtomRepresentation table ℚ where
  label := rationalLabel
  surjective := by
    intro a
    rcases atom_cases a with rfl | rfl | rfl
    · exact ⟨(0, 0), by decide⟩
    · exact ⟨(0, 1), by decide⟩
    · exact ⟨(1, 0), by decide⟩
  identity x y := by exact rationalLabel_eq_none x y
  converse x y := by exact rationalLabel_converse x y
  composition a b x y := by
    rcases atom_cases a with rfl | rfl | rfl <;>
      rcases atom_cases b with rfl | rfl | rfl
    all_goals simp only [cycleClosure_none_left, cycleClosure_none_right, forward_forward,
      backward_backward, forward_backward, backward_forward, rationalLabel_eq_none,
      rationalLabel_eq_forward, rationalLabel_eq_backward, true_iff]
    · rw [eq_comm (a := none), rationalLabel_eq_none]
      simp
    · rw [eq_comm (b := rationalLabel x y), rationalLabel_eq_forward]
      simp
    · rw [eq_comm (b := rationalLabel x y), rationalLabel_eq_backward]
      simp
    · rw [eq_comm (b := rationalLabel x y), rationalLabel_eq_forward]
      simp
    · exact ⟨exists_between, fun ⟨_, hxz, hzy⟩ => hxz.trans hzy⟩
    · obtain ⟨z, hz⟩ := exists_gt (max x y)
      exact ⟨z, (le_max_left x y).trans_lt hz, (le_max_right x y).trans_lt hz⟩
    · rw [eq_comm (b := rationalLabel x y), rationalLabel_eq_backward]
      simp
    · obtain ⟨z, hz⟩ := exists_lt (min x y)
      exact ⟨z, hz.trans_le (min_le_left x y), hz.trans_le (min_le_right x y)⟩
    · constructor
      · intro h
        obtain ⟨z, hyz, hzx⟩ := exists_between h
        exact ⟨z, hzx, hyz⟩
      · rintro ⟨_, hzx, hyz⟩
        exact hyz.trans hzx


/-- This catalogue algebra has a representation on an infinite rational base. -/
theorem representable : Representable Algebra :=
  representation.representable

end Cslib.RelationAlgebra.Catalogue.I1S0N1.Ra02
