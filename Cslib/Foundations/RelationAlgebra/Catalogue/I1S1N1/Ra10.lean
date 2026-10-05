/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.FiniteRepresentation
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Catalogue algebra ⟨1, 1, 1⟩, number 10

Entry 10 in the ⟨1, 1, 1⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `abb~ bbb~ bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The representation below partitions the quaternion group of order eight.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra10

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := Sum.inl 0
  let b : DiversityAtom 1 1 := Sum.inr (0, false)
  let b' : DiversityAtom 1 1 := Sum.inr (0, true)
  {(a, b, b'), (b, b, b'), (b, b, b)}

private theorem tableCode_eq : tableCode cycles = 17098160645038310433 := by decide +kernel

private theorem tableCode_encodes : EncodesTable cycles 17098160645038310433 := by
  rw [← tableCode_eq]
  exact encodesTable_tableCode cycles

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 1 1 where
  cycles := cycles
  associative := atomCompositionAssociative_of_assocCheck (by
    rw [tableCode_eq]
    decide +kernel)

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

/-- The central involution is the symmetric atom; choose one element of each inverse pair
for the forward atom, and put its inverses in the backward atom. -/
def representation : GroupAtomRepresentation table (QuaternionGroup 2) where
  label g :=
    if g = 1 then none
    else if g = QuaternionGroup.a 2 then some (Sum.inl 0)
    else some (Sum.inr (0, !(g ∈
      ({QuaternionGroup.a 1, QuaternionGroup.xa 0, QuaternionGroup.xa 1} :
        Finset (QuaternionGroup 2)))))
  surjective := by decide +kernel
  identity := by decide +kernel
  converse := by decide +kernel
  composition := by
    simp only [table, cycleClosure_iff_bitAt tableCode_encodes]
    decide +kernel

/-- This catalogue algebra has a representation on eight points. -/
theorem representable : Representable Algebra :=
  representation.representable

end Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra10
