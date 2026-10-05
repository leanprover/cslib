/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.FiniteRepresentation
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic

/-!
# Catalogue algebra ⟨1, 2, 0⟩, number 1

Entry 1 in the ⟨1, 2, 0⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `abb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The representation below partitions the cyclic group of order four.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N0.Ra01

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 2 0) :=
  let a : DiversityAtom 2 0 := Sum.inl 0
  let b : DiversityAtom 2 0 := Sum.inl 1
  {(a, b, b)}

private theorem tableCode_eq : tableCode cycles = 59905297 := by decide +kernel

private theorem tableCode_encodes : EncodesTable cycles 59905297 := by
  rw [← tableCode_eq]
  exact encodesTable_tableCode cycles

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 2 0 where
  cycles := cycles
  associative := atomCompositionAssociative_of_assocCheck (by
    rw [tableCode_eq]
    decide +kernel)

/-- The finite relation algebra determined by this table. -/
abbrev Algebra : Type := Complex table

/-- This algebra has the signature of its catalogue row. -/
theorem signature : HasSignature Algebra 1 2 0 :=
  Complex.hasSignature table

/-- Atomic multiplication is characterized exactly by the listed cycles and their closure. -/
theorem cycles_iff (x y z : Atom 2 0) :
    Complex.atom table z ≤ Complex.atom table x * Complex.atom table y ↔
      cycleClosure cycles x y z :=
  Complex.atom_le_mul_iff table x y z

/-- The blocks are identity, `a = {2}`, and `b = {1, 3}` modulo four. -/
def representation : GroupAtomRepresentation table (Multiplicative (ZMod 4)) where
  label g := if g.toAdd = 0 then none else some (Sum.inl (if g.toAdd = 2 then 0 else 1))
  surjective := by decide +kernel
  identity := by decide +kernel
  converse := by decide +kernel
  composition := by
    simp only [table, cycleClosure_iff_bitAt tableCode_encodes]
    decide +kernel

/-- This catalogue algebra has a representation on four points. -/
theorem representable : Representable Algebra :=
  representation.representable

end Cslib.RelationAlgebra.Catalogue.I1S2N0.Ra01
