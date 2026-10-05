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
# Catalogue algebra ⟨1, 3, 0⟩, number 23

Entry 23 in the ⟨1, 3, 0⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `abb acc bbc bcc bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The representation below partitions the cyclic group of order 16.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra23

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 3 0) :=
  let a : DiversityAtom 3 0 := Sum.inl 0
  let b : DiversityAtom 3 0 := Sum.inl 1
  let c : DiversityAtom 3 0 := Sum.inl 2
  {(a, b, b), (a, c, c), (b, b, c), (b, c, c), (b, b, b)}

private theorem tableCode_eq : tableCode cycles = 8973650150716245025 := by decide +kernel

private theorem tableCode_encodes : EncodesTable cycles 8973650150716245025 := by
  rw [← tableCode_eq]
  exact encodesTable_tableCode cycles

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 3 0 where
  cycles := cycles
  associative := atomCompositionAssociative_of_assocCheck (by
    rw [tableCode_eq]
    decide +kernel)

/-- The finite relation algebra determined by this table. -/
abbrev Algebra : Type := Complex table

/-- This algebra has the signature of its catalogue row. -/
theorem signature : HasSignature Algebra 1 3 0 :=
  Complex.hasSignature table

/-- Atomic multiplication is characterized exactly by the listed cycles and their closure. -/
theorem cycles_iff (x y z : Atom 3 0) :
    Complex.atom table z ≤ Complex.atom table x * Complex.atom table y ↔
      cycleClosure cycles x y z :=
  Complex.atom_le_mul_iff table x y z

/-- The nonidentity blocks modulo 16 are
`a = {8}`,
`b = {1, 2, 6, 7, 9, 10, 14, 15}`,
and `c = {3, 4, 5, 11, 12, 13}`. -/
def representation : GroupAtomRepresentation table (Multiplicative (ZMod 16)) where
  label g :=
    if g.toAdd = 0 then none
    else some (Sum.inl (if g.toAdd ∈ ({8} : Finset (ZMod 16)) then 0
      else if g.toAdd ∈ ({1, 2, 6, 7, 9, 10, 14, 15} : Finset (ZMod 16)) then 1 else 2))
  surjective := by decide +kernel
  identity := by decide +kernel
  converse := by decide +kernel
  composition := by
    simp only [table, cycleClosure_iff_bitAt tableCode_encodes]
    decide +kernel

/-- This catalogue algebra has a representation on 16 points. -/
theorem representable : Representable Algebra :=
  representation.representable

end Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra23
