/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.FiniteRepresentation

/-!
# Catalogue algebra ⟨1, 1, 0⟩, number 1

Entry 1 in the ⟨1, 1, 0⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `1'1'1' aa1'`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The representation below uses equality and disequality on two points.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N0.Ra01

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 1 0) :=
  ∅

private theorem tableCode_eq : tableCode cycles = 105 := by decide +kernel

private theorem tableCode_encodes : EncodesTable cycles 105 := by
  rw [← tableCode_eq]
  exact encodesTable_tableCode cycles

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 1 0 where
  cycles := cycles
  associative := atomCompositionAssociative_of_assocCheck (by
    rw [tableCode_eq]
    decide +kernel)

/-- The finite relation algebra determined by this table. -/
abbrev Algebra : Type := Complex table

/-- This algebra has the signature of its catalogue row. -/
theorem signature : HasSignature Algebra 1 1 0 :=
  Complex.hasSignature table

/-- Atomic multiplication is characterized exactly by the listed cycles and their closure. -/
theorem cycles_iff (x y z : Atom 1 0) :
    Complex.atom table z ≤ Complex.atom table x * Complex.atom table y ↔
      cycleClosure cycles x y z :=
  Complex.atom_le_mul_iff table x y z

/-- Label the diagonal by identity and all other edges by the diversity atom. -/
def representation : AtomRepresentation table (Fin 2) where
  label x y := if x = y then none else some (Sum.inl 0)
  surjective := by decide +kernel
  identity := by decide +kernel
  converse := by decide +kernel
  composition := by
    simp only [table, cycleClosure_iff_bitAt tableCode_encodes]
    decide +kernel

/-- This catalogue algebra has a representation on two points. -/
theorem representable : Representable Algebra :=
  representation.representable

end Cslib.RelationAlgebra.Catalogue.I1S1N0.Ra01
