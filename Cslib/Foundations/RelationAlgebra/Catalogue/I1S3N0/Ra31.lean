/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.NetworkRefutation

/-!
# Catalogue algebra ⟨1, 3, 0⟩, number 31

Entry 31 in the ⟨1, 3, 0⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aac abb abc bcc aaa`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
A checked finite-network obstruction proves that no representation exists.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra31

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 3 0) :=
  let a : DiversityAtom 3 0 := Sum.inl 0
  let b : DiversityAtom 3 0 := Sum.inl 1
  let c : DiversityAtom 3 0 := Sum.inl 2
  {(a, a, c), (a, b, b), (a, b, c), (b, c, c), (a, a, a)}

private theorem tableCode_eq : tableCode cycles = 6514636925023978529 := by decide +kernel

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

/-- A finite tree of impossible composition-witness extensions. -/
def obstruction : NetworkRefutation.Certificate 3 0 :=
  let a : Atom 3 0 := some (.inl 0)
  let b : Atom 3 0 := some (.inl 1)
  let c : Atom 3 0 := some (.inl 2)
  .node 0 1 a a [
    .node 0 1 a c [
      .node 0 1 c b []]]

/-- This catalogue algebra has no representation by binary relations. -/
theorem not_representable : ¬ Representable Algebra :=
  NetworkRefutation.not_representable table (some (.inl 0)) obstruction (by decide +kernel)

end Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra31
