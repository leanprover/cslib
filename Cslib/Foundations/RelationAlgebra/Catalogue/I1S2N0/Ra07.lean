/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Cycles

/-!
# Catalogue algebra ⟨1, 2, 0⟩, number 7

Entry 7 in the ⟨1, 2, 0⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab abb aaa bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The algebraic and classification results are stated with proofs deferred.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N0.Ra07

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 2 0) :=
  let a : DiversityAtom 2 0 := Sum.inl 0
  let b : DiversityAtom 2 0 := Sum.inl 1
  {(a, a, b), (a, b, b), (a, a, a), (b, b, b)}

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 2 0 where
  cycles := cycles
  associative := by decide +kernel

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

/-- This catalogue algebra has a representation, with no restriction to finite bases. -/
theorem representable : Representable Algebra := by
  sorry

end Cslib.RelationAlgebra.Catalogue.I1S2N0.Ra07
