/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.OrderedRepresentation

/-!
# Catalogue algebra ⟨1, 1, 1⟩, number 17

Entry 17 in the ⟨1, 1, 1⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The algebra is represented by 2 disjoint copies of the rational order.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra17

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := Sum.inl 0
  let b : DiversityAtom 1 1 := Sum.inr (0, false)
  {(a, a, b), (b, b, b)}

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

/-- The atomic representation on the rational order and a 2-point finite fiber. -/
def representation : AtomRepresentation table (ℚ × Fin 2) :=
  OrderedRepresentation.separated false table (by decide +kernel)

/-- This catalogue algebra has a representation on an infinite rational base. -/
theorem representable : Representable Algebra :=
  representation.representable

end Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra17
