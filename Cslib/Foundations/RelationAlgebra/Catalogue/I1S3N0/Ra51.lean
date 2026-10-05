/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.OrderedColorRepresentation

/-!
# Catalogue algebra ⟨1, 3, 0⟩, number 51

Entry 51 in the ⟨1, 3, 0⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aac abb abc acc bbc bcc aaa`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
Its representation uses six dense colors in a linear order.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra51

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 3 0) :=
  let a : DiversityAtom 3 0 := Sum.inl 0
  let b : DiversityAtom 3 0 := Sum.inl 1
  let c : DiversityAtom 3 0 := Sum.inl 2
  {(a, a, c), (a, b, b), (a, b, c), (a, c, c), (b, b, c), (b, c, c), (a, a, a)}

private theorem tableCode_eq : tableCode cycles = 9144818274393031713 := by decide +kernel

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

/-- Increasing pairs are labelled by three pairs of color differences modulo six. -/
def orderedColorPolicy : OrderedColorRepresentation.Policy table 6 where
  positive := by decide
  up i l :=
    let d := l - i
    if d = 0 ∨ d = 1 then 0 else if d = 3 ∨ d = 4 then 1 else 2
  diagonal := by decide +kernel
  increasing := by decide +kernel

/-- This catalogue algebra has a representation on a countable dense colored order. -/
theorem representable : Representable Algebra := orderedColorPolicy.representable

end Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra51
