/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles

/-!
# Catalogue algebra ⟨1, 2, 1⟩, number 576

The ⟨1, 2, 1⟩ count appears in
[Jipsen's catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
This entry uses canonical cycle mask `31686`. Our numbering orders the least masks under
atom renaming increasingly; it is independent of the source's numbering for smaller rows.
The cycle basis consists of the lexicographically least triple in each Peircean orbit,
ordered by `Atom.code`. Identity cycles are supplied by `cycleClosure`.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Ra0576

/-- The diversity cycles of this canonical representative. -/
def cycles : Finset (Cycle 2 1) :=
  let a : DiversityAtom 2 1 := .inl 0
  let b : DiversityAtom 2 1 := .inl 1
  let c : DiversityAtom 2 1 := .inr (0, false)
  let c' : DiversityAtom 2 1 := .inr (0, true)
  {(a, a, b), (a, a, c), (a, c, c), (a, c, c'), (a, c', c'), (b, b, b), (b, c, c), (b, c, c'),
    (b, c', c'), (c, c, c)}

/-- The numeric encoding used by the catalogue's classification certificate. -/
theorem tableCode_eq : tableCode cycles = 30562935523372887038869171322185060417 := by
  decide +kernel

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 2 1 where
  cycles := cycles
  associative := atomCompositionAssociative_of_assocCheck (by
    rw [tableCode_eq]
    decide +kernel)

/-- The finite relation algebra determined by this table. -/
abbrev Algebra : Type := Complex table

/-- This algebra has the signature of its catalogue row. -/
theorem signature : HasSignature Algebra 1 2 1 :=
  Complex.hasSignature table

/-- Atomic multiplication is characterized by the listed cycles and their closure. -/
theorem cycles_iff (x y z : Atom 2 1) :
    Complex.atom table z ≤ Complex.atom table x * Complex.atom table y ↔
      cycleClosure cycles x y z :=
  Complex.atom_le_mul_iff table x y z

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Ra0576
