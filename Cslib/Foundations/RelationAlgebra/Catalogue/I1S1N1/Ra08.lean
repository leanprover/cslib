/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Cycles

/-!
# Catalogue algebra ⟨1, 1, 1⟩, number 8

Entry 8 in the ⟨1, 1, 1⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab abb abb~ ab~b~ bbb~`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The algebraic and classification results are stated with proofs deferred.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra08

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := Sum.inl 0
  let b : DiversityAtom 1 1 := Sum.inr (0, false)
  let b' : DiversityAtom 1 1 := Sum.inr (0, true)
  {(a, a, b), (a, b, b), (a, b, b'), (a, b', b'), (b, b, b')}

/-- The cycle table, with its associativity obligation deferred. -/
def table : IntegralCycleTable 1 1 where
  cycles := cycles
  associative := by sorry

/-- The finite relation algebra determined by this table. -/
abbrev Algebra : Type := Complex table

/-- This algebra has the signature of its catalogue row. -/
theorem signature : HasSignature Algebra 1 1 1 := by
  sorry

/-- Atomic multiplication is characterized exactly by the listed cycles and their closure. -/
theorem cycles_iff (x y z : Atom 1 1) :
    Complex.atom table z ≤ Complex.atom table x * Complex.atom table y ↔
      cycleClosure cycles x y z := by
  sorry

/-- This catalogue algebra has no representation by binary relations. -/
theorem not_representable : ¬ Representable Algebra := by
  sorry

end Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra08
