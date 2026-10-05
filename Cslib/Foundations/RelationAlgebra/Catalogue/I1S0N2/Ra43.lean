/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles

/-!
# Catalogue algebra ⟨1, 0, 2⟩, number 43

Entry 43 in the ⟨1, 0, 2⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aaa~ aab~ aa~b aba abb ab~b~ bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S0N2.Ra43

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 0 2) :=
  let a : DiversityAtom 0 2 := .inr (0, false)
  let a' : DiversityAtom 0 2 := .inr (0, true)
  let b : DiversityAtom 0 2 := .inr (1, false)
  let b' : DiversityAtom 0 2 := .inr (1, true)
  {(a, a, a'), (a, a, b'), (a, a', b), (a, b, a), (a, b, b), (a, b', b'), (b, b, b)}

private theorem tableCode_eq : tableCode cycles = 22584646873774088303313482515852038209 := by
  decide +kernel

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 0 2 where
  cycles := cycles
  associative := atomCompositionAssociative_of_assocCheck (by
    rw [tableCode_eq]
    decide +kernel)

/-- The finite relation algebra determined by this table. -/
abbrev Algebra : Type := Complex table

/-- This algebra has the signature of its catalogue row. -/
theorem signature : HasSignature Algebra 1 0 2 :=
  Complex.hasSignature table

/-- Atomic multiplication is characterized exactly by the listed cycles and their closure. -/
theorem cycles_iff (x y z : Atom 0 2) :
    Complex.atom table z ≤ Complex.atom table x * Complex.atom table y ↔
      cycleClosure cycles x y z :=
  Complex.atom_le_mul_iff table x y z

end Cslib.RelationAlgebra.Catalogue.I1S0N2.Ra43
