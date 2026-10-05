/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.NetworkRefutation

/-!
# Catalogue algebra ⟨1, 1, 1⟩, number 26

Entry 26 in the ⟨1, 1, 1⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab abb~ ab~b~ bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
A checked finite-network obstruction proves that no representation exists.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra26

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := Sum.inl 0
  let b : DiversityAtom 1 1 := Sum.inr (0, false)
  let b' : DiversityAtom 1 1 := Sum.inr (0, true)
  {(a, a, b), (a, b, b'), (a, b', b'), (b, b, b)}

private theorem tableCode_eq : tableCode cycles = 12639588632895849505 := by decide +kernel

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 1 1 where
  cycles := cycles
  associative := atomCompositionAssociative_of_assocCheck (by
    rw [tableCode_eq]
    decide +kernel)

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

/-- A finite tree of impossible composition-witness extensions. -/
def obstruction : NetworkRefutation.Certificate 1 1 :=
  let a : Atom 1 1 := some (.inl 0)
  let b : Atom 1 1 := some (.inr (0, false))
  let b' : Atom 1 1 := some (.inr (0, true))
  .node 0 1 a b [
    .node 0 1 a b' [
      .node 0 2 a b [
        .node 0 3 a b' [
          .node 2 4 a b [
            .node 0 6 b a [],
            .node 0 6 b a []]]]]]

/-- This catalogue algebra has no representation by binary relations. -/
theorem not_representable : ¬ Representable Algebra :=
  NetworkRefutation.not_representable table (some (.inl 0)) obstruction (by
    rw [NetworkRefutation.check_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel)

end Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra26
