/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.FiniteRepresentation
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic

/-!
# Catalogue algebra ⟨1, 1, 1⟩, number 37

Entry 37 in the ⟨1, 1, 1⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab abb abb~ ab~b~ bbb~ aaa bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The representation below partitions the product group `ZMod 3 × ZMod 3 × ZMod 3`.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra37

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := Sum.inl 0
  let b : DiversityAtom 1 1 := Sum.inr (0, false)
  let b' : DiversityAtom 1 1 := Sum.inr (0, true)
  {(a, a, b), (a, b, b), (a, b, b'), (a, b', b'), (b, b, b'), (a, a, a), (b, b, b)}

private theorem tableCode_eq : tableCode cycles = 17287347428876518433 := by decide +kernel

private theorem tableCode_encodes : EncodesTable cycles 17287347428876518433 := by
  rw [← tableCode_eq]
  exact encodesTable_tableCode cycles

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

/-- An explicit partition of the product group; inversion exchanges the two directed blocks. -/
def representation : GroupAtomRepresentation table (Multiplicative (ZMod 3 × ZMod 3 × ZMod 3)) where
  label g :=
    if g.toAdd = 0 then none
    else if g.toAdd ∈ ({(0, 0, 1), (0, 0, 2), (0, 1, 0), (0, 2, 0),
      (1, 0, 0), (2, 0, 0), (1, 1, 1), (2, 2, 2)} :
        Finset (ZMod 3 × ZMod 3 × ZMod 3)) then some (Sum.inl 0)
    else some (Sum.inr (0, !(g.toAdd ∈ ({(0, 1, 1), (0, 1, 2), (1, 0, 1), (1, 0, 2),
      (1, 1, 0), (2, 2, 1), (1, 2, 0), (2, 1, 2),
      (2, 1, 1)} :
        Finset (ZMod 3 × ZMod 3 × ZMod 3)))))
  surjective := by decide +kernel
  identity := by decide +kernel
  converse := by decide +kernel
  composition := by
    simp only [table, cycleClosure_iff_bitAt tableCode_encodes]
    decide +kernel

/-- This catalogue algebra has a representation on 27 points. -/
theorem representable : Representable Algebra :=
  representation.representable

end Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra37
