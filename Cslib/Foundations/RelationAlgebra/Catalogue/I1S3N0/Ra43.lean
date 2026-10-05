/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FiniteRepresentation
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic

/-!
# Catalogue algebra ⟨1, 3, 0⟩, number 43

Entry 43 in the ⟨1, 3, 0⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aac abb acc bbc aaa`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The representation below partitions the cyclic group of order 16.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra43

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 3 0) :=
  let a : DiversityAtom 3 0 := Sum.inl 0
  let b : DiversityAtom 3 0 := Sum.inl 1
  let c : DiversityAtom 3 0 := Sum.inl 2
  {(a, a, c), (a, b, b), (a, c, c), (b, b, c), (a, a, a)}

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 3 0 where
  cycles := cycles
  associative := by decide +kernel

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

/-- The nonidentity blocks modulo 16 are
`a = {2, 4, 12, 14}`,
`b = {1, 3, 5, 7, 9, 11, 13, 15}`,
and `c = {6, 8, 10}`. -/
def representation : GroupAtomRepresentation table (Multiplicative (ZMod 16)) where
  label g :=
    if g.toAdd = 0 then none
    else some (Sum.inl (if g.toAdd ∈ ({2, 4, 12, 14} : Finset (ZMod 16)) then 0
      else if g.toAdd ∈ ({1, 3, 5, 7, 9, 11, 13, 15} : Finset (ZMod 16)) then 1 else 2))
  surjective := by decide +kernel
  identity := by decide +kernel
  converse := by decide +kernel
  composition := by decide +kernel

/-- This catalogue algebra has a representation on 16 points. -/
theorem representable : Representable Algebra :=
  representation.representable

end Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra43
