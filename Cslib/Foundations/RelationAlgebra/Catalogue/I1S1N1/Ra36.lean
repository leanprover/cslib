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
# Catalogue algebra ⟨1, 1, 1⟩, number 36

Entry 36 in the ⟨1, 1, 1⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab abb abb~ ab~b~ bbb~ bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The representation below partitions the cyclic group of order 21.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra36

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := Sum.inl 0
  let b : DiversityAtom 1 1 := Sum.inr (0, false)
  let b' : DiversityAtom 1 1 := Sum.inr (0, true)
  {(a, a, b), (a, b, b), (a, b, b'), (a, b', b'), (b, b, b'), (b, b, b)}

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

/-- The nonidentity blocks are `a = {1, 3, 8, 13, 18, 20}`, `b = {4, 11, 12, 14, 15, 16, 19}`,
and the converse block `b~ = {2, 5, 6, 7, 9, 10, 17}` modulo 21. -/
def representation : GroupAtomRepresentation table (Multiplicative (ZMod 21)) where
  label g :=
    if g.toAdd = 0 then none
    else if g.toAdd ∈ ({1, 3, 8, 13, 18, 20} : Finset (ZMod 21)) then some (Sum.inl 0)
    else some (Sum.inr (0, !(g.toAdd ∈ ({4, 11, 12, 14, 15, 16, 19} : Finset (ZMod 21)))))
  surjective := by decide +kernel
  identity := by decide +kernel
  converse := by decide +kernel
  composition := by decide +kernel

/-- This catalogue algebra has a representation on 21 points. -/
theorem representable : Representable Algebra :=
  representation.representable

end Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra36
