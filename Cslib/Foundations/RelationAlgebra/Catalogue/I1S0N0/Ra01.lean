/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FiniteRepresentation

/-!
# Catalogue algebra ⟨1, 0, 0⟩, number 1

Entry 1 in the ⟨1, 0, 0⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `1'1'1'`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The representation is the full square relation algebra on a singleton base.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S0N0.Ra01

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 0 0) :=
  ∅

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 0 0 where
  cycles := cycles
  associative := by decide +kernel

/-- The finite relation algebra determined by this table. -/
abbrev Algebra : Type := Complex table

/-- This algebra has the signature of its catalogue row. -/
theorem signature : HasSignature Algebra 1 0 0 :=
  Complex.hasSignature table

/-- Atomic multiplication is characterized exactly by the listed cycles and their closure. -/
theorem cycles_iff (x y z : Atom 0 0) :
    Complex.atom table z ≤ Complex.atom table x * Complex.atom table y ↔
      cycleClosure cycles x y z :=
  Complex.atom_le_mul_iff table x y z

/-- A concrete representation on one point. -/
def representation : AtomRepresentation table (Fin 1) where
  label _ _ := none
  surjective := by decide +kernel
  identity := by decide +kernel
  converse := by decide +kernel
  composition := by decide +kernel

/-- This catalogue algebra has a representation on one point. -/
theorem representable : Representable Algebra := representation.representable

end Cslib.RelationAlgebra.Catalogue.I1S0N0.Ra01
