/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastGroupRepresentation
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic

/-!
# Catalogue algebra ⟨1, 3, 0⟩, number 64

Entry 64 in the ⟨1, 3, 0⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab aac abb abc acc bbc bcc aaa bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The representation below partitions the cyclic group of order 25.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra64

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 3 0) :=
  let a : DiversityAtom 3 0 := Sum.inl 0
  let b : DiversityAtom 3 0 := Sum.inl 1
  let c : DiversityAtom 3 0 := Sum.inl 2
  {(a, a, b), (a, a, c), (a, b, b), (a, b, c), (a, c, c), (b, b, c), (b, c, c), (a, a, a),
    (b, b, b)}

private theorem tableCode_eq : tableCode cycles = 9144822809916245025 := by decide +kernel

private theorem tableCode_encodes : EncodesTable cycles 9144822809916245025 := by
  rw [← tableCode_eq]
  exact encodesTable_tableCode cycles

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

/-- The nonidentity blocks modulo 25 are
`a = {1, 2, 6, 8, 17, 19, 23, 24}`,
`b = {3, 7, 9, 10, 15, 16, 18, 22}`,
and `c = {4, 5, 11, 12, 13, 14, 20, 21}`. -/
def groupLabel (g : Multiplicative (ZMod 25)) : Atom 3 0 :=
  if g.toAdd = 0 then none
  else some (Sum.inl (if g.toAdd ∈ ({1, 2, 6, 8, 17, 19, 23, 24} : Finset (ZMod 25)) then 0
    else if g.toAdd ∈ ({3, 7, 9, 10, 15, 16, 18, 22} : Finset (ZMod 25)) then 1 else 2))

private theorem groupLabel_code (g : Multiplicative (ZMod 25)) :
    (groupLabel g).code = Code.field 403962073816980 (Nat.mul g.toAdd.val 2) 2 := by
  revert g
  decide +kernel

/-- The group partition with the prescribed atomic products. -/
def representation : GroupAtomRepresentation table (Multiplicative (ZMod 25)) where
  label := groupLabel
  surjective := by decide +kernel
  identity := by decide +kernel
  converse := by decide +kernel
  composition := by
    apply zmodComposition_of_check tableCode_encodes
    simp only [Code.groupCompositionCheck, Code.groupFactorMask, groupLabel_code]
    decide +kernel

/-- This catalogue algebra has a representation on 25 points. -/
theorem representable : Representable Algebra :=
  representation.representable

end Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra64
