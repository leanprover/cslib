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
# Catalogue algebra ⟨1, 1, 1⟩, number 19

Entry 19 in the ⟨1, 1, 1⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab bbb~ bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
The representation below partitions the cyclic group of order 14.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra19

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := Sum.inl 0
  let b : DiversityAtom 1 1 := Sum.inr (0, false)
  let b' : DiversityAtom 1 1 := Sum.inr (0, true)
  {(a, a, b), (b, b, b'), (b, b, b)}

private theorem tableCode_eq : tableCode cycles = 14783307824604808225 := by decide +kernel

private theorem tableCode_encodes : EncodesTable cycles 14783307824604808225 := by
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

/-- The nonidentity blocks are `a = {1, 3, 5, 7, 9, 11, 13}`, `b = {2, 4, 8}`,
and the converse block `b~ = {6, 10, 12}` modulo 14. -/
def groupLabel (g : Multiplicative (ZMod 14)) : Atom 1 1 :=
  if g.toAdd = 0 then none
  else if g.toAdd ∈ ({1, 3, 5, 7, 9, 11, 13} : Finset (ZMod 14)) then some (Sum.inl 0)
  else some (Sum.inr (0, !(g.toAdd ∈ ({2, 4, 8} : Finset (ZMod 14)))))

private theorem groupLabel_code (g : Multiplicative (ZMod 14)) :
    (groupLabel g).code = Code.field 125204068 (Nat.mul g.toAdd.val 2) 2 := by
  revert g
  decide +kernel

/-- The group partition with the prescribed atomic products. -/
def representation : GroupAtomRepresentation table (Multiplicative (ZMod 14)) where
  label := groupLabel
  surjective := by decide +kernel
  identity := by decide +kernel
  converse := by decide +kernel
  composition := by
    apply zmodComposition_of_check tableCode_encodes
    simp only [Code.groupCompositionCheck, Code.groupFactorMask, groupLabel_code]
    decide +kernel

/-- This catalogue algebra has a representation on 14 points. -/
theorem representable : Representable Algebra :=
  representation.representable

end Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra19
