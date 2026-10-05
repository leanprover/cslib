/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.FastWitnessRepresentation

/-!
# Catalogue algebra ⟨1, 1, 1⟩, number 25

Entry 25 in the ⟨1, 1, 1⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab ab~b~ aaa bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
Representability follows by successively adding the witnesses specified by a finite policy.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra25

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := Sum.inl 0
  let b : DiversityAtom 1 1 := Sum.inr (0, false)
  let b' : DiversityAtom 1 1 := Sum.inr (0, true)
  {(a, a, b), (a, b', b'), (a, a, a), (b, b, b)}

private theorem tableCode_eq : tableCode cycles = 10315728475187741729 := by decide +kernel

private theorem tableCode_encodes : EncodesTable cycles 10315728475187741729 := by
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

/-- Numeric names for the identity and the three diversity atoms. -/
def atomCode : Atom 1 1 → ℕ
  | none => 0
  | some (.inl _) => 1
  | some (.inr (_, false)) => 2
  | some (.inr (_, true)) => 3

/-- Packed two-bit labels, indexed by the four remaining atom codes. -/
def witnessCode : ℕ → ℕ
  | 1 => 0x955555555955955555555555555955755555555555555555555555555555555555555555
  | 2 => 0xa55565955555565555555565755555555555555565555995555555555555555555555555
  | 3 => 0x95d55555555555555575d755fd55d7fd5755555555555957555555555555555555555555
  | _ => 0x555555555555555555555555555555555555555555555555555555555555555555555555

/-- The same witness labels, expressed directly on numeric atom codes. -/
def witnessLabelCode (a b c d e : ℕ) : ℕ :=
  if d = 0 then a else if e = 0 then Code.conv 1 b else
  let i := ((b * 4 + c) * 3 + (d - 1)) * 3 + (e - 1)
  Nat.land (Nat.shiftRight (witnessCode a) (2 * i)) 3

/-- Labels of new witness edges, as a function of the two endpoint labels. -/
def witnessLabel (a b c d e : Atom 1 1) : Atom 1 1 :=
  if d = none then a else if e = none then Atom.converse b else
  let i := ((atomCode b * 4 + atomCode c) * 3 + (atomCode d - 1)) * 3 +
    (atomCode e - 1)
  match Nat.land (Nat.shiftRight (witnessCode (atomCode a)) (2 * i)) 3 with
  | 1 => some (.inl 0)
  | 2 => some (.inr (0, false))
  | _ => some (.inr (0, true))

set_option synthInstance.maxSize 1024 in
/-- The finite extension policy for composition witnesses. -/
def witnessPolicy : WitnessPolicy table where
  label := witnessLabel
  diversity := by decide +kernel
  left := by
    simp only [table, cycleClosure_iff_bitAt tableCode_encodes]
    decide +kernel
  right := by
    simp only [table, cycleClosure_iff_bitAt tableCode_encodes]
    decide +kernel
  triangle := by
    exact witnessTriangle_of_check tableCode_encodes witnessLabel witnessLabelCode
      (by decide +kernel) (by decide +kernel)

/-- This catalogue algebra has a representation, with no restriction to finite bases. -/
theorem representable : Representable Algebra :=
  witnessPolicy.representable

end Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra25
