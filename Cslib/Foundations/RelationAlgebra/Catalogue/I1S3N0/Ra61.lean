/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.FastWitnessRepresentation

/-!
# Catalogue algebra ⟨1, 3, 0⟩, number 61

Entry 61 in the ⟨1, 3, 0⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab aac abb acc bbc bcc aaa bbb ccc`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
Representability follows by successively adding the witnesses specified by a finite policy.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra61

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 3 0) :=
  let a : DiversityAtom 3 0 := Sum.inl 0
  let b : DiversityAtom 3 0 := Sum.inl 1
  let c : DiversityAtom 3 0 := Sum.inl 2
  {(a, a, b), (a, a, c), (a, b, b), (a, c, c), (b, b, c), (b, c, c), (a, a, a), (b, b, b),
    (c, c, c)}

private theorem tableCode_eq : tableCode cycles = 18206029524849820705 := by decide +kernel

private theorem tableCode_encodes : EncodesTable cycles 18206029524849820705 := by
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

/-- Numeric names for the identity and the three diversity atoms. -/
def atomCode : Atom 3 0 → ℕ
  | none => 0
  | some (.inl i) => i.val + 1
  | some (.inr (i, _)) => Fin.elim0 i

/-- Packed two-bit labels, indexed by the four remaining atom codes. -/
def witnessCode : ℕ → ℕ
  | 1 => 0xfe9555555d5965555555557da95d59d55555555555555555555555555555555555555555
  | 2 => 0xfd9579659555555555aa59bd995996ab5555555579e59dd9555555555555555555555555
  | 3 => 0x7e955dfdf5dffd5655d79d75a95555555555e79d55555d5a555555555555555555555555
  | _ => 0x555555555555555555555555555555555555555555555555555555555555555555555555

/-- The same witness labels, expressed directly on numeric atom codes. -/
def witnessLabelCode (a b c d e : ℕ) : ℕ :=
  if d = 0 then a else if e = 0 then Code.conv 3 b else
  let i := ((b * 4 + c) * 3 + (d - 1)) * 3 + (e - 1)
  Nat.land (Nat.shiftRight (witnessCode a) (2 * i)) 3

/-- Labels of new witness edges, as a function of the two endpoint labels. -/
def witnessLabel (a b c d e : Atom 3 0) : Atom 3 0 :=
  if d = none then a else if e = none then Atom.converse b else
  let i := ((atomCode b * 4 + atomCode c) * 3 + (atomCode d - 1)) * 3 +
    (atomCode e - 1)
  match Nat.land (Nat.shiftRight (witnessCode (atomCode a)) (2 * i)) 3 with
  | 1 => some (.inl 0)
  | 2 => some (.inl 1)
  | _ => some (.inl 2)

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

end Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra61
