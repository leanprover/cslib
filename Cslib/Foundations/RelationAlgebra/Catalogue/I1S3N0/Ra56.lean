/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.WitnessRepresentation

/-!
# Catalogue algebra ⟨1, 3, 0⟩, number 56

Entry 56 in the ⟨1, 3, 0⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aac abb abc acc bbc bcc bbb ccc`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
Representability follows by successively adding the witnesses specified by a finite policy.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra56

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 3 0) :=
  let a : DiversityAtom 3 0 := Sum.inl 0
  let b : DiversityAtom 3 0 := Sum.inl 1
  let c : DiversityAtom 3 0 := Sum.inl 2
  {(a, a, c), (a, b, b), (a, b, c), (a, c, c), (b, b, c), (b, c, c), (b, b, b), (c, c, c)}

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

/-- Numeric names for the identity and the three diversity atoms. -/
def atomCode : Atom 3 0 → ℕ
  | none => 0
  | some (.inl i) => i.val + 1
  | some (.inr (i, _)) => Fin.elim0 i

/-- Labels of new witness edges, as a function of the two endpoint labels. -/
def witnessLabel (a b c d e : Atom 3 0) : Atom 3 0 :=
  if d = none then a else if e = none then Atom.converse b else
  match atomCode a, atomCode b, atomCode c, atomCode d, atomCode e with
  | 1, 1, 3, 1, 2 => some (.inl 2)
  | 1, 1, 3, 1, 3 => some (.inl 2)
  | 1, 1, 3, 2, 1 => some (.inl 2)
  | 1, 1, 3, 3, 1 => some (.inl 2)
  | 1, 2, 2, 1, 3 => some (.inl 2)
  | 1, 2, 3, 1, 1 => some (.inl 2)
  | 1, 2, 3, 1, 3 => some (.inl 2)
  | 1, 3, 2, 1, 2 => some (.inl 2)
  | 1, 3, 3, 1, 1 => some (.inl 2)
  | 1, 3, 3, 1, 2 => some (.inl 2)
  | 2, 1, 2, 3, 1 => some (.inl 2)
  | 2, 1, 3, 1, 1 => some (.inl 2)
  | 2, 1, 3, 3, 1 => some (.inl 2)
  | 3, 1, 2, 2, 1 => some (.inl 2)
  | 3, 1, 3, 1, 1 => some (.inl 2)
  | 3, 1, 3, 2, 1 => some (.inl 2)
  | 3, 3, 0, 1, 1 => some (.inl 0)
  | 3, 3, 3, 1, 1 => some (.inl 0)
  | _, _, _, _, _ => some (.inl 1)

set_option synthInstance.maxSize 1024 in
/-- The finite extension policy for composition witnesses. -/
def witnessPolicy : WitnessPolicy table where
  label := witnessLabel
  diversity := by decide +kernel
  left := by decide +kernel
  right := by decide +kernel
  triangle := by
    have check : ∀ (a b c : Atom 3 0), a ≠ none → b ≠ none →
        cycleClosure cycles a b c → ∀ d e,
        cycleClosure cycles d (Atom.converse e) c → (d, e) ≠ (a, Atom.converse b) →
        ∀ d' e', cycleClosure cycles d' (Atom.converse e') c →
        (d', e') ≠ (a, Atom.converse b) → ∀ h,
        cycleClosure cycles d h d' → cycleClosure cycles e h e' →
        cycleClosure cycles h (witnessLabel a b c d' e') (witnessLabel a b c d e) := by
      decide +kernel
    intro a b c d e d' e' h ha hb hc hp hp' hne hne' hd he
    exact check a b c ha hb hc d e hp hne d' e' hp' hne' h hd he

/-- This catalogue algebra has a representation, with no restriction to finite bases. -/
theorem representable : Representable Algebra :=
  witnessPolicy.representable

end Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra56
