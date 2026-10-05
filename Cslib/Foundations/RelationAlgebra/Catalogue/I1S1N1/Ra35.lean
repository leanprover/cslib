/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.WitnessRepresentation

/-!
# Catalogue algebra ⟨1, 1, 1⟩, number 35

Entry 35 in the ⟨1, 1, 1⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab abb abb~ ab~b~ aaa bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
Representability follows by successively adding the witnesses specified by a finite policy.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra35

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := Sum.inl 0
  let b : DiversityAtom 1 1 := Sum.inr (0, false)
  let b' : DiversityAtom 1 1 := Sum.inr (0, true)
  {(a, a, b), (a, b, b), (a, b, b'), (a, b', b'), (a, a, a), (b, b, b)}

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

/-- Labels of new witness edges, as a function of the two endpoint labels. -/
def witnessLabel (a b _c d e : Atom 1 1) : Atom 1 1 :=
  if d = none then a else if e = none then Atom.converse b else some (.inl 0)

set_option synthInstance.maxSize 1024 in
/-- The finite extension policy for composition witnesses. -/
def witnessPolicy : WitnessPolicy table where
  label := witnessLabel
  diversity := by decide +kernel
  left := by decide +kernel
  right := by decide +kernel
  triangle := by
    have check : ∀ (a b c : Atom 1 1), a ≠ none → b ≠ none →
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

end Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra35
