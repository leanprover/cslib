/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.IntegralCycles
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Small integral atom structures

We list small integral atom structures and state their classification up to equivalence.

## References

* Peter Jipsen, [*List of small integral relation algebras*](https://www1.chapman.edu/~jipsen/gap/ramaddux.html)

-/

@[expose] public section

namespace Cslib.RelationAlgebra
namespace IntegralAtom

/-- The atom structure with only the identity atom, as a singleton family. -/
def identityOnly : Fin 1 → AtomStructure (IntegralAtom 0 0) :=
  ![integral_cycles%]

/-- The two atom structures with one symmetric diversity atom. -/
def oneSymm : Fin 2 → AtomStructure (IntegralAtom 1 0) :=
  ![integral_cycles% (symm := a),
    integral_cycles% (symm := a) (a, a, a)]

/-- The three atom structures with one pair of nonsymmetric atoms. -/
def oneConv : Fin 3 → AtomStructure (IntegralAtom 0 1) :=
  ![integral_cycles% (nsymm := a) (a, a, a~),
    integral_cycles% (nsymm := a) (a, a, a),
    integral_cycles% (nsymm := a) (a, a, a~) (a, a, a)]

/-- The seven atom structures with two symmetric diversity atoms. -/
def twoSymm : Fin 7 → AtomStructure (IntegralAtom 2 0) :=
  ![integral_cycles% (symm := [a, b]) (a, b, b),
    integral_cycles% (symm := [a, b]) (a, b, b) (a, a, a),
    integral_cycles% (symm := [a, b]) (a, b, b) (b, b, b),
    integral_cycles% (symm := [a, b]) (a, b, b) (a, a, a) (b, b, b),
    integral_cycles% (symm := [a, b]) (a, a, b) (a, b, b),
    integral_cycles% (symm := [a, b]) (a, a, b) (a, b, b) (a, a, a),
    integral_cycles% (symm := [a, b]) (a, a, b) (a, b, b) (a, a, a) (b, b, b)]

/-- The 37 atom structures with one symmetric diversity atom and one pair of
nonsymmetric atoms. -/
def oneSymmOneConv : Fin 37 → AtomStructure (IntegralAtom 1 1) :=
  ![integral_cycles% (symm := a) (nsymm := b) (a, b, b~),
    integral_cycles% (symm := a) (nsymm := b) (a, b, b) (a, b~, b~) (b, b, b~),
    integral_cycles% (symm := a) (nsymm := b) (a, b, b) (a, b~, b~) (b, b, b~) (a, a, a),
    integral_cycles% (symm := a) (nsymm := b) (a, b, b) (a, b, b~) (a, b~, b~) (a, a, a),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (b, b, b~),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (b, b, b~) (a, a, a),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~)
      (a, a, a),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~)
      (b, b, b~),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~)
      (b, b, b~) (a, a, a),
    integral_cycles% (symm := a) (nsymm := b) (a, b, b~) (b, b, b~) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, b, b) (a, b~, b~) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, b, b) (a, b~, b~) (a, a, a) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, b, b) (a, b~, b~) (b, b, b~) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, b, b) (a, b~, b~) (b, b, b~) (a, a, a)
      (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, b, b) (a, b, b~) (a, b~, b~) (a, a, a)
      (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, b, b) (a, b, b~) (a, b~, b~) (b, b, b~)
      (a, a, a) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, a, a) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (b, b, b~) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (b, b, b~) (a, a, a) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b~) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b~) (a, a, a) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b~) (b, b, b~) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b~) (b, b, b~) (a, a, a) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b~, b~) (a, a, a) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b~) (a, b~, b~) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b~) (a, b~, b~) (a, a, a)
      (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b~) (a, b~, b~) (b, b, b~)
      (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b~) (a, b~, b~) (b, b, b~)
      (a, a, a) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b) (a, b~, b~) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b) (a, b~, b~) (a, a, a) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b) (a, b~, b~) (b, b, b~)
      (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b) (a, b~, b~) (b, b, b~)
      (a, a, a) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~)
      (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~)
      (a, a, a) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~)
      (b, b, b~) (b, b, b),
    integral_cycles% (symm := a) (nsymm := b) (a, a, b) (a, b, b) (a, b, b~) (a, b~, b~)
      (b, b, b~) (a, a, a) (b, b, b)]

/-- The 65 atom structures with three symmetric diversity atoms. -/
def threeSymm : Fin 65 → AtomStructure (IntegralAtom 3 0) :=
  ![integral_cycles% (symm := [a, b, c]) (a, b, c),
    integral_cycles% (symm := [a, b, c]) (a, b, c) (b, c, c) (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, b, c) (b, b, c) (b, c, c) (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, b, c) (a, c, c) (b, c, c) (a, a, a) (b, b, b)
      (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, b, c) (a, c, c) (b, b, c) (b, c, c) (a, a, a)
      (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, b, c) (a, c, c) (b, b, c) (b, c, c) (a, a, a)
      (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, c) (b, b, c) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, c) (a, c, c) (b, b, c) (b, c, c)
      (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, c) (a, c, c) (b, b, c) (b, c, c)
      (a, a, a) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, c) (a, c, c) (b, b, c) (b, c, c)
      (a, a, a) (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (a, a, a),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (a, a, a) (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (a, a, a) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, c, c) (a, a, a) (b, b, b)
      (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, b, c) (a, c, c) (b, c, c) (a, a, a)
      (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, b, c) (a, c, c) (b, c, c) (a, a, a)
      (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, b, c) (b, c, c),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, b, c) (b, c, c) (a, a, a),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, b, c) (b, c, c) (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, b, c) (b, c, c) (a, a, a)
      (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, b, c) (b, c, c) (b, b, b)
      (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, c, c) (b, b, c) (b, c, c) (a, a, a)
      (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c)
      (a, a, a),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c)
      (a, a, a) (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, b, b) (a, b, c) (a, c, c) (b, b, c) (b, c, c)
      (a, a, a) (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, c, c) (a, a, a),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, c, c) (a, a, a)
      (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, c, c) (a, a, a)
      (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c)
      (a, a, a),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c)
      (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c)
      (a, a, a) (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c)
      (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c)
      (a, a, a) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c)
      (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (b, b, c) (b, c, c)
      (a, a, a) (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, c, c) (b, b, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (a, a, a),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (a, a, a)
      (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (a, a, a)
      (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, c, c) (b, b, c) (a, a, a)
      (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
      (a, a, a) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
      (a, a, a) (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
      (b, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
      (b, c, c) (a, a, a),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
      (b, c, c) (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
      (b, c, c) (a, a, a) (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
      (b, c, c) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
      (b, c, c) (a, a, a) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
      (b, c, c) (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, c) (a, b, b) (a, b, c) (a, c, c) (b, b, c)
      (b, c, c) (a, a, a) (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, c, c) (b, b, c)
      (b, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, c, c) (b, b, c)
      (b, c, c) (a, a, a),
    integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, c, c) (b, b, c)
      (b, c, c) (a, a, a) (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, c, c) (b, b, c)
      (b, c, c) (a, a, a) (b, b, b) (c, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, b, c) (a, c, c)
      (b, b, c) (b, c, c),
    integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, b, c) (a, c, c)
      (b, b, c) (b, c, c) (a, a, a),
    integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, b, c) (a, c, c)
      (b, b, c) (b, c, c) (a, a, a) (b, b, b),
    integral_cycles% (symm := [a, b, c]) (a, a, b) (a, a, c) (a, b, b) (a, b, c) (a, c, c)
      (b, b, c) (b, c, c) (a, a, a) (b, b, b) (c, c, c)]

/-!
## Classification of finite integral relation algebras

-/

variable {α : Type*} [RelationAlgebra α] [Finite α]

/-- A finite integral relation algebra with no diversity atoms is equivalent to a unique
entry of `identityOnly`. -/
proof_wanted existsUnique_equiv_identityOnly (hIntegral : IsIntegral α)
    (hSymm : Nat.card (symmetricDiversityAtoms α) = 0)
    (hNsymm : Nat.card (nonsymmetricDiversityAtoms α) = 0) :
    ∃! i : Fin 1, Nonempty (RelationAlgebraEquiv α (ComplexAlgebra (identityOnly i)))

/-- A finite integral relation algebra with one symmetric diversity atom and no nonsymmetric
atoms is equivalent to a unique entry of `oneSymm`. -/
proof_wanted existsUnique_equiv_oneSymm (hIntegral : IsIntegral α)
    (hSymm : Nat.card (symmetricDiversityAtoms α) = 1)
    (hNsymm : Nat.card (nonsymmetricDiversityAtoms α) = 0) :
    ∃! i : Fin 2, Nonempty (RelationAlgebraEquiv α (ComplexAlgebra (oneSymm i)))

/-- A finite integral relation algebra with no symmetric diversity atoms and one converse pair
of nonsymmetric atoms is equivalent to a unique entry of `oneConv`. -/
proof_wanted existsUnique_equiv_oneConv (hIntegral : IsIntegral α)
    (hSymm : Nat.card (symmetricDiversityAtoms α) = 0)
    (hNsymm : Nat.card (nonsymmetricDiversityAtoms α) = 2) :
    ∃! i : Fin 3, Nonempty (RelationAlgebraEquiv α (ComplexAlgebra (oneConv i)))

/-- A finite integral relation algebra with two symmetric diversity atoms and no nonsymmetric
atoms is equivalent to a unique entry of `twoSymm`. -/
proof_wanted existsUnique_equiv_twoSymm (hIntegral : IsIntegral α)
    (hSymm : Nat.card (symmetricDiversityAtoms α) = 2)
    (hNsymm : Nat.card (nonsymmetricDiversityAtoms α) = 0) :
    ∃! i : Fin 7, Nonempty (RelationAlgebraEquiv α (ComplexAlgebra (twoSymm i)))

/-- A finite integral relation algebra with one symmetric diversity atom and one converse pair
of nonsymmetric atoms is equivalent to a unique entry of `oneSymmOneConv`. -/
proof_wanted existsUnique_equiv_oneSymmOneConv (hIntegral : IsIntegral α)
    (hSymm : Nat.card (symmetricDiversityAtoms α) = 1)
    (hNsymm : Nat.card (nonsymmetricDiversityAtoms α) = 2) :
    ∃! i : Fin 37, Nonempty (RelationAlgebraEquiv α (ComplexAlgebra (oneSymmOneConv i)))

/-- A finite integral relation algebra with three symmetric diversity atoms and no nonsymmetric
atoms is equivalent to a unique entry of `threeSymm`. -/
proof_wanted existsUnique_equiv_threeSymm (hIntegral : IsIntegral α)
    (hSymm : Nat.card (symmetricDiversityAtoms α) = 3)
    (hNsymm : Nat.card (nonsymmetricDiversityAtoms α) = 0) :
    ∃! i : Fin 65, Nonempty (RelationAlgebraEquiv α (ComplexAlgebra (threeSymm i)))

end IntegralAtom

end Cslib.RelationAlgebra
