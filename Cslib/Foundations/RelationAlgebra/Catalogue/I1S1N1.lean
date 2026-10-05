/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra01
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra02
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra03
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra04
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra05
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra06
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra07
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra08
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra09
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra10
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra11
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra12
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra13
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra14
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra15
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra16
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra17
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra18
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra19
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra20
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra21
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra22
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra23
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra24
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra25
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra26
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra27
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra28
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra29
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra30
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra31
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra32
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra33
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra34
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra35
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra36
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N1.Ra37

/-!
# Classification of the ⟨1, 1, 1⟩ catalogue row

This row contains 37 isomorphism classes, of which 26 are representable and
11 are nonrepresentable. See
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
`Model` uses zero-based indices: index `n` denotes source entry `n + 1`.
The unique-index classification expresses both exhaustiveness and absence of duplicates.
All classification and counting proofs are deferred.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N1

/-- The certified cycle tables, in the source's order. -/
def table : Fin 37 → IntegralCycleTable 1 1
  | ⟨0, _⟩ => Ra01.table
  | ⟨1, _⟩ => Ra02.table
  | ⟨2, _⟩ => Ra03.table
  | ⟨3, _⟩ => Ra04.table
  | ⟨4, _⟩ => Ra05.table
  | ⟨5, _⟩ => Ra06.table
  | ⟨6, _⟩ => Ra07.table
  | ⟨7, _⟩ => Ra08.table
  | ⟨8, _⟩ => Ra09.table
  | ⟨9, _⟩ => Ra10.table
  | ⟨10, _⟩ => Ra11.table
  | ⟨11, _⟩ => Ra12.table
  | ⟨12, _⟩ => Ra13.table
  | ⟨13, _⟩ => Ra14.table
  | ⟨14, _⟩ => Ra15.table
  | ⟨15, _⟩ => Ra16.table
  | ⟨16, _⟩ => Ra17.table
  | ⟨17, _⟩ => Ra18.table
  | ⟨18, _⟩ => Ra19.table
  | ⟨19, _⟩ => Ra20.table
  | ⟨20, _⟩ => Ra21.table
  | ⟨21, _⟩ => Ra22.table
  | ⟨22, _⟩ => Ra23.table
  | ⟨23, _⟩ => Ra24.table
  | ⟨24, _⟩ => Ra25.table
  | ⟨25, _⟩ => Ra26.table
  | ⟨26, _⟩ => Ra27.table
  | ⟨27, _⟩ => Ra28.table
  | ⟨28, _⟩ => Ra29.table
  | ⟨29, _⟩ => Ra30.table
  | ⟨30, _⟩ => Ra31.table
  | ⟨31, _⟩ => Ra32.table
  | ⟨32, _⟩ => Ra33.table
  | ⟨33, _⟩ => Ra34.table
  | ⟨34, _⟩ => Ra35.table
  | ⟨35, _⟩ => Ra36.table
  | ⟨36, _⟩ => Ra37.table
  | ⟨n + 37, h⟩ => False.elim (by omega)

/-- The explicitly listed algebras, indexed in the source's order. -/
abbrev Model (idx : Fin 37) : Type := Complex (table idx)

/-- Every algebra of this signature is isomorphic to exactly one listed model. -/
theorem classification (A : Type*) [RelationAlgebra A] (h : HasSignature A 1 1 1) :
    ∃! idx : Fin 37, Nonempty (RelationAlgebraEquiv A (Model idx)) := by
  sorry

/-- The number of representable isomorphism classes in this row. -/
theorem count_representable :
    Nat.card {idx : Fin 37 // Representable (Model idx)} = 26 := by
  sorry

/-- The number of nonrepresentable isomorphism classes in this row. -/
theorem count_nonrepresentable :
    Nat.card {idx : Fin 37 // ¬ Representable (Model idx)} = 11 := by
  sorry

end Cslib.RelationAlgebra.Catalogue.I1S1N1
