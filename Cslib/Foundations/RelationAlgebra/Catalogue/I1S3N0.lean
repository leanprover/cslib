/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra01
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra02
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra03
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra04
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra05
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra06
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra07
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra08
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra09
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra10
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra11
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra12
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra13
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra14
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra15
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra16
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra17
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra18
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra19
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra20
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra21
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra22
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra23
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra24
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra25
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra26
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra27
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra28
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra29
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra30
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra31
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra32
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra33
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra34
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra35
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra36
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra37
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra38
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra39
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra40
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra41
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra42
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra43
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra44
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra45
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra46
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra47
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra48
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra49
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra50
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra51
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra52
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra53
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra54
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra55
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra56
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra57
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra58
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra59
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra60
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra61
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra62
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra63
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra64
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S3N0.Ra65

/-!
# Classification of the ⟨1, 3, 0⟩ catalogue row

This row contains 65 isomorphism classes, of which 45 are representable and
20 are nonrepresentable. See
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
`Model` uses zero-based indices: index `n` denotes source entry `n + 1`.
The unique-index classification expresses both exhaustiveness and absence of duplicates.
All classification and counting proofs are deferred.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S3N0

/-- The certified cycle tables, in the source's order. -/
def table : Fin 65 → IntegralCycleTable 3 0
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
  | ⟨37, _⟩ => Ra38.table
  | ⟨38, _⟩ => Ra39.table
  | ⟨39, _⟩ => Ra40.table
  | ⟨40, _⟩ => Ra41.table
  | ⟨41, _⟩ => Ra42.table
  | ⟨42, _⟩ => Ra43.table
  | ⟨43, _⟩ => Ra44.table
  | ⟨44, _⟩ => Ra45.table
  | ⟨45, _⟩ => Ra46.table
  | ⟨46, _⟩ => Ra47.table
  | ⟨47, _⟩ => Ra48.table
  | ⟨48, _⟩ => Ra49.table
  | ⟨49, _⟩ => Ra50.table
  | ⟨50, _⟩ => Ra51.table
  | ⟨51, _⟩ => Ra52.table
  | ⟨52, _⟩ => Ra53.table
  | ⟨53, _⟩ => Ra54.table
  | ⟨54, _⟩ => Ra55.table
  | ⟨55, _⟩ => Ra56.table
  | ⟨56, _⟩ => Ra57.table
  | ⟨57, _⟩ => Ra58.table
  | ⟨58, _⟩ => Ra59.table
  | ⟨59, _⟩ => Ra60.table
  | ⟨60, _⟩ => Ra61.table
  | ⟨61, _⟩ => Ra62.table
  | ⟨62, _⟩ => Ra63.table
  | ⟨63, _⟩ => Ra64.table
  | ⟨64, _⟩ => Ra65.table
  | ⟨n + 65, h⟩ => False.elim (by omega)

/-- The explicitly listed algebras, indexed in the source's order. -/
abbrev Model (idx : Fin 65) : Type := Complex (table idx)

/-- Every algebra of this signature is isomorphic to exactly one listed model. -/
theorem classification (A : Type*) [RelationAlgebra A] (h : HasSignature A 1 3 0) :
    ∃! idx : Fin 65, Nonempty (RelationAlgebraEquiv A (Model idx)) := by
  sorry

/-- The number of representable isomorphism classes in this row. -/
theorem count_representable :
    Nat.card {idx : Fin 65 // Representable (Model idx)} = 45 := by
  sorry

/-- The number of nonrepresentable isomorphism classes in this row. -/
theorem count_nonrepresentable :
    Nat.card {idx : Fin 65 // ¬ Representable (Model idx)} = 20 := by
  sorry

end Cslib.RelationAlgebra.Catalogue.I1S3N0
