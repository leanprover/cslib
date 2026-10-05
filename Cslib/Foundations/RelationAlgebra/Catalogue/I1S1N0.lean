/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N0.Ra01
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N0.Ra02

/-!
# Classification of the ⟨1, 1, 0⟩ catalogue row

This row contains 2 isomorphism classes, of which 2 are representable and
0 are nonrepresentable. See
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
`Model` uses zero-based indices: index `n` denotes source entry `n + 1`.
The unique-index classification expresses both exhaustiveness and absence of duplicates.
All classification and counting proofs are deferred.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N0

/-- The certified cycle tables, in the source's order. -/
def table : Fin 2 → IntegralCycleTable 1 0
  | ⟨0, _⟩ => Ra01.table
  | ⟨1, _⟩ => Ra02.table

/-- The explicitly listed algebras, indexed in the source's order. -/
abbrev Model (idx : Fin 2) : Type := Complex (table idx)

/-- Every algebra of this signature is isomorphic to exactly one listed model. -/
theorem classification (A : Type*) [RelationAlgebra A] (h : HasSignature A 1 1 0) :
    ∃! idx : Fin 2, Nonempty (RelationAlgebraEquiv A (Model idx)) := by
  sorry

/-- The number of representable isomorphism classes in this row. -/
theorem count_representable :
    Nat.card {idx : Fin 2 // Representable (Model idx)} = 2 := by
  sorry

/-- The number of nonrepresentable isomorphism classes in this row. -/
theorem count_nonrepresentable :
    Nat.card {idx : Fin 2 // ¬ Representable (Model idx)} = 0 := by
  sorry

end Cslib.RelationAlgebra.Catalogue.I1S1N0
