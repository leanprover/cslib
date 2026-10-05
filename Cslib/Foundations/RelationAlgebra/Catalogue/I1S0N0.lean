/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S0N0.Ra01
public import Cslib.Foundations.RelationAlgebra.Classification

/-!
# Classification of the ⟨1, 0, 0⟩ catalogue row

This row contains 1 isomorphism classes, of which 1 are representable and
0 are nonrepresentable. See
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
`Model` uses zero-based indices: index `n` denotes source entry `n + 1`.
The unique-index classification expresses both exhaustiveness and absence of duplicates.
The sole isomorphism class is representable.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S0N0

/-- The certified cycle tables, in the source's order. -/
def table : Fin 1 → IntegralCycleTable 0 0
  | ⟨0, _⟩ => Ra01.table

/-- The explicitly listed algebras, indexed in the source's order. -/
abbrev Model (idx : Fin 1) : Type := Complex (table idx)

/-- Every algebra of this signature is isomorphic to exactly one listed model. -/
theorem classification (A : Type*) [RelationAlgebra A] (h : HasSignature A 1 0 0) :
    ∃! idx : Fin 1, Nonempty (RelationAlgebraEquiv A (Model idx)) := by
  exact ⟨0, ⟨equivOfHasSignatureOne h Ra01.signature⟩, fun _ _ => Subsingleton.elim _ _⟩

/-- The number of representable isomorphism classes in this row. -/
theorem count_representable :
    Nat.card {idx : Fin 1 // Representable (Model idx)} = 1 := by
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨⟨0, Ra01.representable⟩⟩⟩

/-- The number of nonrepresentable isomorphism classes in this row. -/
theorem count_nonrepresentable :
    Nat.card {idx : Fin 1 // ¬ Representable (Model idx)} = 0 := by
  have : IsEmpty {idx : Fin 1 // ¬ Representable (Model idx)} := ⟨by
    rintro ⟨idx, hidx⟩
    have hi : idx = 0 := Subsingleton.elim _ _
    subst idx
    exact hidx Ra01.representable⟩
  simp

end Cslib.RelationAlgebra.Catalogue.I1S0N0
