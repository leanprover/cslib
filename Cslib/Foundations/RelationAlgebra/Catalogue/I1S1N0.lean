/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N0.Ra01
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S1N0.Ra02
public import Cslib.Foundations.RelationAlgebra.Classification

/-!
# Classification of the ⟨1, 1, 0⟩ catalogue row

This row contains 2 isomorphism classes, of which 2 are representable and
0 are nonrepresentable. See
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
`Model` uses zero-based indices: index `n` denotes source entry `n + 1`.
The unique-index classification expresses both exhaustiveness and absence of duplicates.
The two algebras are distinguished by whether the diversity atom squares to identity or top.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N0

/-- The certified cycle tables, in the source's order. -/
def table : Fin 2 → IntegralCycleTable 1 0
  | ⟨0, _⟩ => Ra01.table
  | ⟨1, _⟩ => Ra02.table

/-- The explicitly listed algebras, indexed in the source's order. -/
abbrev Model (idx : Fin 2) : Type := Complex (table idx)

private theorem first_diversity_sq : (1 : Model 0)ᶜ * (1 : Model 0)ᶜ = 1 := by
  decide +kernel

private theorem second_diversity_sq_ne_one : (1 : Model 1)ᶜ * (1 : Model 1)ᶜ ≠ 1 := by
  decide +kernel

private theorem model_representable (idx : Fin 2) : Representable (Model idx) := by
  rcases (show idx = 0 ∨ idx = 1 by omega) with rfl | rfl
  · exact Ra01.representable
  · exact Ra02.representable

/-- Every algebra of this signature is isomorphic to exactly one listed model. -/
theorem classification (A : Type*) [RelationAlgebra A] (h : HasSignature A 1 1 0) :
    ∃! idx : Fin 2, Nonempty (RelationAlgebraEquiv A (Model idx)) := by
  by_cases hsq : (1 : A)ᶜ * (1 : A)ᶜ = 1
  · refine ⟨0, ⟨equivOfHasSignatureOneOne h Ra01.signature
      (iff_of_true hsq first_diversity_sq)⟩, ?_⟩
    rintro idx ⟨e⟩
    have he := (diversity_sq_eq_one_iff e).mp hsq
    rcases (show idx = 0 ∨ idx = 1 by omega) with rfl | rfl
    · rfl
    · exact (second_diversity_sq_ne_one he).elim
  · refine ⟨1, ⟨equivOfHasSignatureOneOne h Ra02.signature
      (iff_of_false hsq second_diversity_sq_ne_one)⟩, ?_⟩
    rintro idx ⟨e⟩
    rcases (show idx = 0 ∨ idx = 1 by omega) with rfl | rfl
    · exact (hsq ((diversity_sq_eq_one_iff e).mpr first_diversity_sq)).elim
    · rfl

/-- The number of representable isomorphism classes in this row. -/
theorem count_representable :
    Nat.card {idx : Fin 2 // Representable (Model idx)} = 2 := by
  have he : {idx : Fin 2 // Representable (Model idx)} ≃ Fin 2 :=
    { toFun := Subtype.val
      invFun := fun idx => ⟨idx, model_representable idx⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa using Nat.card_congr he

/-- The number of nonrepresentable isomorphism classes in this row. -/
theorem count_nonrepresentable :
    Nat.card {idx : Fin 2 // ¬ Representable (Model idx)} = 0 := by
  have : IsEmpty {idx : Fin 2 // ¬ Representable (Model idx)} :=
    ⟨fun idx => idx.property (model_representable idx.val)⟩
  simp

end Cslib.RelationAlgebra.Catalogue.I1S1N0
