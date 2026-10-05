/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N0.Ra01
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N0.Ra02
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N0.Ra03
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N0.Ra04
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N0.Ra05
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N0.Ra06
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N0.Ra07
public import Cslib.Foundations.RelationAlgebra.FiniteClassification

/-!
# Classification of the ⟨1, 2, 0⟩ catalogue row

This row contains 7 isomorphism classes, of which 7 are representable and
0 are nonrepresentable. See
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
`Model` uses zero-based indices: index `n` denotes source entry `n + 1`.
The unique-index classification expresses both exhaustiveness and absence of duplicates.
Four Peircean cycle orbits reduce this classification to sixteen possible cycle tables.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N0

/-- The certified cycle tables, in the source's order. -/
def table : Fin 7 → IntegralCycleTable 2 0
  | ⟨0, _⟩ => Ra01.table
  | ⟨1, _⟩ => Ra02.table
  | ⟨2, _⟩ => Ra03.table
  | ⟨3, _⟩ => Ra04.table
  | ⟨4, _⟩ => Ra05.table
  | ⟨5, _⟩ => Ra06.table
  | ⟨6, _⟩ => Ra07.table

/-- The explicitly listed algebras, indexed in the source's order. -/
abbrev Model (idx : Fin 7) : Type := Complex (table idx)

private def cycleReps : Fin 4 → Cycle 2 0
  | 0 => (.inl 0, .inl 0, .inl 0)
  | 1 => (.inl 0, .inl 0, .inl 1)
  | 2 => (.inl 0, .inl 1, .inl 1)
  | 3 => (.inl 1, .inl 1, .inl 1)

private theorem cycleReps_cover : ∀ c : Cycle 2 0,
    ∃ i, (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (cycleReps i) := by
  decide +kernel

private theorem cycles_exhaustive : ∀ bits : Fin 4 → Bool,
    AtomCompositionAssociative (selectedCycles cycleReps bits) →
      ∃ idx : Fin 7, ∃ f,
        AtomRelabelling (selectedCycles cycleReps bits) (table idx).cycles f := by
  decide +kernel

private theorem cycles_distinct : ∀ i j : Fin 7, ∀ f,
    AtomRelabelling (table i).cycles (table j).cycles f → i = j := by
  decide +kernel

private theorem model_representable (idx : Fin 7) : Representable (Model idx) := by
  rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Ra01.representable
  · exact Ra02.representable
  · exact Ra03.representable
  · exact Ra04.representable
  · exact Ra05.representable
  · exact Ra06.representable
  · exact Ra07.representable

/-- Every algebra of this signature is isomorphic to exactly one listed model. -/
theorem classification (A : Type*) [RelationAlgebra A] (h : HasSignature A 1 2 0) :
    ∃! idx : Fin 7, Nonempty (RelationAlgebraEquiv A (Model idx)) := by
  exact classification_of_cycle_basis cycleReps cycleReps_cover table
    cycles_exhaustive cycles_distinct A h

/-- The number of representable isomorphism classes in this row. -/
theorem count_representable :
    Nat.card {idx : Fin 7 // Representable (Model idx)} = 7 := by
  have he : {idx : Fin 7 // Representable (Model idx)} ≃ Fin 7 :=
    { toFun := Subtype.val
      invFun := fun idx => ⟨idx, model_representable idx⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa using Nat.card_congr he

/-- The number of nonrepresentable isomorphism classes in this row. -/
theorem count_nonrepresentable :
    Nat.card {idx : Fin 7 // ¬ Representable (Model idx)} = 0 := by
  have : IsEmpty {idx : Fin 7 // ¬ Representable (Model idx)} :=
    ⟨fun idx => idx.property (model_representable idx.val)⟩
  simp

end Cslib.RelationAlgebra.Catalogue.I1S2N0
