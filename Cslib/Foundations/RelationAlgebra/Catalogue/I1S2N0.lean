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
public import Cslib.Foundations.RelationAlgebra.FastClassification

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

private def classificationWitness : ℕ → Fin 7 × Fin 2
  | 2 => (0, 1)
  | 3 => (2, 1)
  | 4 => (0, 0)
  | 5 => (1, 0)
  | 6 => (4, 0)
  | 7 => (5, 0)
  | 10 => (1, 1)
  | 11 => (3, 1)
  | 12 => (2, 0)
  | 13 => (3, 0)
  | 14 => (5, 1)
  | 15 => (6, 0)
  | _ => (0, 0)

private def modelCode : Fin 7 → ℕ
  | 0 => 59905297
  | 1 => 59913489
  | 2 => 127014161
  | 3 => 127022353
  | 4 => 64181521
  | 5 => 64189713
  | 6 => 131298577

private theorem modelCode_eq : ∀ idx, tableCode (table idx).cycles = modelCode idx := by
  decide +kernel

private theorem modelCode_encodes (idx : Fin 7) :
    EncodesTable (table idx).cycles (modelCode idx) := by
  rw [← modelCode_eq]
  exact encodesTable_tableCode _

private def rename (p : Fin 2) : Atom 2 0 → Atom 2 0
  | none => none
  | some (.inl i) => some (.inl (if p.val = 0 then i else if i = 0 then 1 else 0))
  | some (.inr (i, _)) => Fin.elim0 i

private def renameCodes (p : Fin 2) (x : ℕ) : ℕ :=
  cond (Nat.beq p.val 0) x (cond (Nat.beq x 0) 0 (Nat.sub 3 x))

private theorem renames_code : ∀ p x, (rename p x).code = renameCodes p x.code := by
  decide +kernel

private theorem renames_laws : ∀ p, Function.Injective (rename p) ∧ rename p none = none ∧
    ∀ x, rename p x.converse = (rename p x).converse := by
  unfold Function.Injective
  decide +kernel

private theorem cycles_exhaustive : ∀ bits : Fin 4 → Bool,
    AtomCompositionAssociative (selectedCycles cycleReps bits) →
      ∃ idx : Fin 7, ∃ f,
        AtomRelabelling (selectedCycles cycleReps bits) (table idx).cycles f :=
  cycles_exhaustive_of_check cycleReps table modelCode modelCode_encodes
    rename renameCodes renames_code renames_laws classificationWitness (by decide +kernel)

private theorem renamings_exhaustive : ∀ f : Atom 2 0 → Atom 2 0,
    Function.Injective f → f none = none →
      (∀ x, f x.converse = (f x).converse) → ∃ p : Fin 2, f = rename p := by
  unfold Function.Injective
  decide +kernel

private theorem rename_zero : ∀ x, rename 0 x = x := by
  decide +kernel

private def profileCode : Fin 7 → Fin 2 → ℕ
  | 0, 0 => 4
  | 0, 1 => 2
  | 1, 0 => 5
  | 1, 1 => 10
  | 2, 0 => 12
  | 2, 1 => 3
  | 3, 0 => 13
  | 3, 1 => 11
  | 4, 0 => 6
  | 4, 1 => 6
  | 5, 0 => 7
  | 5, 1 => 14
  | 6, 0 => 15
  | 6, 1 => 15

private theorem profileCode_eq : ∀ idx : Fin 7, ∀ p : Fin 2,
    choiceMask (fun c => decide (cycleClosure (table idx).cycles
      (rename p (some (cycleReps c).1)) (rename p (some (cycleReps c).2.1))
      (rename p (some (cycleReps c).2.2)))) = profileCode idx p := by
  simp only [cycleClosure_iff_bitAt (modelCode_encodes _), Bool.decide_eq_true, renames_code]
  decide +kernel

private theorem profileCode_injective : ∀ i j : Fin 7, ∀ p : Fin 2,
    profileCode i 0 = profileCode j p → i = j := by
  decide +kernel

private theorem cycles_distinct : ∀ i j : Fin 7, ∀ f,
    AtomRelabelling (table i).cycles (table j).cycles f → i = j := by
  intro i j f hf
  obtain ⟨p, rfl⟩ := renamings_exhaustive f hf.1 hf.2.1 hf.2.2.1
  apply profileCode_injective i j p
  rw [← profileCode_eq i 0, ← profileCode_eq j p]
  simp only [rename_zero]
  congr 1
  funext c
  simp only [hf.2.2.2]

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
