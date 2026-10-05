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
public import Cslib.Foundations.RelationAlgebra.FastClassification

/-!
# Classification of the ⟨1, 1, 1⟩ catalogue row

This row contains 37 isomorphism classes, of which 26 are representable and
11 are nonrepresentable. See
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
`Model` uses zero-based indices: index `n` denotes source entry `n + 1`.
The unique-index classification expresses both exhaustiveness and absence of duplicates.
Seven Peircean cycle orbits reduce this classification to 128 possible cycle tables.
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

private def cycleReps : Fin 7 → Cycle 1 1
  | 0 => (.inl 0, .inl 0, .inl 0)
  | 1 => (.inl 0, .inl 0, .inr (0, false))
  | 2 => (.inl 0, .inr (0, false), .inr (0, false))
  | 3 => (.inl 0, .inr (0, false), .inr (0, true))
  | 4 => (.inl 0, .inr (0, true), .inr (0, true))
  | 5 => (.inr (0, false), .inr (0, false), .inr (0, false))
  | 6 => (.inr (0, false), .inr (0, false), .inr (0, true))

private theorem cycleReps_cover : ∀ c : Cycle 1 1,
    ∃ i, (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (cycleReps i) := by
  decide +kernel

private def rename (flip : Bool) (x : Atom 1 1) : Atom 1 1 :=
  if flip then x.converse else x

private def cycleMask (bits : Fin 7 → Bool) : ℕ :=
  (if bits 0 then 1 else 0) +
    (if bits 1 then 2 else 0) +
    (if bits 2 then 4 else 0) +
    (if bits 3 then 8 else 0) +
    (if bits 4 then 16 else 0) +
    (if bits 5 then 32 else 0) +
    (if bits 6 then 64 else 0)

private def classificationWitness : ℕ → Fin 37 × Fin 2
  | 8 => (0, 0)
  | 29 => (3, 0)
  | 31 => (6, 0)
  | 34 => (16, 0)
  | 35 => (17, 0)
  | 39 => (24, 1)
  | 42 => (20, 0)
  | 43 => (21, 0)
  | 46 => (25, 1)
  | 47 => (26, 1)
  | 51 => (24, 0)
  | 52 => (10, 0)
  | 53 => (11, 0)
  | 54 => (29, 0)
  | 55 => (30, 0)
  | 58 => (25, 0)
  | 59 => (26, 0)
  | 61 => (14, 0)
  | 62 => (33, 0)
  | 63 => (34, 0)
  | 66 => (4, 0)
  | 67 => (5, 0)
  | 84 => (1, 0)
  | 85 => (2, 0)
  | 94 => (7, 0)
  | 95 => (8, 0)
  | 98 => (18, 0)
  | 99 => (19, 0)
  | 104 => (9, 0)
  | 106 => (22, 0)
  | 107 => (23, 0)
  | 110 => (27, 1)
  | 111 => (28, 1)
  | 116 => (12, 0)
  | 117 => (13, 0)
  | 118 => (31, 0)
  | 119 => (32, 0)
  | 122 => (27, 0)
  | 123 => (28, 0)
  | 125 => (15, 0)
  | 126 => (35, 0)
  | 127 => (36, 0)
  | _ => (0, 0)

private def profileCode : Fin 37 → Bool → ℕ
  | 0, false => 8
  | 0, true => 8
  | 1, false => 84
  | 1, true => 84
  | 2, false => 85
  | 2, true => 85
  | 3, false => 29
  | 3, true => 29
  | 4, false => 66
  | 4, true => 66
  | 5, false => 67
  | 5, true => 67
  | 6, false => 31
  | 6, true => 31
  | 7, false => 94
  | 7, true => 94
  | 8, false => 95
  | 8, true => 95
  | 9, false => 104
  | 9, true => 104
  | 10, false => 52
  | 10, true => 52
  | 11, false => 53
  | 11, true => 53
  | 12, false => 116
  | 12, true => 116
  | 13, false => 117
  | 13, true => 117
  | 14, false => 61
  | 14, true => 61
  | 15, false => 125
  | 15, true => 125
  | 16, false => 34
  | 16, true => 34
  | 17, false => 35
  | 17, true => 35
  | 18, false => 98
  | 18, true => 98
  | 19, false => 99
  | 19, true => 99
  | 20, false => 42
  | 20, true => 42
  | 21, false => 43
  | 21, true => 43
  | 22, false => 106
  | 22, true => 106
  | 23, false => 107
  | 23, true => 107
  | 24, false => 51
  | 24, true => 39
  | 25, false => 58
  | 25, true => 46
  | 26, false => 59
  | 26, true => 47
  | 27, false => 122
  | 27, true => 110
  | 28, false => 123
  | 28, true => 111
  | 29, false => 54
  | 29, true => 54
  | 30, false => 55
  | 30, true => 55
  | 31, false => 118
  | 31, true => 118
  | 32, false => 119
  | 32, true => 119
  | 33, false => 62
  | 33, true => 62
  | 34, false => 63
  | 34, true => 63
  | 35, false => 126
  | 35, true => 126
  | 36, false => 127
  | 36, true => 127
  | ⟨v + 37, h⟩, _ => False.elim (by omega)

private def modelCode : Fin 37 → ℕ
  | 0 => 2398187160928945185
  | 1 => 4866201264298558497
  | 2 => 4866201264300655649
  | 3 => 2578366607490450465
  | 4 => 4695029155015853089
  | 5 => 4695029155017950241
  | 6 => 2587373944767153185
  | 7 => 7199068759285466145
  | 8 => 7199068759287563297
  | 9 => 17098160645038310433
  | 10 => 10342785119367103521
  | 11 => 10342785119369200673
  | 12 => 14954479933887513633
  | 13 => 14954479933889610785
  | 14 => 12666645277079405601
  | 15 => 17278340091599815713
  | 16 => 10171613010084398113
  | 17 => 10171613010086495265
  | 18 => 14783307824604808225
  | 19 => 14783307824606905377
  | 20 => 12495473167794603041
  | 21 => 12495473167796700193
  | 22 => 17107167982315013153
  | 23 => 17107167982317110305
  | 24 => 10315728475187741729
  | 25 => 12639588632895849505
  | 26 => 12639588632897946657
  | 27 => 17251283447416259617
  | 28 => 17251283447418356769
  | 29 => 10351792456643806241
  | 30 => 10351792456645903393
  | 31 => 14963487271164216353
  | 32 => 14963487271166313505
  | 33 => 12675652614354011169
  | 34 => 12675652614356108321
  | 35 => 17287347428874421281
  | 36 => 17287347428876518433
  | ⟨n + 37, h⟩ => False.elim (by omega)

private theorem modelCode_eq : ∀ idx, tableCode (table idx).cycles = modelCode idx := by
  decide +kernel

private theorem modelCode_encodes (idx : Fin 37) :
    EncodesTable (table idx).cycles (modelCode idx) := by
  rw [← modelCode_eq]
  exact encodesTable_tableCode _

private def renames (p : Fin 2) : Atom 1 1 → Atom 1 1 := rename (Nat.beq p.val 1)

private def renameCodes (p : Fin 2) (x : ℕ) : ℕ :=
  cond (Nat.beq p.val 0) x (Code.conv 1 x)

private theorem renames_code : ∀ p x, (renames p x).code = renameCodes p x.code := by
  decide +kernel

private theorem renames_laws : ∀ p, Function.Injective (renames p) ∧ renames p none = none ∧
    ∀ x, renames p x.converse = (renames p x).converse := by
  unfold Function.Injective
  decide +kernel

private theorem cycles_exhaustive : ∀ bits : Fin 7 → Bool,
    AtomCompositionAssociative (selectedCycles cycleReps bits) →
      ∃ idx : Fin 37, ∃ f,
        AtomRelabelling (selectedCycles cycleReps bits) (table idx).cycles f :=
  cycles_exhaustive_of_check cycleReps table modelCode modelCode_encodes
    renames renameCodes renames_code renames_laws classificationWitness (by decide +kernel)

private theorem renamings_exhaustive : ∀ f : Atom 1 1 → Atom 1 1,
    Function.Injective f → f none = none →
      (∀ x, f x.converse = (f x).converse) → ∃ flip : Bool, f = rename flip := by
  unfold Function.Injective
  decide +kernel

private theorem rename_zero : ∀ x, rename false x = x := by
  decide +kernel

private theorem profileCode_eq : ∀ idx : Fin 37, ∀ p : Bool,
    cycleMask (fun c => decide (cycleClosure (table idx).cycles
      (rename p (some (cycleReps c).1)) (rename p (some (cycleReps c).2.1))
      (rename p (some (cycleReps c).2.2)))) = profileCode idx p := by
  simp only [cycleClosure_iff_bitAt (modelCode_encodes _), Bool.decide_eq_true]
  decide +kernel

private theorem profileCode_injective : ∀ i j : Fin 37, ∀ p : Bool,
    profileCode i false = profileCode j p → i = j := by
  decide +kernel

private theorem cycles_distinct : ∀ i j : Fin 37, ∀ f,
    AtomRelabelling (table i).cycles (table j).cycles f → i = j := by
  intro i j f hf
  obtain ⟨p, rfl⟩ := renamings_exhaustive f hf.1 hf.2.1 hf.2.2.1
  apply profileCode_injective i j p
  rw [← profileCode_eq i false, ← profileCode_eq j p]
  simp only [rename_zero]
  congr 1
  funext c
  simp only [hf.2.2.2]

/-- Every algebra of this signature is isomorphic to exactly one listed model. -/
theorem classification (A : Type*) [RelationAlgebra A] (h : HasSignature A 1 1 1) :
    ∃! idx : Fin 37, Nonempty (RelationAlgebraEquiv A (Model idx)) := by
  exact classification_of_cycle_basis cycleReps cycleReps_cover table
    cycles_exhaustive cycles_distinct A h

private def nonrepresentableIndices : Finset (Fin 37) :=
  {7, 14, 21, 22, 23, 25, 26, 27, 29, 31, 33}

private theorem model_representable_iff : ∀ idx : Fin 37,
    Representable (Model idx) ↔ idx ∉ nonrepresentableIndices
  | ⟨0, _⟩ => iff_of_true Ra01.representable (by decide +kernel +revert)
  | ⟨1, _⟩ => iff_of_true Ra02.representable (by decide +kernel +revert)
  | ⟨2, _⟩ => iff_of_true Ra03.representable (by decide +kernel +revert)
  | ⟨3, _⟩ => iff_of_true Ra04.representable (by decide +kernel +revert)
  | ⟨4, _⟩ => iff_of_true Ra05.representable (by decide +kernel +revert)
  | ⟨5, _⟩ => iff_of_true Ra06.representable (by decide +kernel +revert)
  | ⟨6, _⟩ => iff_of_true Ra07.representable (by decide +kernel +revert)
  | ⟨7, _⟩ => iff_of_false Ra08.not_representable (by decide +kernel +revert)
  | ⟨8, _⟩ => iff_of_true Ra09.representable (by decide +kernel +revert)
  | ⟨9, _⟩ => iff_of_true Ra10.representable (by decide +kernel +revert)
  | ⟨10, _⟩ => iff_of_true Ra11.representable (by decide +kernel +revert)
  | ⟨11, _⟩ => iff_of_true Ra12.representable (by decide +kernel +revert)
  | ⟨12, _⟩ => iff_of_true Ra13.representable (by decide +kernel +revert)
  | ⟨13, _⟩ => iff_of_true Ra14.representable (by decide +kernel +revert)
  | ⟨14, _⟩ => iff_of_false Ra15.not_representable (by decide +kernel +revert)
  | ⟨15, _⟩ => iff_of_true Ra16.representable (by decide +kernel +revert)
  | ⟨16, _⟩ => iff_of_true Ra17.representable (by decide +kernel +revert)
  | ⟨17, _⟩ => iff_of_true Ra18.representable (by decide +kernel +revert)
  | ⟨18, _⟩ => iff_of_true Ra19.representable (by decide +kernel +revert)
  | ⟨19, _⟩ => iff_of_true Ra20.representable (by decide +kernel +revert)
  | ⟨20, _⟩ => iff_of_true Ra21.representable (by decide +kernel +revert)
  | ⟨21, _⟩ => iff_of_false Ra22.not_representable (by decide +kernel +revert)
  | ⟨22, _⟩ => iff_of_false Ra23.not_representable (by decide +kernel +revert)
  | ⟨23, _⟩ => iff_of_false Ra24.not_representable (by decide +kernel +revert)
  | ⟨24, _⟩ => iff_of_true Ra25.representable (by decide +kernel +revert)
  | ⟨25, _⟩ => iff_of_false Ra26.not_representable (by decide +kernel +revert)
  | ⟨26, _⟩ => iff_of_false Ra27.not_representable (by decide +kernel +revert)
  | ⟨27, _⟩ => iff_of_false Ra28.not_representable (by decide +kernel +revert)
  | ⟨28, _⟩ => iff_of_true Ra29.representable (by decide +kernel +revert)
  | ⟨29, _⟩ => iff_of_false Ra30.not_representable (by decide +kernel +revert)
  | ⟨30, _⟩ => iff_of_true Ra31.representable (by decide +kernel +revert)
  | ⟨31, _⟩ => iff_of_false Ra32.not_representable (by decide +kernel +revert)
  | ⟨32, _⟩ => iff_of_true Ra33.representable (by decide +kernel +revert)
  | ⟨33, _⟩ => iff_of_false Ra34.not_representable (by decide +kernel +revert)
  | ⟨34, _⟩ => iff_of_true Ra35.representable (by decide +kernel +revert)
  | ⟨35, _⟩ => iff_of_true Ra36.representable (by decide +kernel +revert)
  | ⟨36, _⟩ => iff_of_true Ra37.representable (by decide +kernel +revert)
  | ⟨n + 37, h⟩ => False.elim (by omega)

/-- The number of representable isomorphism classes in this row. -/
theorem count_representable :
    Nat.card {idx : Fin 37 // Representable (Model idx)} = 26 := by
  let e : {idx : Fin 37 // Representable (Model idx)} ≃
      {idx : Fin 37 // idx ∉ nonrepresentableIndices} :=
    { toFun := fun idx => ⟨idx.val, (model_representable_iff idx.val).mp idx.property⟩
      invFun := fun idx => ⟨idx.val, (model_representable_iff idx.val).mpr idx.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

/-- The number of nonrepresentable isomorphism classes in this row. -/
theorem count_nonrepresentable :
    Nat.card {idx : Fin 37 // ¬ Representable (Model idx)} = 11 := by
  let e : {idx : Fin 37 // ¬ Representable (Model idx)} ≃
      {idx : Fin 37 // idx ∈ nonrepresentableIndices} :=
    { toFun := fun idx => ⟨idx.val, by
          simpa only [model_representable_iff, not_not] using idx.property⟩
      invFun := fun idx => ⟨idx.val, by
          simpa only [model_representable_iff, not_not] using idx.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S1N1
