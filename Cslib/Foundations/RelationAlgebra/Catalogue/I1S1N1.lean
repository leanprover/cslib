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
public import Cslib.Foundations.RelationAlgebra.FiniteClassification

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

private abbrev a : DiversityAtom 1 1 := .inl 0

private abbrev b : DiversityAtom 1 1 := .inr (0, false)

private abbrev b' : DiversityAtom 1 1 := .inr (0, true)

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

private def classificationWitness (bits : Fin 7 → Bool) : Fin 37 × Bool :=
  match cycleMask bits with
  | 8 => (0, false)
  | 29 => (3, false)
  | 31 => (6, false)
  | 34 => (16, false)
  | 35 => (17, false)
  | 39 => (24, true)
  | 42 => (20, false)
  | 43 => (21, false)
  | 46 => (25, true)
  | 47 => (26, true)
  | 51 => (24, false)
  | 52 => (10, false)
  | 53 => (11, false)
  | 54 => (29, false)
  | 55 => (30, false)
  | 58 => (25, false)
  | 59 => (26, false)
  | 61 => (14, false)
  | 62 => (33, false)
  | 63 => (34, false)
  | 66 => (4, false)
  | 67 => (5, false)
  | 84 => (1, false)
  | 85 => (2, false)
  | 94 => (7, false)
  | 95 => (8, false)
  | 98 => (18, false)
  | 99 => (19, false)
  | 104 => (9, false)
  | 106 => (22, false)
  | 107 => (23, false)
  | 110 => (27, true)
  | 111 => (28, true)
  | 116 => (12, false)
  | 117 => (13, false)
  | 118 => (31, false)
  | 119 => (32, false)
  | 122 => (27, false)
  | 123 => (28, false)
  | 125 => (15, false)
  | 126 => (35, false)
  | 127 => (36, false)
  | _ => (0, false)

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

private def bitsVector (b0 b1 b2 b3 b4 b5 b6 : Bool) : Fin 7 → Bool
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5
  | 6 => b6

private theorem bitsVector_eq (bits : Fin 7 → Bool) :
    bitsVector (bits 0) (bits 1) (bits 2) (bits 3) (bits 4) (bits 5) (bits 6) = bits := by
  funext i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem cycles_exhaustive : ∀ bits : Fin 7 → Bool,
    AtomCompositionAssociative (selectedCycles cycleReps bits) →
      ∃ idx : Fin 37, ∃ f,
        AtomRelabelling (selectedCycles cycleReps bits) (table idx).cycles f := by
  have h : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
      let bits := bitsVector b0 b1 b2 b3 b4 b5 b6
      AtomRelabelling (selectedCycles cycleReps bits)
        (table (classificationWitness bits).1).cycles (rename (classificationWitness bits).2) ∨
          ¬ AtomCompositionAssociative (selectedCycles cycleReps bits) := by
    intro b0 b1 b2 b3 b4 b5 b6
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6
    · right
      change ¬ AtomCompositionAssociative ∅
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(b, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b', b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b', b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b', b'), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b', b'), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, b, b')}
        (table 0).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b'), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b)
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, b, b'), (b, b, b), (b, b, b')}
        (table 9).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b'), (a, b', b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b'), (a, b', b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b'), (a, b', b'), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b'), (a, b', b'), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b') (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b') (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b') (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b') (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b), (a, b', b')}
      intro ha
      have hbad := ha (some b) (some b) (some b') (some b)
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, b, b), (a, b', b'), (b, b, b')}
        (table 1).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, b, b), (a, b', b'), (b, b, b)}
        (table 10).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, b, b), (a, b', b'), (b, b, b), (b, b, b')}
        (table 12).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b), (a, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b), (a, b, b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b), (a, b, b'), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b), (a, b, b'), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b), (a, b, b'), (a, b', b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b), (a, b, b'), (a, b', b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, b, b), (a, b, b'), (a, b', b'), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative
        {(a, b, b), (a, b, b'), (a, b', b'), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (b, b, b')}
        (table 4).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (b, b, b)}
        (table 16).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (b, b, b), (b, b, b')}
        (table 18).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b', b')}
      intro ha
      have hbad := ha (some a) (some a) (some a) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b', b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some a) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b', b'), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some a) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b', b'), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some a) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b, b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b)
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (a, b, b'), (b, b, b)}
        (table 20).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (a, b, b'), (b, b, b), (b, b, b')}
        (table 22).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b, b'), (a, b', b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b, b'), (a, b', b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b)
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (a, b, b'), (a, b', b'), (b, b, b)}
        (table 25).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (a, b, b'), (a, b', b'), (b, b, b), (b, b, b')}
        (table 27).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some a) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some a) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b, b), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some a) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b, b), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some a) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b, b), (a, b', b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b, b), (a, b', b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b)
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (a, b, b), (a, b', b'), (b, b, b)}
        (table 29).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (a, b, b), (a, b', b'), (b, b, b), (b, b, b')}
        (table 31).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b, b), (a, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b, b), (a, b, b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b') (some b')
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (a, b, b), (a, b, b'), (b, b, b)}
        (table 25).cycles (rename true)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (a, b, b), (a, b, b'), (b, b, b), (b, b, b')}
        (table 27).cycles (rename true)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, b), (a, b, b), (a, b, b'), (a, b', b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (a, b, b), (a, b, b'), (a, b', b'), (b, b, b')}
        (table 7).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (a, b, b), (a, b, b'), (a, b', b'), (b, b, b)}
        (table 33).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, b), (a, b, b), (a, b, b'), (a, b', b'), (b, b, b), (b, b, b')}
        (table 35).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a)}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b', b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b', b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b', b'), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b', b'), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b'), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b'), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b'), (a, b', b')}
      intro ha
      have hbad := ha (some a) (some b) (some a) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b'), (a, b', b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some a) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b'), (a, b', b'), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some b) (some a) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative
        {(a, a, a), (a, b, b'), (a, b', b'), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some a) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b') (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b') (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b') (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some a) (some b') (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b), (a, b', b')}
      intro ha
      have hbad := ha (some b) (some b) (some b') (some b)
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, b, b), (a, b', b'), (b, b, b')}
        (table 2).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, b, b), (a, b', b'), (b, b, b)}
        (table 11).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, b, b), (a, b', b'), (b, b, b), (b, b, b')}
        (table 13).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b), (a, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some a) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b), (a, b, b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some a) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b), (a, b, b'), (b, b, b)}
      intro ha
      have hbad := ha (some a) (some b) (some a) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, b, b), (a, b, b'), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some a) (some b')
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, b, b), (a, b, b'), (a, b', b')}
        (table 3).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative
        {(a, a, a), (a, b, b), (a, b, b'), (a, b', b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b)
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, b, b), (a, b, b'), (a, b', b'), (b, b, b)}
        (table 14).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, b, b), (a, b, b'), (a, b', b'), (b, b, b), (b, b, b')}
        (table 15).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (b, b, b')}
        (table 5).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (b, b, b)}
        (table 17).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (b, b, b), (b, b, b')}
        (table 19).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b), (a, b', b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b), (a, b', b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b')
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (a, b', b'), (b, b, b)}
        (table 24).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b), (a, b', b'), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b), (a, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b), (a, b, b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b)
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (a, b, b'), (b, b, b)}
        (table 21).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (a, b, b'), (b, b, b), (b, b, b')}
        (table 23).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b), (a, b, b'), (a, b', b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b)
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative
        {(a, a, a), (a, a, b), (a, b, b'), (a, b', b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b)
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (a, b, b'), (a, b', b'), (b, b, b)}
        (table 26).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (a, b, b'), (a, b', b'), (b, b, b), (b, b, b')}
        (table 28).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b), (a, b, b)}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b), (a, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b)
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (a, b, b), (b, b, b)}
        (table 24).cycles (rename true)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b), (a, b, b), (b, b, b), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b), (a, b, b), (a, b', b')}
      intro ha
      have hbad := ha (some a) (some a) (some b) (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b), (a, b, b), (a, b', b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b) (some b)
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (a, b, b), (a, b', b'), (b, b, b)}
        (table 30).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (a, b, b), (a, b', b'), (b, b, b), (b, b, b')}
        (table 32).cycles (rename false)
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b), (a, b, b), (a, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b') (some b')
      revert hbad
      decide +kernel
    · right
      change ¬ AtomCompositionAssociative {(a, a, a), (a, a, b), (a, b, b), (a, b, b'), (b, b, b')}
      intro ha
      have hbad := ha (some a) (some b) (some b') (some b')
      revert hbad
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (a, b, b), (a, b, b'), (b, b, b)}
        (table 26).cycles (rename true)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (a, b, b), (a, b, b'), (b, b, b), (b, b, b')}
        (table 28).cycles (rename true)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (a, b, b), (a, b, b'), (a, b', b')}
        (table 6).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (a, b, b), (a, b, b'), (a, b', b'), (b, b, b')}
        (table 8).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling {(a, a, a), (a, a, b), (a, b, b), (a, b, b'), (a, b', b'), (b, b, b)}
        (table 34).cycles (rename false)
      decide +kernel
    · left
      change AtomRelabelling
        {(a, a, a), (a, a, b), (a, b, b), (a, b, b'), (a, b', b'), (b, b, b), (b, b, b')}
        (table 36).cycles (rename false)
      decide +kernel
  intro bits hb
  have hh := h (bits 0) (bits 1) (bits 2) (bits 3) (bits 4) (bits 5) (bits 6)
  dsimp only at hh
  rw [bitsVector_eq] at hh
  exact ⟨(classificationWitness bits).1, rename (classificationWitness bits).2,
    hh.resolve_right (not_not_intro hb)⟩

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
