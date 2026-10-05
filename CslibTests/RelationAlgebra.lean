/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Foundations.RelationAlgebra.Catalogue
import Mathlib.Data.Fintype.Perm

/-!
# Relation algebra sanity checks

These executable checks inspect the concrete cycle lists and algebra operations independently
of the associativity, classification, and representability proofs. They check the
atom laws for every catalogue entry and distinguish each row under all atom permutations that
preserve identity and converse. They do not prove exhaustiveness or representability.
-/

set_option linter.hashCommand false

namespace CslibTests.RelationAlgebra

open Cslib Cslib.RelationAlgebra Cslib.RelationAlgebra.Catalogue

private def auditCycles {j k : ℕ} (cycles : Finset (Cycle j k)) : Bool :=
  decide (
    (∀ x : Atom j k, Atom.converse (Atom.converse x) = x) ∧
    (∀ x y : Atom j k,
      (cycleClosure cycles none x y ↔ x = y) ∧
      (cycleClosure cycles x none y ↔ x = y) ∧
      (cycleClosure cycles x y none ↔ y = Atom.converse x)) ∧
    (∀ x y z : Atom j k,
      (cycleClosure cycles x y z ↔
        cycleClosure cycles (Atom.converse y) (Atom.converse x) (Atom.converse z)) ∧
      (cycleClosure cycles x y z ↔ cycleClosure cycles (Atom.converse x) z y) ∧
      (cycleClosure cycles x y z ↔ cycleClosure cycles z (Atom.converse y) x)) ∧
    AtomCompositionAssociative cycles)

private def allAtoms (j k : ℕ) : List (Atom j k) :=
  none :: ((List.finRange j).map (fun a => some (.inl a)) ++
    (List.finRange k).flatMap (fun a => [some (.inr (a, false)), some (.inr (a, true))]))

/-- Encode an atom multiplication table as a binary natural number, and minimize over all
identity- and converse-preserving permutations. Equal codes mean isomorphic atom tables. -/
private def canonicalCode {j k : ℕ} (cycles : Finset (Cycle j k)) : ℕ :=
  let atoms := allAtoms j k
  let triples := atoms.flatMap fun x => atoms.flatMap fun y => atoms.map fun z => (x, y, z)
  let permutations := (permsOfList atoms).filter fun p =>
    decide (p none = none ∧ ∀ x, p (Atom.converse x) = Atom.converse (p x))
  let codes := permutations.map fun p => triples.foldl (fun acc (x, y, z) =>
    2 * acc + if cycleClosure cycles (p x) (p y) (p z) then 1 else 0) 0
  codes.foldl min (2 ^ triples.length)

private def distinctTables {j k : ℕ} (row : List (Finset (Cycle j k))) : Bool :=
  decide (row.map canonicalCode).Nodup

/-- Run the exhaustive audit using compiled evaluation, without constructing theorem proofs. -/
private def checkRow {j k : ℕ} (name : String) (row : List (Finset (Cycle j k)))
    (expected : ℕ) : IO Unit := do
  unless row.length == expected do
    throw <| IO.userError s!"{name}: unexpected number of entries"
  unless row.all auditCycles do
    throw <| IO.userError s!"{name}: an atom law failed"
  unless distinctTables row do
    throw <| IO.userError s!"{name}: isomorphic entries found"

-- Keep compiled audits independent of the law certificates in the indexed tables.
-- The equality checks below also verify that these lists enumerate the actual indexed families.
private def rowI1S0N0 : List (Finset (Cycle 0 0)) :=
  [I1S0N0.Ra01.cycles]

#guard rowI1S0N0 == List.ofFn (fun idx : Fin 1 => (I1S0N0.table idx).cycles)
#eval checkRow "I1S0N0" rowI1S0N0 1

private def rowI1S1N0 : List (Finset (Cycle 1 0)) :=
  [I1S1N0.Ra01.cycles, I1S1N0.Ra02.cycles]

#guard rowI1S1N0 == List.ofFn (fun idx : Fin 2 => (I1S1N0.table idx).cycles)
#eval checkRow "I1S1N0" rowI1S1N0 2

private def rowI1S0N1 : List (Finset (Cycle 0 1)) :=
  [I1S0N1.Ra01.cycles, I1S0N1.Ra02.cycles, I1S0N1.Ra03.cycles]

#guard rowI1S0N1 == List.ofFn (fun idx : Fin 3 => (I1S0N1.table idx).cycles)
#eval checkRow "I1S0N1" rowI1S0N1 3

private def rowI1S2N0 : List (Finset (Cycle 2 0)) :=
  [I1S2N0.Ra01.cycles, I1S2N0.Ra02.cycles, I1S2N0.Ra03.cycles,
   I1S2N0.Ra04.cycles, I1S2N0.Ra05.cycles, I1S2N0.Ra06.cycles,
   I1S2N0.Ra07.cycles]

#guard rowI1S2N0 == List.ofFn (fun idx : Fin 7 => (I1S2N0.table idx).cycles)
#eval checkRow "I1S2N0" rowI1S2N0 7

private def rowI1S1N1 : List (Finset (Cycle 1 1)) :=
  [I1S1N1.Ra01.cycles, I1S1N1.Ra02.cycles, I1S1N1.Ra03.cycles,
   I1S1N1.Ra04.cycles, I1S1N1.Ra05.cycles, I1S1N1.Ra06.cycles,
   I1S1N1.Ra07.cycles, I1S1N1.Ra08.cycles, I1S1N1.Ra09.cycles,
   I1S1N1.Ra10.cycles, I1S1N1.Ra11.cycles, I1S1N1.Ra12.cycles,
   I1S1N1.Ra13.cycles, I1S1N1.Ra14.cycles, I1S1N1.Ra15.cycles,
   I1S1N1.Ra16.cycles, I1S1N1.Ra17.cycles, I1S1N1.Ra18.cycles,
   I1S1N1.Ra19.cycles, I1S1N1.Ra20.cycles, I1S1N1.Ra21.cycles,
   I1S1N1.Ra22.cycles, I1S1N1.Ra23.cycles, I1S1N1.Ra24.cycles,
   I1S1N1.Ra25.cycles, I1S1N1.Ra26.cycles, I1S1N1.Ra27.cycles,
   I1S1N1.Ra28.cycles, I1S1N1.Ra29.cycles, I1S1N1.Ra30.cycles,
   I1S1N1.Ra31.cycles, I1S1N1.Ra32.cycles, I1S1N1.Ra33.cycles,
   I1S1N1.Ra34.cycles, I1S1N1.Ra35.cycles, I1S1N1.Ra36.cycles,
   I1S1N1.Ra37.cycles]

#guard rowI1S1N1 == List.ofFn (fun idx : Fin 37 => (I1S1N1.table idx).cycles)
#eval checkRow "I1S1N1" rowI1S1N1 37

private def rowI1S3N0 : List (Finset (Cycle 3 0)) :=
  [I1S3N0.Ra01.cycles, I1S3N0.Ra02.cycles, I1S3N0.Ra03.cycles,
   I1S3N0.Ra04.cycles, I1S3N0.Ra05.cycles, I1S3N0.Ra06.cycles,
   I1S3N0.Ra07.cycles, I1S3N0.Ra08.cycles, I1S3N0.Ra09.cycles,
   I1S3N0.Ra10.cycles, I1S3N0.Ra11.cycles, I1S3N0.Ra12.cycles,
   I1S3N0.Ra13.cycles, I1S3N0.Ra14.cycles, I1S3N0.Ra15.cycles,
   I1S3N0.Ra16.cycles, I1S3N0.Ra17.cycles, I1S3N0.Ra18.cycles,
   I1S3N0.Ra19.cycles, I1S3N0.Ra20.cycles, I1S3N0.Ra21.cycles,
   I1S3N0.Ra22.cycles, I1S3N0.Ra23.cycles, I1S3N0.Ra24.cycles,
   I1S3N0.Ra25.cycles, I1S3N0.Ra26.cycles, I1S3N0.Ra27.cycles,
   I1S3N0.Ra28.cycles, I1S3N0.Ra29.cycles, I1S3N0.Ra30.cycles,
   I1S3N0.Ra31.cycles, I1S3N0.Ra32.cycles, I1S3N0.Ra33.cycles,
   I1S3N0.Ra34.cycles, I1S3N0.Ra35.cycles, I1S3N0.Ra36.cycles,
   I1S3N0.Ra37.cycles, I1S3N0.Ra38.cycles, I1S3N0.Ra39.cycles,
   I1S3N0.Ra40.cycles, I1S3N0.Ra41.cycles, I1S3N0.Ra42.cycles,
   I1S3N0.Ra43.cycles, I1S3N0.Ra44.cycles, I1S3N0.Ra45.cycles,
   I1S3N0.Ra46.cycles, I1S3N0.Ra47.cycles, I1S3N0.Ra48.cycles,
   I1S3N0.Ra49.cycles, I1S3N0.Ra50.cycles, I1S3N0.Ra51.cycles,
   I1S3N0.Ra52.cycles, I1S3N0.Ra53.cycles, I1S3N0.Ra54.cycles,
   I1S3N0.Ra55.cycles, I1S3N0.Ra56.cycles, I1S3N0.Ra57.cycles,
   I1S3N0.Ra58.cycles, I1S3N0.Ra59.cycles, I1S3N0.Ra60.cycles,
   I1S3N0.Ra61.cycles, I1S3N0.Ra62.cycles, I1S3N0.Ra63.cycles,
   I1S3N0.Ra64.cycles, I1S3N0.Ra65.cycles]

#guard rowI1S3N0 == List.ofFn (fun idx : Fin 65 => (I1S3N0.table idx).cycles)
#eval checkRow "I1S3N0" rowI1S3N0 65

-- Concrete powerset operations compute independently of their law certificates.
private def c2Generator : I1S1N0.Ra01.Algebra :=
  Complex.atom I1S1N0.Ra01.table (some (.inl 0))

#guard (c2Generator * c2Generator).atoms == {none}
#guard (c2Generatorᶜ).atoms == {none}
#guard (star c2Generator).atoms == c2Generator.atoms

private def c3Generator : I1S0N1.Ra01.Algebra :=
  Complex.atom I1S0N1.Ra01.table (some (.inr (0, false)))

#guard (c3Generator * c3Generator).atoms == {some (.inr (0, true))}
#guard (c3Generator * star c3Generator).atoms == {none}
#guard (c3Generatorᶜ).atoms == {none, some (.inr (0, true))}

-- The concrete square model uses left-to-right relational composition.
example {Base : Type*} (R S : SquareRelations Base) (x z : Base) :
    ((R * S : SquareRelations Base) : SetRel Base Base) (x, z) ↔
      ∃ y, (R : SetRel Base Base) (x, y) ∧ (S : SetRel Base Base) (y, z) := Iff.rfl

example {Base : Type*} (R : SquareRelations Base) (x y : Base) :
    ((star R : SquareRelations Base) : SetRel Base Base) (x, y) ↔
      (R : SetRel Base Base) (y, x) := Iff.rfl

section Morphisms

variable {A B : Type*} [RelationAlgebra A] [RelationAlgebra B]

example (f : RelationAlgebraHom A B) : (f.toBoundedLatticeHom : A → B) = f := rfl

example (f : RelationAlgebraHom A B) : (f.toStarMonoidHom : A → B) = f := rfl

example (e : RelationAlgebraEquiv A B) (a : A) : e.toHom a = e a := rfl

example (a : A) : ((RelationAlgebraHom.id A).comp (RelationAlgebraHom.id A)) a = a := rfl

end Morphisms

end CslibTests.RelationAlgebra
