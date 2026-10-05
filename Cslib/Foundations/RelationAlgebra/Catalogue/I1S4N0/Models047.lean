/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3009
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3010
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3011
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3012
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3013

/-!
# Certified models 3009–3013 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models047

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3009.table, code := 42229701789209822698562279585523961921,
        encodes := Ra3009.tableCode_eq ▸ encodesTable_tableCode Ra3009.cycles } 1031839
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3010.table, code := 42229701789292029728371285713318318145,
        encodes := Ra3010.tableCode_eq ▸ encodesTable_tableCode Ra3010.cycles } 1031871
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3011.table, code := 42232460196998128717308786013863415873,
        encodes := Ra3011.tableCode_eq ▸ encodesTable_tableCode Ra3011.cycles } 1031935
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3012.table, code := 42315861544535849713470527838653517889,
        encodes := Ra3012.tableCode_eq ▸ encodesTable_tableCode Ra3012.cycles } 1032191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3013.table, code := 42492399796801338936040706136380543041,
        encodes := Ra3013.tableCode_eq ▸ encodesTable_tableCode Ra3013.cycles } 1048575
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 5, ∀ p : Fin 24,
    Data.profiles (3008 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (3008 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 5, ∀ p : Fin 24,
    Data.profiles (3008 + i.val) 0 ≤ Data.profiles (3008 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 5,
    Data.profiles (3008 + i.val) 0 = Data.canonicalMask (3008 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 4,
    Data.canonicalMask (3008 + i.val) < Data.canonicalMask (3008 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 5,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (3008 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models047
