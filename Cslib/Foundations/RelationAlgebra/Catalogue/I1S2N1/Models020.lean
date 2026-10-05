/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1281
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1282
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1283
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1284
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1285
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1286
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1287
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1288
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1289
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1290
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1291
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1292
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1293
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1294
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1295
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1296
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1297
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1298
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1299
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1300
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1301
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1302
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1303
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1304
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1305
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1306
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1307
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1308
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1309
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1310
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1311
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1312
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1313
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1314
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1315
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1316

/-!
# Certified models 1281–1316 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models020

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1281.table, code := 41196759509459254650665712204961288257,
        encodes := Ra1281.tableCode_eq ▸ encodesTable_tableCode Ra1281.cycles } 64455
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1282.table, code := 41196678379818422194794672898797998145,
        encodes := Ra1282.tableCode_eq ▸ encodesTable_tableCode Ra1282.cycles } 64459
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1283.table, code := 41199436787606728211019163325356576833,
        encodes := Ra1283.tableCode_eq ▸ encodesTable_tableCode Ra1283.cycles } 64497
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1284.table, code := 41199436787606728211091220992408948801,
        encodes := Ra1284.tableCode_eq ▸ encodesTable_tableCode Ra1284.cycles } 64499
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1285.table, code := 41199517917247560669340160964100886593,
        encodes := Ra1285.tableCode_eq ▸ encodesTable_tableCode Ra1285.cycles } 64500
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1286.table, code := 41199517917247560669340160966248370241,
        encodes := Ra1286.tableCode_eq ▸ encodesTable_tableCode Ra1286.cycles } 64501
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1287.table, code := 41199517917247560669412218631153258561,
        encodes := Ra1287.tableCode_eq ▸ encodesTable_tableCode Ra1287.cycles } 64502
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1288.table, code := 41199517917247560669412218633300742209,
        encodes := Ra1288.tableCode_eq ▸ encodesTable_tableCode Ra1288.cycles } 64503
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1289.table, code := 41199436787606728213541179327137452097,
        encodes := Ra1289.tableCode_eq ▸ encodesTable_tableCode Ra1289.cycles } 64507
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1290.table, code := 41199517917247560671790119298829389889,
        encodes := Ra1290.tableCode_eq ▸ encodesTable_tableCode Ra1290.cycles } 64508
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1291.table, code := 41199517917247560671790119300976873537,
        encodes := Ra1291.tableCode_eq ▸ encodesTable_tableCode Ra1291.cycles } 64509
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1292.table, code := 41199517917247560671862176965881761857,
        encodes := Ra1292.tableCode_eq ▸ encodesTable_tableCode Ra1292.cycles } 64510
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1293.table, code := 41199517917247560671862176968029245505,
        encodes := Ra1293.tableCode_eq ▸ encodesTable_tableCode Ra1293.cycles } 64511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1294.table, code := 41201951806472536878653739119692484673,
        encodes := Ra1294.tableCode_eq ▸ encodesTable_tableCode Ra1294.cycles } 64974
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1295.table, code := 41201951806472536878653739121839968321,
        encodes := Ra1295.tableCode_eq ▸ encodesTable_tableCode Ra1295.cycles } 64975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1296.table, code := 41202114065826739703710157823153541185,
        encodes := Ra1296.tableCode_eq ▸ encodesTable_tableCode Ra1296.cycles } 64980
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1297.table, code := 41202114065826739703710157825301024833,
        encodes := Ra1297.tableCode_eq ▸ encodesTable_tableCode Ra1297.cycles } 64981
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1298.table, code := 41202114065826739703782215490205913153,
        encodes := Ra1298.tableCode_eq ▸ encodesTable_tableCode Ra1298.cycles } 64982
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1299.table, code := 41202114065826739703782215492353396801,
        encodes := Ra1299.tableCode_eq ▸ encodesTable_tableCode Ra1299.cycles } 64983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1300.table, code := 41202114065826739706160116160029528129,
        encodes := Ra1300.tableCode_eq ▸ encodesTable_tableCode Ra1300.cycles } 64989
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1301.table, code := 41202114065826739706232173824934416449,
        encodes := Ra1301.tableCode_eq ▸ encodesTable_tableCode Ra1301.cycles } 64990
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1302.table, code := 41202114065826739706232173827081900097,
        encodes := Ra1302.tableCode_eq ▸ encodesTable_tableCode Ra1302.cycles } 64991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1303.table, code := 41204710214260842894878229546251063361,
        encodes := Ra1303.tableCode_eq ▸ encodesTable_tableCode Ra1303.cycles } 65012
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1304.table, code := 41204710214260842894878229548398547009,
        encodes := Ra1304.tableCode_eq ▸ encodesTable_tableCode Ra1304.cycles } 65013
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1305.table, code := 41204710214260842894950287213303435329,
        encodes := Ra1305.tableCode_eq ▸ encodesTable_tableCode Ra1305.cycles } 65014
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1306.table, code := 41204710214260842894950287215450918977,
        encodes := Ra1306.tableCode_eq ▸ encodesTable_tableCode Ra1306.cycles } 65015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1307.table, code := 41204710214260842897328187883127050305,
        encodes := Ra1307.tableCode_eq ▸ encodesTable_tableCode Ra1307.cycles } 65021
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1308.table, code := 41204710214260842897400245548031938625,
        encodes := Ra1308.tableCode_eq ▸ encodesTable_tableCode Ra1308.cycles } 65022
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1309.table, code := 41204710214260842897400245550179422273,
        encodes := Ra1309.tableCode_eq ▸ encodesTable_tableCode Ra1309.cycles } 65023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1310.table, code := 41201951806472536883265425140267356225,
        encodes := Ra1310.tableCode_eq ▸ encodesTable_tableCode Ra1310.cycles } 65487
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1311.table, code := 41202114065826739708321843843728412737,
        encodes := Ra1311.tableCode_eq ▸ encodesTable_tableCode Ra1311.cycles } 65493
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1312.table, code := 41202114065826739708393901510780784705,
        encodes := Ra1312.tableCode_eq ▸ encodesTable_tableCode Ra1312.cycles } 65495
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1313.table, code := 41202114065826739710843859845509288001,
        encodes := Ra1313.tableCode_eq ▸ encodesTable_tableCode Ra1313.cycles } 65503
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1314.table, code := 41204710214260842899489915566825934913,
        encodes := Ra1314.tableCode_eq ▸ encodesTable_tableCode Ra1314.cycles } 65525
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1315.table, code := 41204710214260842899561973233878306881,
        encodes := Ra1315.tableCode_eq ▸ encodesTable_tableCode Ra1315.cycles } 65527
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1316.table, code := 41204710214260842902011931568606810177,
        encodes := Ra1316.tableCode_eq ▸ encodesTable_tableCode Ra1316.cycles } 65535
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 36, ∀ p : Fin 4,
    Data.profiles (1280 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1280 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 36, ∀ p : Fin 4,
    Data.profiles (1280 + i.val) 0 ≤ Data.profiles (1280 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 36,
    Data.profiles (1280 + i.val) 0 = Data.canonicalMask (1280 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 35,
    Data.canonicalMask (1280 + i.val) < Data.canonicalMask (1280 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 36,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1280 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models020
