/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1345
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1346
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1347
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1348
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1349
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1350
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1351
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1352
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1353
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1354
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1355
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1356
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1357
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1358
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1359
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1360
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1361
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1362
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1363
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1364
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1365
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1366
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1367
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1368
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1369
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1370
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1371
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1372
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1373
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1374
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1375
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1376
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1377
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1378
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1379
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1380
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1381
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1382
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1383
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1384
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1385
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1386
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1387
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1388
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1389
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1390
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1391
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1392
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1393
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1394
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1395
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1396
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1397
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1398
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1399
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1400
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1401
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1402
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1403
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1404
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1405
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1406
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1407
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1408

/-!
# Certified models 1345–1408 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models021

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1345.table, code := 9921039824583879984193337582627852353,
        encodes := Ra1345.tableCode_eq ▸ encodesTable_tableCode Ra1345.cycles } 184309
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1346.table, code := 9921039824583879984265395247532740673,
        encodes := Ra1346.tableCode_eq ▸ encodesTable_tableCode Ra1346.cycles } 184310
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1347.table, code := 9921039824583879984265395249680224321,
        encodes := Ra1347.tableCode_eq ▸ encodesTable_tableCode Ra1347.cycles } 184311
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1348.table, code := 9921120954219876739235872291594440769,
        encodes := Ra1348.tableCode_eq ▸ encodesTable_tableCode Ra1348.cycles } 184313
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1349.table, code := 9921120954219876739307929956499329089,
        encodes := Ra1349.tableCode_eq ▸ encodesTable_tableCode Ra1349.cycles } 184314
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1350.table, code := 9921120954219876739307929958646812737,
        encodes := Ra1350.tableCode_eq ▸ encodesTable_tableCode Ra1350.cycles } 184315
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1351.table, code := 9921120954222294590875103755409559617,
        encodes := Ra1351.tableCode_eq ▸ encodesTable_tableCode Ra1351.cycles } 184316
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1352.table, code := 9921120954222294590875103757557043265,
        encodes := Ra1352.tableCode_eq ▸ encodesTable_tableCode Ra1352.cycles } 184317
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1353.table, code := 9921120954222294590947161422461931585,
        encodes := Ra1353.tableCode_eq ▸ encodesTable_tableCode Ra1353.cycles } 184318
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1354.table, code := 9921120954222294590947161424609415233,
        encodes := Ra1354.tableCode_eq ▸ encodesTable_tableCode Ra1354.cycles } 184319
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1355.table, code := 9923473713736320556708008035663220801,
        encodes := Ra1355.tableCode_eq ▸ encodesTable_tableCode Ra1355.cycles } 187303
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1356.table, code := 9923554843374735163389774210592411713,
        encodes := Ra1356.tableCode_eq ▸ encodesTable_tableCode Ra1356.cycles } 187311
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1357.table, code := 9923473713733902707518734904429121601,
        encodes := Ra1357.tableCode_eq ▸ encodesTable_tableCode Ra1357.cycles } 187315
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1358.table, code := 9923473713736320559157966370391724097,
        encodes := Ra1358.tableCode_eq ▸ encodesTable_tableCode Ra1358.cycles } 187319
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1359.table, code := 9923554843372317314200501077210828865,
        encodes := Ra1359.tableCode_eq ▸ encodesTable_tableCode Ra1359.cycles } 187322
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1360.table, code := 9923554843372317314200501079358312513,
        encodes := Ra1360.tableCode_eq ▸ encodesTable_tableCode Ra1360.cycles } 187323
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1361.table, code := 9923554843374735165839732543173431361,
        encodes := Ra1361.tableCode_eq ▸ encodesTable_tableCode Ra1361.cycles } 187326
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1362.table, code := 9923554843374735165839732545320915009,
        encodes := Ra1362.tableCode_eq ▸ encodesTable_tableCode Ra1362.cycles } 187327
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1363.table, code := 9926232121442419545645508334060834881,
        encodes := Ra1363.tableCode_eq ▸ encodesTable_tableCode Ra1363.cycles } 187366
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1364.table, code := 9926232121442419545645508336208318529,
        encodes := Ra1364.tableCode_eq ▸ encodesTable_tableCode Ra1364.cycles } 187367
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1365.table, code := 9926313251080834152327274508990025793,
        encodes := Ra1365.tableCode_eq ▸ encodesTable_tableCode Ra1365.cycles } 187374
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1366.table, code := 9926313251080834152327274511137509441,
        encodes := Ra1366.tableCode_eq ▸ encodesTable_tableCode Ra1366.cycles } 187375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1367.table, code := 9926232121440001696384177537921847361,
        encodes := Ra1367.tableCode_eq ▸ encodesTable_tableCode Ra1367.cycles } 187377
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1368.table, code := 9926232121440001696456235204974219329,
        encodes := Ra1368.tableCode_eq ▸ encodesTable_tableCode Ra1368.cycles } 187379
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1369.table, code := 9926232121442419548023409003884449857,
        encodes := Ra1369.tableCode_eq ▸ encodesTable_tableCode Ra1369.cycles } 187381
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1370.table, code := 9926232121442419548095466670936821825,
        encodes := Ra1370.tableCode_eq ▸ encodesTable_tableCode Ra1370.cycles } 187383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1371.table, code := 9926313251078416303065943712851038273,
        encodes := Ra1371.tableCode_eq ▸ encodesTable_tableCode Ra1371.cycles } 187385
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1372.table, code := 9926313251078416303138001377755926593,
        encodes := Ra1372.tableCode_eq ▸ encodesTable_tableCode Ra1372.cycles } 187386
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1373.table, code := 9926313251078416303138001379903410241,
        encodes := Ra1373.tableCode_eq ▸ encodesTable_tableCode Ra1373.cycles } 187387
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1374.table, code := 9926313251080834154705175176666157121,
        encodes := Ra1374.tableCode_eq ▸ encodesTable_tableCode Ra1374.cycles } 187388
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1375.table, code := 9926313251080834154705175178813640769,
        encodes := Ra1375.tableCode_eq ▸ encodesTable_tableCode Ra1375.cycles } 187389
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1376.table, code := 9926313251080834154777232843718529089,
        encodes := Ra1376.tableCode_eq ▸ encodesTable_tableCode Ra1376.cycles } 187390
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1377.table, code := 9926313251080834154777232845866012737,
        encodes := Ra1377.tableCode_eq ▸ encodesTable_tableCode Ra1377.cycles } 187391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1378.table, code := 9926313248513075642002268022481621057,
        encodes := Ra1378.tableCode_eq ▸ encodesTable_tableCode Ra1378.cycles } 188239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1379.table, code := 9926313248513075644452226357210124353,
        encodes := Ra1379.tableCode_eq ▸ encodesTable_tableCode Ra1379.cycles } 188255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1380.table, code := 9926313248595282671811274150275977281,
        encodes := Ra1380.tableCode_eq ▸ encodesTable_tableCode Ra1380.cycles } 188271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1381.table, code := 9926313248595282674261232485004480577,
        encodes := Ra1381.tableCode_eq ▸ encodesTable_tableCode Ra1381.cycles } 188287
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1382.table, code := 9923554843292528140642412433806463041,
        encodes := Ra1382.tableCode_eq ▸ encodesTable_tableCode Ra1382.cycles } 188318
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1383.table, code := 9923554843292528140642412435953946689,
        encodes := Ra1383.tableCode_eq ▸ encodesTable_tableCode Ra1383.cycles } 188319
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1384.table, code := 9923473713733902709680462588128006209,
        encodes := Ra1384.tableCode_eq ▸ encodesTable_tableCode Ra1384.cycles } 188323
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1385.table, code := 9923473713736320561319694054090608705,
        encodes := Ra1385.tableCode_eq ▸ encodesTable_tableCode Ra1385.cycles } 188327
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1386.table, code := 9923554843372317316362228763057197121,
        encodes := Ra1386.tableCode_eq ▸ encodesTable_tableCode Ra1386.cycles } 188331
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1387.table, code := 9923554843374735168001460226872315969,
        encodes := Ra1387.tableCode_eq ▸ encodesTable_tableCode Ra1387.cycles } 188334
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1388.table, code := 9923554843374735168001460229019799617,
        encodes := Ra1388.tableCode_eq ▸ encodesTable_tableCode Ra1388.cycles } 188335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1389.table, code := 9923473713733902712130420922856509505,
        encodes := Ra1389.tableCode_eq ▸ encodesTable_tableCode Ra1389.cycles } 188339
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1390.table, code := 9923473713736320563769652388819112001,
        encodes := Ra1390.tableCode_eq ▸ encodesTable_tableCode Ra1390.cycles } 188343
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1391.table, code := 9923554843372317318812187095638216769,
        encodes := Ra1391.tableCode_eq ▸ encodesTable_tableCode Ra1391.cycles } 188346
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1392.table, code := 9923554843372317318812187097785700417,
        encodes := Ra1392.tableCode_eq ▸ encodesTable_tableCode Ra1392.cycles } 188347
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1393.table, code := 9923554843374735170451418561600819265,
        encodes := Ra1393.tableCode_eq ▸ encodesTable_tableCode Ra1393.cycles } 188350
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1394.table, code := 9923554843374735170451418563748302913,
        encodes := Ra1394.tableCode_eq ▸ encodesTable_tableCode Ra1394.cycles } 188351
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1395.table, code := 9926232121360212520448188226841350209,
        encodes := Ra1395.tableCode_eq ▸ encodesTable_tableCode Ra1395.cycles } 188359
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1396.table, code := 9926313250998627127129954399623057473,
        encodes := Ra1396.tableCode_eq ▸ encodesTable_tableCode Ra1396.cycles } 188366
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1397.table, code := 9926313250998627127129954401770541121,
        encodes := Ra1397.tableCode_eq ▸ encodesTable_tableCode Ra1397.cycles } 188367
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1398.table, code := 9926232121360212522898146561569853505,
        encodes := Ra1398.tableCode_eq ▸ encodesTable_tableCode Ra1398.cycles } 188375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1399.table, code := 9926313250998627129507855067299188801,
        encodes := Ra1399.tableCode_eq ▸ encodesTable_tableCode Ra1399.cycles } 188380
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1400.table, code := 9926313250998627129507855069446672449,
        encodes := Ra1400.tableCode_eq ▸ encodesTable_tableCode Ra1400.cycles } 188381
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1401.table, code := 9926313250998627129579912734351560769,
        encodes := Ra1401.tableCode_eq ▸ encodesTable_tableCode Ra1401.cycles } 188382
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1402.table, code := 9926313250998627129579912736499044417,
        encodes := Ra1402.tableCode_eq ▸ encodesTable_tableCode Ra1402.cycles } 188383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1403.table, code := 9926232121440001698617962888673103937,
        encodes := Ra1403.tableCode_eq ▸ encodesTable_tableCode Ra1403.cycles } 188387
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1404.table, code := 9926232121442419550257194354635706433,
        encodes := Ra1404.tableCode_eq ▸ encodesTable_tableCode Ra1404.cycles } 188391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1405.table, code := 9926313251078416305299729063602294849,
        encodes := Ra1405.tableCode_eq ▸ encodesTable_tableCode Ra1405.cycles } 188395
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1406.table, code := 9926313251080834156938960527417413697,
        encodes := Ra1406.tableCode_eq ▸ encodesTable_tableCode Ra1406.cycles } 188398
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1407.table, code := 9926313251080834156938960529564897345,
        encodes := Ra1407.tableCode_eq ▸ encodesTable_tableCode Ra1407.cycles } 188399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1408.table, code := 9926232121440001700995863556349235265,
        encodes := Ra1408.tableCode_eq ▸ encodesTable_tableCode Ra1408.cycles } 188401
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1344 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1344 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1344 + i.val) 0 ≤ Data.profiles (1344 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1344 + i.val) 0 = Data.canonicalMask (1344 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1344 + i.val) < Data.canonicalMask (1344 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1344 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models021
