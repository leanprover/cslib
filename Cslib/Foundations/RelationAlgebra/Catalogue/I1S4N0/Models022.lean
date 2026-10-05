/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1409
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1410
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1411
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1412
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1413
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1414
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1415
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1416
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1417
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1418
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1419
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1420
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1421
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1422
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1423
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1424
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1425
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1426
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1427
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1428
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1429
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1430
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1431
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1432
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1433
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1434
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1435
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1436
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1437
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1438
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1439
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1440
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1441
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1442
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1443
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1444
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1445
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1446
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1447
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1448
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1449
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1450
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1451
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1452
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1453
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1454
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1455
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1456
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1457
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1458
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1459
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1460
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1461
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1462
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1463
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1464
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1465
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1466
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1467
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1468
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1469
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1470
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1471
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1472

/-!
# Certified models 1409–1472 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models022

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1409.table, code := 9926232121440001701067921223401607233,
        encodes := Ra1409.tableCode_eq ▸ encodesTable_tableCode Ra1409.cycles } 188403
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1410.table, code := 9926232121442419552635095022311837761,
        encodes := Ra1410.tableCode_eq ▸ encodesTable_tableCode Ra1410.cycles } 188405
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1411.table, code := 9926232121442419552707152689364209729,
        encodes := Ra1411.tableCode_eq ▸ encodesTable_tableCode Ra1411.cycles } 188407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1412.table, code := 9926313251078416307677629731278426177,
        encodes := Ra1412.tableCode_eq ▸ encodesTable_tableCode Ra1412.cycles } 188409
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1413.table, code := 9926313251078416307749687396183314497,
        encodes := Ra1413.tableCode_eq ▸ encodesTable_tableCode Ra1413.cycles } 188410
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1414.table, code := 9926313251078416307749687398330798145,
        encodes := Ra1414.tableCode_eq ▸ encodesTable_tableCode Ra1414.cycles } 188411
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1415.table, code := 9926313251080834159316861195093545025,
        encodes := Ra1415.tableCode_eq ▸ encodesTable_tableCode Ra1415.cycles } 188412
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1416.table, code := 9926313251080834159316861197241028673,
        encodes := Ra1416.tableCode_eq ▸ encodesTable_tableCode Ra1416.cycles } 188413
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1417.table, code := 9926313251080834159388918862145916993,
        encodes := Ra1417.tableCode_eq ▸ encodesTable_tableCode Ra1417.cycles } 188414
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1418.table, code := 9926313251080834159388918864293400641,
        encodes := Ra1418.tableCode_eq ▸ encodesTable_tableCode Ra1418.cycles } 188415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1419.table, code := 9918362551620280550701146177829867585,
        encodes := Ra1419.tableCode_eq ▸ encodesTable_tableCode Ra1419.cycles } 190393
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1420.table, code := 9918362551620280550773203842734755905,
        encodes := Ra1420.tableCode_eq ▸ encodesTable_tableCode Ra1420.cycles } 190394
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1421.table, code := 9918362551620280550773203844882239553,
        encodes := Ra1421.tableCode_eq ▸ encodesTable_tableCode Ra1421.cycles } 190395
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1422.table, code := 9918362551622698402340377641644986433,
        encodes := Ra1422.tableCode_eq ▸ encodesTable_tableCode Ra1422.cycles } 190396
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1423.table, code := 9918362551622698402340377643792470081,
        encodes := Ra1423.tableCode_eq ▸ encodesTable_tableCode Ra1423.cycles } 190397
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1424.table, code := 9918362551622698402412435308697358401,
        encodes := Ra1424.tableCode_eq ▸ encodesTable_tableCode Ra1424.cycles } 190398
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1425.table, code := 9918362551622698402412435310844842049,
        encodes := Ra1425.tableCode_eq ▸ encodesTable_tableCode Ra1425.cycles } 190399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1426.table, code := 9921039829687964930578979635769643073,
        encodes := Ra1426.tableCode_eq ▸ encodesTable_tableCode Ra1426.cycles } 190435
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1427.table, code := 9921039829690382782218211101732245569,
        encodes := Ra1427.tableCode_eq ▸ encodesTable_tableCode Ra1427.cycles } 190439
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1428.table, code := 9921120959326379537260745808551350337,
        encodes := Ra1428.tableCode_eq ▸ encodesTable_tableCode Ra1428.cycles } 190442
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1429.table, code := 9921120959326379537260745810698833985,
        encodes := Ra1429.tableCode_eq ▸ encodesTable_tableCode Ra1429.cycles } 190443
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1430.table, code := 9921120959328797388899977274513952833,
        encodes := Ra1430.tableCode_eq ▸ encodesTable_tableCode Ra1430.cycles } 190446
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1431.table, code := 9921120959328797388899977276661436481,
        encodes := Ra1431.tableCode_eq ▸ encodesTable_tableCode Ra1431.cycles } 190447
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1432.table, code := 9921039829687964933028937970498146369,
        encodes := Ra1432.tableCode_eq ▸ encodesTable_tableCode Ra1432.cycles } 190451
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1433.table, code := 9921039829690382784596111769408376897,
        encodes := Ra1433.tableCode_eq ▸ encodesTable_tableCode Ra1433.cycles } 190453
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1434.table, code := 9921039829690382784668169436460748865,
        encodes := Ra1434.tableCode_eq ▸ encodesTable_tableCode Ra1434.cycles } 190455
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1435.table, code := 9921120959326379539638646478374965313,
        encodes := Ra1435.tableCode_eq ▸ encodesTable_tableCode Ra1435.cycles } 190457
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1436.table, code := 9921120959326379539710704143279853633,
        encodes := Ra1436.tableCode_eq ▸ encodesTable_tableCode Ra1436.cycles } 190458
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1437.table, code := 9921120959326379539710704145427337281,
        encodes := Ra1437.tableCode_eq ▸ encodesTable_tableCode Ra1437.cycles } 190459
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1438.table, code := 9921120959328797391277877942190084161,
        encodes := Ra1438.tableCode_eq ▸ encodesTable_tableCode Ra1438.cycles } 190460
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1439.table, code := 9921120959328797391277877944337567809,
        encodes := Ra1439.tableCode_eq ▸ encodesTable_tableCode Ra1439.cycles } 190461
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1440.table, code := 9921120959328797391349935609242456129,
        encodes := Ra1440.tableCode_eq ▸ encodesTable_tableCode Ra1440.cycles } 190462
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1441.table, code := 9921120959328797391349935611389939777,
        encodes := Ra1441.tableCode_eq ▸ encodesTable_tableCode Ra1441.cycles } 190463
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1442.table, code := 9918281422139026454988707962080727105,
        encodes := Ra1442.tableCode_eq ▸ encodesTable_tableCode Ra1442.cycles } 192423
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1443.table, code := 9918362551775023210031242668899831873,
        encodes := Ra1443.tableCode_eq ▸ encodesTable_tableCode Ra1443.cycles } 192426
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1444.table, code := 9918362551775023210031242671047315521,
        encodes := Ra1444.tableCode_eq ▸ encodesTable_tableCode Ra1444.cycles } 192427
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1445.table, code := 9918362551777441061670474134862434369,
        encodes := Ra1445.tableCode_eq ▸ encodesTable_tableCode Ra1445.cycles } 192430
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1446.table, code := 9918362551777441061670474137009918017,
        encodes := Ra1446.tableCode_eq ▸ encodesTable_tableCode Ra1446.cycles } 192431
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1447.table, code := 9918281422139026457438666296809230401,
        encodes := Ra1447.tableCode_eq ▸ encodesTable_tableCode Ra1447.cycles } 192439
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1448.table, code := 9918362551775023212409143338723446849,
        encodes := Ra1448.tableCode_eq ▸ encodesTable_tableCode Ra1448.cycles } 192441
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1449.table, code := 9918362551775023212481201003628335169,
        encodes := Ra1449.tableCode_eq ▸ encodesTable_tableCode Ra1449.cycles } 192442
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1450.table, code := 9918362551775023212481201005775818817,
        encodes := Ra1450.tableCode_eq ▸ encodesTable_tableCode Ra1450.cycles } 192443
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1451.table, code := 9918362551777441064048374802538565697,
        encodes := Ra1451.tableCode_eq ▸ encodesTable_tableCode Ra1451.cycles } 192444
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1452.table, code := 9918362551777441064048374804686049345,
        encodes := Ra1452.tableCode_eq ▸ encodesTable_tableCode Ra1452.cycles } 192445
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1453.table, code := 9918362551777441064120432469590937665,
        encodes := Ra1453.tableCode_eq ▸ encodesTable_tableCode Ra1453.cycles } 192446
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1454.table, code := 9918362551777441064120432471738421313,
        encodes := Ra1454.tableCode_eq ▸ encodesTable_tableCode Ra1454.cycles } 192447
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1455.table, code := 9921039829762918414117202134831468609,
        encodes := Ra1455.tableCode_eq ▸ encodesTable_tableCode Ra1455.cycles } 192455
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1456.table, code := 9921120959401333020798968307613175873,
        encodes := Ra1456.tableCode_eq ▸ encodesTable_tableCode Ra1456.cycles } 192462
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1457.table, code := 9921120959401333020798968309760659521,
        encodes := Ra1457.tableCode_eq ▸ encodesTable_tableCode Ra1457.cycles } 192463
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1458.table, code := 9921039829762918416567160469559971905,
        encodes := Ra1458.tableCode_eq ▸ encodesTable_tableCode Ra1458.cycles } 192471
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1459.table, code := 9921120959401333023176868975289307201,
        encodes := Ra1459.tableCode_eq ▸ encodesTable_tableCode Ra1459.cycles } 192476
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1460.table, code := 9921120959401333023176868977436790849,
        encodes := Ra1460.tableCode_eq ▸ encodesTable_tableCode Ra1460.cycles } 192477
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1461.table, code := 9921120959401333023248926642341679169,
        encodes := Ra1461.tableCode_eq ▸ encodesTable_tableCode Ra1461.cycles } 192478
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1462.table, code := 9921120959401333023248926644489162817,
        encodes := Ra1462.tableCode_eq ▸ encodesTable_tableCode Ra1462.cycles } 192479
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1463.table, code := 9921039829845125443926208262625824833,
        encodes := Ra1463.tableCode_eq ▸ encodesTable_tableCode Ra1463.cycles } 192487
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1464.table, code := 9921120959481122198968742969444929601,
        encodes := Ra1464.tableCode_eq ▸ encodesTable_tableCode Ra1464.cycles } 192490
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1465.table, code := 9921120959481122198968742971592413249,
        encodes := Ra1465.tableCode_eq ▸ encodesTable_tableCode Ra1465.cycles } 192491
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1466.table, code := 9921120959483540050607974435407532097,
        encodes := Ra1466.tableCode_eq ▸ encodesTable_tableCode Ra1466.cycles } 192494
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1467.table, code := 9921120959483540050607974437555015745,
        encodes := Ra1467.tableCode_eq ▸ encodesTable_tableCode Ra1467.cycles } 192495
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1468.table, code := 9921039829845125446376166597354328129,
        encodes := Ra1468.tableCode_eq ▸ encodesTable_tableCode Ra1468.cycles } 192503
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1469.table, code := 9921120959481122201346643639268544577,
        encodes := Ra1469.tableCode_eq ▸ encodesTable_tableCode Ra1469.cycles } 192505
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1470.table, code := 9921120959481122201418701304173432897,
        encodes := Ra1470.tableCode_eq ▸ encodesTable_tableCode Ra1470.cycles } 192506
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1471.table, code := 9921120959481122201418701306320916545,
        encodes := Ra1471.tableCode_eq ▸ encodesTable_tableCode Ra1471.cycles } 192507
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1472.table, code := 9921120959483540052985875103083663425,
        encodes := Ra1472.tableCode_eq ▸ encodesTable_tableCode Ra1472.cycles } 192508
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1408 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1408 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1408 + i.val) 0 ≤ Data.profiles (1408 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1408 + i.val) 0 = Data.canonicalMask (1408 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1408 + i.val) < Data.canonicalMask (1408 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1408 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models022
