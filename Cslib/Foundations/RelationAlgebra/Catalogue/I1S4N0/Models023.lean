/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1473
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1474
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1475
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1476
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1477
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1478
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1479
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1480
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1481
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1482
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1483
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1484
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1485
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1486
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1487
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1488
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1489
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1490
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1491
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1492
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1493
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1494
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1495
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1496
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1497
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1498
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1499
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1500
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1501
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1502
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1503
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1504
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1505
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1506
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1507
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1508
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1509
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1510
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1511
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1512
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1513
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1514
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1515
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1516
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1517
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1518
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1519
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1520
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1521
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1522
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1523
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1524
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1525
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1526
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1527
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1528
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1529
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1530
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1531
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1532
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1533
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1534
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1535
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1536

/-!
# Certified models 1473–1536 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models023

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1473.table, code := 9921120959483540052985875105231147073,
        encodes := Ra1473.tableCode_eq ▸ encodesTable_tableCode Ra1473.cycles } 192509
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1474.table, code := 9921120959483540053057932770136035393,
        encodes := Ra1474.tableCode_eq ▸ encodesTable_tableCode Ra1474.cycles } 192510
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1475.table, code := 9921120959483540053057932772283519041,
        encodes := Ra1475.tableCode_eq ▸ encodesTable_tableCode Ra1475.cycles } 192511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1476.table, code := 9923554848478820114603275263991353409,
        encodes := Ra1476.tableCode_eq ▸ encodesTable_tableCode Ra1476.cycles } 193466
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1477.table, code := 9923554848478820114603275266138837057,
        encodes := Ra1477.tableCode_eq ▸ encodesTable_tableCode Ra1477.cycles } 193467
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1478.table, code := 9923554848481237966242506729953955905,
        encodes := Ra1478.tableCode_eq ▸ encodesTable_tableCode Ra1478.cycles } 193470
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1479.table, code := 9923554848481237966242506732101439553,
        encodes := Ra1479.tableCode_eq ▸ encodesTable_tableCode Ra1479.cycles } 193471
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1480.table, code := 9926313256184919103540775564536451137,
        encodes := Ra1480.tableCode_eq ▸ encodesTable_tableCode Ra1480.cycles } 193530
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1481.table, code := 9926313256184919103540775566683934785,
        encodes := Ra1481.tableCode_eq ▸ encodesTable_tableCode Ra1481.cycles } 193531
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1482.table, code := 9926313256187336955180007030499053633,
        encodes := Ra1482.tableCode_eq ▸ encodesTable_tableCode Ra1482.cycles } 193534
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1483.table, code := 9926313256187336955180007032646537281,
        encodes := Ra1483.tableCode_eq ▸ encodesTable_tableCode Ra1483.cycles } 193535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1484.table, code := 9923554848478820116765002949837721665,
        encodes := Ra1484.tableCode_eq ▸ encodesTable_tableCode Ra1484.cycles } 194475
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1485.table, code := 9923554848481237968404234413652840513,
        encodes := Ra1485.tableCode_eq ▸ encodesTable_tableCode Ra1485.cycles } 194478
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1486.table, code := 9923554848481237968404234415800324161,
        encodes := Ra1486.tableCode_eq ▸ encodesTable_tableCode Ra1486.cycles } 194479
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1487.table, code := 9923554848478820119214961284566224961,
        encodes := Ra1487.tableCode_eq ▸ encodesTable_tableCode Ra1487.cycles } 194491
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1488.table, code := 9923554848481237970782135081328971841,
        encodes := Ra1488.tableCode_eq ▸ encodesTable_tableCode Ra1488.cycles } 194492
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1489.table, code := 9923554848481237970782135083476455489,
        encodes := Ra1489.tableCode_eq ▸ encodesTable_tableCode Ra1489.cycles } 194493
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1490.table, code := 9923554848481237970854192748381343809,
        encodes := Ra1490.tableCode_eq ▸ encodesTable_tableCode Ra1490.cycles } 194494
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1491.table, code := 9923554848481237970854192750528827457,
        encodes := Ra1491.tableCode_eq ▸ encodesTable_tableCode Ra1491.cycles } 194495
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1492.table, code := 9926313256184919105702503250382819393,
        encodes := Ra1492.tableCode_eq ▸ encodesTable_tableCode Ra1492.cycles } 194539
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1493.table, code := 9926313256187336957341734714197938241,
        encodes := Ra1493.tableCode_eq ▸ encodesTable_tableCode Ra1493.cycles } 194542
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1494.table, code := 9926313256187336957341734716345421889,
        encodes := Ra1494.tableCode_eq ▸ encodesTable_tableCode Ra1494.cycles } 194543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1495.table, code := 9926313256184919108152461585111322689,
        encodes := Ra1495.tableCode_eq ▸ encodesTable_tableCode Ra1495.cycles } 194555
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1496.table, code := 9926313256187336959719635381874069569,
        encodes := Ra1496.tableCode_eq ▸ encodesTable_tableCode Ra1496.cycles } 194556
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1497.table, code := 9926313256187336959719635384021553217,
        encodes := Ra1497.tableCode_eq ▸ encodesTable_tableCode Ra1497.cycles } 194557
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1498.table, code := 9926313256187336959791693048926441537,
        encodes := Ra1498.tableCode_eq ▸ encodesTable_tableCode Ra1498.cycles } 194558
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1499.table, code := 9926313256187336959791693051073925185,
        encodes := Ra1499.tableCode_eq ▸ encodesTable_tableCode Ra1499.cycles } 194559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1500.table, code := 9923554848553773598141497763053178945,
        encodes := Ra1500.tableCode_eq ▸ encodesTable_tableCode Ra1500.cycles } 195486
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1501.table, code := 9923554848553773598141497765200662593,
        encodes := Ra1501.tableCode_eq ▸ encodesTable_tableCode Ra1501.cycles } 195487
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1502.table, code := 9923554848635980625500545558266515521,
        encodes := Ra1502.tableCode_eq ▸ encodesTable_tableCode Ra1502.cycles } 195503
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1503.table, code := 9923554848635980627878446225942646849,
        encodes := Ra1503.tableCode_eq ▸ encodesTable_tableCode Ra1503.cycles } 195517
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1504.table, code := 9923554848635980627950503890847535169,
        encodes := Ra1504.tableCode_eq ▸ encodesTable_tableCode Ra1504.cycles } 195518
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1505.table, code := 9923554848635980627950503892995018817,
        encodes := Ra1505.tableCode_eq ▸ encodesTable_tableCode Ra1505.cycles } 195519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1506.table, code := 9926313256259872584629039731017257025,
        encodes := Ra1506.tableCode_eq ▸ encodesTable_tableCode Ra1506.cycles } 195535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1507.table, code := 9926313256259872587006940398693388353,
        encodes := Ra1507.tableCode_eq ▸ encodesTable_tableCode Ra1507.cycles } 195549
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1508.table, code := 9926313256259872587078998063598276673,
        encodes := Ra1508.tableCode_eq ▸ encodesTable_tableCode Ra1508.cycles } 195550
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1509.table, code := 9926313256259872587078998065745760321,
        encodes := Ra1509.tableCode_eq ▸ encodesTable_tableCode Ra1509.cycles } 195551
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1510.table, code := 9926313256342079614438045856664129601,
        encodes := Ra1510.tableCode_eq ▸ encodesTable_tableCode Ra1510.cycles } 195566
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1511.table, code := 9926313256342079614438045858811613249,
        encodes := Ra1511.tableCode_eq ▸ encodesTable_tableCode Ra1511.cycles } 195567
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1512.table, code := 9926313256342079616815946526487744577,
        encodes := Ra1512.tableCode_eq ▸ encodesTable_tableCode Ra1512.cycles } 195581
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1513.table, code := 9926313256342079616888004191392632897,
        encodes := Ra1513.tableCode_eq ▸ encodesTable_tableCode Ra1513.cycles } 195582
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1514.table, code := 9926313256342079616888004193540116545,
        encodes := Ra1514.tableCode_eq ▸ encodesTable_tableCode Ra1514.cycles } 195583
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1515.table, code := 9923554848553773602753183783628050497,
        encodes := Ra1515.tableCode_eq ▸ encodesTable_tableCode Ra1515.cycles } 196511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1516.table, code := 9923554848635980630112231576693903425,
        encodes := Ra1516.tableCode_eq ▸ encodesTable_tableCode Ra1516.cycles } 196527
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1517.table, code := 9923554848635980632562189911422406721,
        encodes := Ra1517.tableCode_eq ▸ encodesTable_tableCode Ra1517.cycles } 196543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1518.table, code := 9926313256259872589240725749444644929,
        encodes := Ra1518.tableCode_eq ▸ encodesTable_tableCode Ra1518.cycles } 196559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1519.table, code := 9926313256259872591690684084173148225,
        encodes := Ra1519.tableCode_eq ▸ encodesTable_tableCode Ra1519.cycles } 196575
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1520.table, code := 9926313256342079619049731877239001153,
        encodes := Ra1520.tableCode_eq ▸ encodesTable_tableCode Ra1520.cycles } 196591
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1521.table, code := 9926313256342079621499690211967504449,
        encodes := Ra1521.tableCode_eq ▸ encodesTable_tableCode Ra1521.cycles } 196607
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1522.table, code := 1666829051583780825859873677938790465,
        encodes := Ra1522.tableCode_eq ▸ encodesTable_tableCode Ra1522.cycles } 201775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1523.table, code := 1666829051583780828309832012667293761,
        encodes := Ra1523.tableCode_eq ▸ encodesTable_tableCode Ra1523.cycles } 201791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1524.table, code := 1666829054069332313437518391956213825,
        encodes := Ra1524.tableCode_eq ▸ encodesTable_tableCode Ra1524.cycles } 201919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1525.table, code := 4412093837990300897798503899846676545,
        encodes := Ra1525.tableCode_eq ▸ encodesTable_tableCode Ra1525.cycles } 202751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1526.table, code := 1666829051656316457758864711038013505,
        encodes := Ra1526.tableCode_eq ▸ encodesTable_tableCode Ra1526.cycles } 203791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1527.table, code := 1666829051656316460208823045766516801,
        encodes := Ra1527.tableCode_eq ▸ encodesTable_tableCode Ra1527.cycles } 203807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1528.table, code := 1666829051738523487567870838832369729,
        encodes := Ra1528.tableCode_eq ▸ encodesTable_tableCode Ra1528.cycles } 203823
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1529.table, code := 1666829051738523490017829173560873025,
        encodes := Ra1529.tableCode_eq ▸ encodesTable_tableCode Ra1529.cycles } 203839
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1530.table, code := 1666829054141867945264451758003064897,
        encodes := Ra1530.tableCode_eq ▸ encodesTable_tableCode Ra1530.cycles } 203933
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1531.table, code := 1666829054221657121056325752158687297,
        encodes := Ra1531.tableCode_eq ▸ encodesTable_tableCode Ra1531.cycles } 203947
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1532.table, code := 1666829054224074972695557218121289793,
        encodes := Ra1532.tableCode_eq ▸ encodesTable_tableCode Ra1532.cycles } 203951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1533.table, code := 1666829054224074975073457885797421121,
        encodes := Ra1533.tableCode_eq ▸ encodesTable_tableCode Ra1533.cycles } 203965
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1534.table, code := 1666829054224074975145515552849793089,
        encodes := Ra1534.tableCode_eq ▸ encodesTable_tableCode Ra1534.cycles } 203967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1535.table, code := 4325852953178184086205197499666534465,
        encodes := Ra1535.tableCode_eq ▸ encodesTable_tableCode Ra1535.cycles } 204433
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1536.table, code := 4325934082816598692886963672448241729,
        encodes := Ra1536.tableCode_eq ▸ encodesTable_tableCode Ra1536.cycles } 204440
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1472 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1472 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1472 + i.val) 0 ≤ Data.profiles (1472 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1472 + i.val) 0 = Data.canonicalMask (1472 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1472 + i.val) < Data.canonicalMask (1472 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1472 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models023
