/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1537
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1538
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1539
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1540
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1541
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1542
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1543
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1544
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1545
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1546
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1547
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1548
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1549
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1550
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1551
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1552
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1553
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1554
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1555
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1556
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1557
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1558
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1559
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1560
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1561
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1562
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1563
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1564
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1565
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1566
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1567
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1568
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1569
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1570
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1571
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1572
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1573
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1574
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1575
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1576
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1577
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1578
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1579
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1580
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1581
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1582
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1583
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1584
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1585
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1586
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1587
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1588
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1589
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1590
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1591
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1592
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1593
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1594
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1595
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1596
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1597
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1598
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1599
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1600

/-!
# Certified models 1537–1600 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models024

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1537.table, code := 4325934082816598692886963674595725377,
        encodes := Ra1537.tableCode_eq ▸ encodesTable_tableCode Ra1537.cycles } 204441
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1538.table, code := 4409254298232771448878484411130318913,
        encodes := Ra1538.tableCode_eq ▸ encodesTable_tableCode Ra1538.cycles } 204565
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1539.table, code := 4409335427871186055560250583912026177,
        encodes := Ra1539.tableCode_eq ▸ encodesTable_tableCode Ra1539.cycles } 204572
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1540.table, code := 4409335427871186055560250586059509825,
        encodes := Ra1540.tableCode_eq ▸ encodesTable_tableCode Ra1540.cycles } 204573
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1541.table, code := 4409254300718322934006170790419238977,
        encodes := Ra1541.tableCode_eq ▸ encodesTable_tableCode Ra1541.cycles } 204693
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1542.table, code := 4409335430356737540687936963200946241,
        encodes := Ra1542.tableCode_eq ▸ encodesTable_tableCode Ra1542.cycles } 204700
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1543.table, code := 4409335430356737540687936965348429889,
        encodes := Ra1543.tableCode_eq ▸ encodesTable_tableCode Ra1543.cycles } 204701
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1544.table, code := 4412012708506628950374776551082561601,
        encodes := Ra1544.tableCode_eq ▸ encodesTable_tableCode Ra1544.cycles } 204775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1545.table, code := 4412093838145043557056542723864268865,
        encodes := Ra1545.tableCode_eq ▸ encodesTable_tableCode Ra1545.cycles } 204782
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1546.table, code := 4412093838145043557056542726011752513,
        encodes := Ra1546.tableCode_eq ▸ encodesTable_tableCode Ra1546.cycles } 204783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1547.table, code := 4412012708506628952824734885811064897,
        encodes := Ra1547.tableCode_eq ▸ encodesTable_tableCode Ra1547.cycles } 204791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1548.table, code := 4412093838145043559506501058592772161,
        encodes := Ra1548.tableCode_eq ▸ encodesTable_tableCode Ra1548.cycles } 204798
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1549.table, code := 4412093838145043559506501060740255809,
        encodes := Ra1549.tableCode_eq ▸ encodesTable_tableCode Ra1549.cycles } 204799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1550.table, code := 1666829059403113407447280772729540673,
        encodes := Ra1550.tableCode_eq ▸ encodesTable_tableCode Ra1550.cycles } 212127
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1551.table, code := 1666829059485320437256286900523896897,
        encodes := Ra1551.tableCode_eq ▸ encodesTable_tableCode Ra1551.cycles } 212159
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1552.table, code := 4325852958439429548315968847340638273,
        encodes := Ra1552.tableCode_eq ▸ encodesTable_tableCode Ra1552.cycles } 212625
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1553.table, code := 4325934088077844154997735020122345537,
        encodes := Ra1553.tableCode_eq ▸ encodesTable_tableCode Ra1553.cycles } 212632
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1554.table, code := 4325934088077844154997735022269829185,
        encodes := Ra1554.tableCode_eq ▸ encodesTable_tableCode Ra1554.cycles } 212633
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1555.table, code := 4412012711282322927357861519467745345,
        encodes := Ra1555.tableCode_eq ▸ encodesTable_tableCode Ra1555.cycles } 212839
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1556.table, code := 4412093840920737534039627692249452609,
        encodes := Ra1556.tableCode_eq ▸ encodesTable_tableCode Ra1556.cycles } 212846
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1557.table, code := 4412093840920737534039627694396936257,
        encodes := Ra1557.tableCode_eq ▸ encodesTable_tableCode Ra1557.cycles } 212847
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1558.table, code := 4412012711282322929807819854196248641,
        encodes := Ra1558.tableCode_eq ▸ encodesTable_tableCode Ra1558.cycles } 212855
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1559.table, code := 4412093840920737536489586026977955905,
        encodes := Ra1559.tableCode_eq ▸ encodesTable_tableCode Ra1559.cycles } 212862
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1560.table, code := 4412093840920737536489586029125439553,
        encodes := Ra1560.tableCode_eq ▸ encodesTable_tableCode Ra1560.cycles } 212863
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1561.table, code := 4412012713767874414935506233485168705,
        encodes := Ra1561.tableCode_eq ▸ encodesTable_tableCode Ra1561.cycles } 212983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1562.table, code := 4412093843406289021617272406266875969,
        encodes := Ra1562.tableCode_eq ▸ encodesTable_tableCode Ra1562.cycles } 212990
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1563.table, code := 4412093843406289021617272408414359617,
        encodes := Ra1563.tableCode_eq ▸ encodesTable_tableCode Ra1563.cycles } 212991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1564.table, code := 4588550958131824026109271308627087425,
        encodes := Ra1564.tableCode_eq ▸ encodesTable_tableCode Ra1564.cycles } 218983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1565.table, code := 4588632087770238632791037481408794689,
        encodes := Ra1565.tableCode_eq ▸ encodesTable_tableCode Ra1565.cycles } 218990
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1566.table, code := 4588632087770238632791037483556278337,
        encodes := Ra1566.tableCode_eq ▸ encodesTable_tableCode Ra1566.cycles } 218991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1567.table, code := 4588550958131824028559229643355590721,
        encodes := Ra1567.tableCode_eq ▸ encodesTable_tableCode Ra1567.cycles } 218999
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1568.table, code := 4588632087770238635240995816137297985,
        encodes := Ra1568.tableCode_eq ▸ encodesTable_tableCode Ra1568.cycles } 219006
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1569.table, code := 4588632087770238635240995818284781633,
        encodes := Ra1569.tableCode_eq ▸ encodesTable_tableCode Ra1569.cycles } 219007
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1570.table, code := 4588550960617375513686916022644510785,
        encodes := Ra1570.tableCode_eq ▸ encodesTable_tableCode Ra1570.cycles } 219127
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1571.table, code := 4588632090255790120368682195426218049,
        encodes := Ra1571.tableCode_eq ▸ encodesTable_tableCode Ra1571.cycles } 219134
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1572.table, code := 4588632090255790120368682197573701697,
        encodes := Ra1572.tableCode_eq ▸ encodesTable_tableCode Ra1572.cycles } 219135
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1573.table, code := 4502391203040328853456695545898995777,
        encodes := Ra1573.tableCode_eq ▸ encodesTable_tableCode Ra1573.cycles } 220721
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1574.table, code := 4502472332678743460138461720828186689,
        encodes := Ra1574.tableCode_eq ▸ encodesTable_tableCode Ra1574.cycles } 220729
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1575.table, code := 4505149610748845691655526644730564673,
        encodes := Ra1575.tableCode_eq ▸ encodesTable_tableCode Ra1575.cycles } 220775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1576.table, code := 4505230740387260298337292817512271937,
        encodes := Ra1576.tableCode_eq ▸ encodesTable_tableCode Ra1576.cycles } 220782
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1577.table, code := 4505230740387260298337292819659755585,
        encodes := Ra1577.tableCode_eq ▸ encodesTable_tableCode Ra1577.cycles } 220783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1578.table, code := 4505149610748845694105484979459067969,
        encodes := Ra1578.tableCode_eq ▸ encodesTable_tableCode Ra1578.cycles } 220791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1579.table, code := 4505230740387260300787251152240775233,
        encodes := Ra1579.tableCode_eq ▸ encodesTable_tableCode Ra1579.cycles } 220798
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1580.table, code := 4505230740387260300787251154388258881,
        encodes := Ra1580.tableCode_eq ▸ encodesTable_tableCode Ra1580.cycles } 220799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1581.table, code := 4502391205525880338584381925187915841,
        encodes := Ra1581.tableCode_eq ▸ encodesTable_tableCode Ra1581.cycles } 220849
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1582.table, code := 4502472335164294945266148097969623105,
        encodes := Ra1582.tableCode_eq ▸ encodesTable_tableCode Ra1582.cycles } 220856
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1583.table, code := 4502472335164294945266148100117106753,
        encodes := Ra1583.tableCode_eq ▸ encodesTable_tableCode Ra1583.cycles } 220857
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1584.table, code := 4505149613234397176783213024019484737,
        encodes := Ra1584.tableCode_eq ▸ encodesTable_tableCode Ra1584.cycles } 220903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1585.table, code := 4505230742872811783464979196801192001,
        encodes := Ra1585.tableCode_eq ▸ encodesTable_tableCode Ra1585.cycles } 220910
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1586.table, code := 4505230742872811783464979198948675649,
        encodes := Ra1586.tableCode_eq ▸ encodesTable_tableCode Ra1586.cycles } 220911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1587.table, code := 4505149613234397179233171358747988033,
        encodes := Ra1587.tableCode_eq ▸ encodesTable_tableCode Ra1587.cycles } 220919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1588.table, code := 4505230742872811785914937531529695297,
        encodes := Ra1588.tableCode_eq ▸ encodesTable_tableCode Ra1588.cycles } 220926
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1589.table, code := 4505230742872811785914937533677178945,
        encodes := Ra1589.tableCode_eq ▸ encodesTable_tableCode Ra1589.cycles } 220927
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1590.table, code := 4585792550580467698879768168975568961,
        encodes := Ra1590.tableCode_eq ▸ encodesTable_tableCode Ra1590.cycles } 220967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1591.table, code := 4585873680218882305561534341757276225,
        encodes := Ra1591.tableCode_eq ▸ encodesTable_tableCode Ra1591.cycles } 220974
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1592.table, code := 4585873680218882305561534343904759873,
        encodes := Ra1592.tableCode_eq ▸ encodesTable_tableCode Ra1592.cycles } 220975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1593.table, code := 4585792550580467701329726503704072257,
        encodes := Ra1593.tableCode_eq ▸ encodesTable_tableCode Ra1593.cycles } 220983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1594.table, code := 4585873680218882308011492676485779521,
        encodes := Ra1594.tableCode_eq ▸ encodesTable_tableCode Ra1594.cycles } 220990
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1595.table, code := 4585873680218882308011492678633263169,
        encodes := Ra1595.tableCode_eq ▸ encodesTable_tableCode Ra1595.cycles } 220991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1596.table, code := 4588550958286566687817268469520666689,
        encodes := Ra1596.tableCode_eq ▸ encodesTable_tableCode Ra1596.cycles } 221031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1597.table, code := 4588632087924981294499034642302373953,
        encodes := Ra1597.tableCode_eq ▸ encodesTable_tableCode Ra1597.cycles } 221038
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1598.table, code := 4588632087924981294499034644449857601,
        encodes := Ra1598.tableCode_eq ▸ encodesTable_tableCode Ra1598.cycles } 221039
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1599.table, code := 4588550958286566690267226804249169985,
        encodes := Ra1599.tableCode_eq ▸ encodesTable_tableCode Ra1599.cycles } 221047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1600.table, code := 4588632087924981296948992977030877249,
        encodes := Ra1600.tableCode_eq ▸ encodesTable_tableCode Ra1600.cycles } 221054
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1536 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1536 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1536 + i.val) 0 ≤ Data.profiles (1536 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1536 + i.val) 0 = Data.canonicalMask (1536 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1536 + i.val) < Data.canonicalMask (1536 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1536 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models024
