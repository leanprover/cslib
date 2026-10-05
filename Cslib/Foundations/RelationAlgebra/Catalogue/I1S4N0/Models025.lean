/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1601
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1602
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1603
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1604
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1605
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1606
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1607
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1608
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1609
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1610
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1611
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1612
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1613
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1614
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1615
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1616
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1617
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1618
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1619
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1620
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1621
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1622
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1623
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1624
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1625
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1626
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1627
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1628
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1629
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1630
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1631
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1632
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1633
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1634
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1635
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1636
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1637
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1638
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1639
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1640
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1641
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1642
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1643
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1644
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1645
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1646
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1647
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1648
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1649
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1650
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1651
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1652
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1653
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1654
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1655
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1656
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1657
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1658
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1659
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1660
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1661
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1662
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1663
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1664

/-!
# Certified models 1601–1664 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models025

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1601.table, code := 4588632087924981296948992979178360897,
        encodes := Ra1601.tableCode_eq ▸ encodesTable_tableCode Ra1601.cycles } 221055
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1602.table, code := 4585792553066019184007454548264489025,
        encodes := Ra1602.tableCode_eq ▸ encodesTable_tableCode Ra1602.cycles } 221095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1603.table, code := 4585873682704433790689220721046196289,
        encodes := Ra1603.tableCode_eq ▸ encodesTable_tableCode Ra1603.cycles } 221102
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1604.table, code := 4585873682704433790689220723193679937,
        encodes := Ra1604.tableCode_eq ▸ encodesTable_tableCode Ra1604.cycles } 221103
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1605.table, code := 4585792553066019186457412882992992321,
        encodes := Ra1605.tableCode_eq ▸ encodesTable_tableCode Ra1605.cycles } 221111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1606.table, code := 4585873682704433793139179055774699585,
        encodes := Ra1606.tableCode_eq ▸ encodesTable_tableCode Ra1606.cycles } 221118
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1607.table, code := 4585873682704433793139179057922183233,
        encodes := Ra1607.tableCode_eq ▸ encodesTable_tableCode Ra1607.cycles } 221119
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1608.table, code := 4588550960772118172944954848809586753,
        encodes := Ra1608.tableCode_eq ▸ encodesTable_tableCode Ra1608.cycles } 221159
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1609.table, code := 4588632090410532779626721021591294017,
        encodes := Ra1609.tableCode_eq ▸ encodesTable_tableCode Ra1609.cycles } 221166
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1610.table, code := 4588632090410532779626721023738777665,
        encodes := Ra1610.tableCode_eq ▸ encodesTable_tableCode Ra1610.cycles } 221167
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1611.table, code := 4588550960772118175394913183538090049,
        encodes := Ra1611.tableCode_eq ▸ encodesTable_tableCode Ra1611.cycles } 221175
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1612.table, code := 4588632090410532782076679356319797313,
        encodes := Ra1612.tableCode_eq ▸ encodesTable_tableCode Ra1612.cycles } 221182
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1613.table, code := 4588632090410532782076679358467280961,
        encodes := Ra1613.tableCode_eq ▸ encodesTable_tableCode Ra1613.cycles } 221183
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1614.table, code := 4502391208301574315567466893573099585,
        encodes := Ra1614.tableCode_eq ▸ encodesTable_tableCode Ra1614.cycles } 228913
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1615.table, code := 4502472337939988922249233068502290497,
        encodes := Ra1615.tableCode_eq ▸ encodesTable_tableCode Ra1615.cycles } 228921
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1616.table, code := 4505149616010091153766297992404668481,
        encodes := Ra1616.tableCode_eq ▸ encodesTable_tableCode Ra1616.cycles } 228967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1617.table, code := 4505230745648505760448064165186375745,
        encodes := Ra1617.tableCode_eq ▸ encodesTable_tableCode Ra1617.cycles } 228974
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1618.table, code := 4505230745648505760448064167333859393,
        encodes := Ra1618.tableCode_eq ▸ encodesTable_tableCode Ra1618.cycles } 228975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1619.table, code := 4505149616010091156216256327133171777,
        encodes := Ra1619.tableCode_eq ▸ encodesTable_tableCode Ra1619.cycles } 228983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1620.table, code := 4505230745648505762898022499914879041,
        encodes := Ra1620.tableCode_eq ▸ encodesTable_tableCode Ra1620.cycles } 228990
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1621.table, code := 4505230745648505762898022502062362689,
        encodes := Ra1621.tableCode_eq ▸ encodesTable_tableCode Ra1621.cycles } 228991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1622.table, code := 4502391210787125800695153272862019649,
        encodes := Ra1622.tableCode_eq ▸ encodesTable_tableCode Ra1622.cycles } 229041
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1623.table, code := 4502472340425540407376919445643726913,
        encodes := Ra1623.tableCode_eq ▸ encodesTable_tableCode Ra1623.cycles } 229048
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1624.table, code := 4502472340425540407376919447791210561,
        encodes := Ra1624.tableCode_eq ▸ encodesTable_tableCode Ra1624.cycles } 229049
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1625.table, code := 4505149618495642638893984371693588545,
        encodes := Ra1625.tableCode_eq ▸ encodesTable_tableCode Ra1625.cycles } 229095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1626.table, code := 4505230748134057245575750544475295809,
        encodes := Ra1626.tableCode_eq ▸ encodesTable_tableCode Ra1626.cycles } 229102
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1627.table, code := 4505230748134057245575750546622779457,
        encodes := Ra1627.tableCode_eq ▸ encodesTable_tableCode Ra1627.cycles } 229103
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1628.table, code := 4505149618495642641343942706422091841,
        encodes := Ra1628.tableCode_eq ▸ encodesTable_tableCode Ra1628.cycles } 229111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1629.table, code := 4505230748134057248025708879203799105,
        encodes := Ra1629.tableCode_eq ▸ encodesTable_tableCode Ra1629.cycles } 229118
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1630.table, code := 4505230748134057248025708881351282753,
        encodes := Ra1630.tableCode_eq ▸ encodesTable_tableCode Ra1630.cycles } 229119
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1631.table, code := 4588550963547812149928039817194770497,
        encodes := Ra1631.tableCode_eq ▸ encodesTable_tableCode Ra1631.cycles } 229223
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1632.table, code := 4588632093186226756609805989976477761,
        encodes := Ra1632.tableCode_eq ▸ encodesTable_tableCode Ra1632.cycles } 229230
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1633.table, code := 4588632093186226756609805992123961409,
        encodes := Ra1633.tableCode_eq ▸ encodesTable_tableCode Ra1633.cycles } 229231
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1634.table, code := 4588550963547812152377998151923273793,
        encodes := Ra1634.tableCode_eq ▸ encodesTable_tableCode Ra1634.cycles } 229239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1635.table, code := 4588632093186226759059764324704981057,
        encodes := Ra1635.tableCode_eq ▸ encodesTable_tableCode Ra1635.cycles } 229246
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1636.table, code := 4588632093186226759059764326852464705,
        encodes := Ra1636.tableCode_eq ▸ encodesTable_tableCode Ra1636.cycles } 229247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1637.table, code := 4588550966033363637505684531212193857,
        encodes := Ra1637.tableCode_eq ▸ encodesTable_tableCode Ra1637.cycles } 229367
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1638.table, code := 4588632095671778244187450703993901121,
        encodes := Ra1638.tableCode_eq ▸ encodesTable_tableCode Ra1638.cycles } 229374
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1639.table, code := 4588632095671778244187450706141384769,
        encodes := Ra1639.tableCode_eq ▸ encodesTable_tableCode Ra1639.cycles } 229375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1640.table, code := 9744582709220031535824341785892884545,
        encodes := Ra1640.tableCode_eq ▸ encodesTable_tableCode Ra1640.cycles } 231295
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1641.table, code := 9744582711705583020952028165181804609,
        encodes := Ra1641.tableCode_eq ▸ encodesTable_tableCode Ra1641.cycles } 231423
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1642.table, code := 9744501579736359588400614437128769601,
        encodes := Ra1642.tableCode_eq ▸ encodesTable_tableCode Ra1642.cycles } 233319
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1643.table, code := 9744582709374774195082380609910476865,
        encodes := Ra1643.tableCode_eq ▸ encodesTable_tableCode Ra1643.cycles } 233326
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1644.table, code := 9744582709374774195082380612057960513,
        encodes := Ra1644.tableCode_eq ▸ encodesTable_tableCode Ra1644.cycles } 233327
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1645.table, code := 9744501579736359590778515104804900929,
        encodes := Ra1645.tableCode_eq ▸ encodesTable_tableCode Ra1645.cycles } 233333
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1646.table, code := 9744501579736359590850572771857272897,
        encodes := Ra1646.tableCode_eq ▸ encodesTable_tableCode Ra1646.cycles } 233335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1647.table, code := 9744582709374774197460281279734091841,
        encodes := Ra1647.tableCode_eq ▸ encodesTable_tableCode Ra1647.cycles } 233341
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1648.table, code := 9744582709374774197532338944638980161,
        encodes := Ra1648.tableCode_eq ▸ encodesTable_tableCode Ra1648.cycles } 233342
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1649.table, code := 9744582709374774197532338946786463809,
        encodes := Ra1649.tableCode_eq ▸ encodesTable_tableCode Ra1649.cycles } 233343
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1650.table, code := 9744501582219493221889069350455087169,
        encodes := Ra1650.tableCode_eq ▸ encodesTable_tableCode Ra1650.cycles } 233443
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1651.table, code := 9744501582221911073528300816417689665,
        encodes := Ra1651.tableCode_eq ▸ encodesTable_tableCode Ra1651.cycles } 233447
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1652.table, code := 9744582711857907828570835525384278081,
        encodes := Ra1652.tableCode_eq ▸ encodesTable_tableCode Ra1652.cycles } 233451
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1653.table, code := 9744582711860325680210066989199396929,
        encodes := Ra1653.tableCode_eq ▸ encodesTable_tableCode Ra1653.cycles } 233454
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1654.table, code := 9744582711860325680210066991346880577,
        encodes := Ra1654.tableCode_eq ▸ encodesTable_tableCode Ra1654.cycles } 233455
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1655.table, code := 9744501582219493224266970018131218497,
        encodes := Ra1655.tableCode_eq ▸ encodesTable_tableCode Ra1655.cycles } 233457
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1656.table, code := 9744501582219493224339027685183590465,
        encodes := Ra1656.tableCode_eq ▸ encodesTable_tableCode Ra1656.cycles } 233459
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1657.table, code := 9744501582221911075906201484093820993,
        encodes := Ra1657.tableCode_eq ▸ encodesTable_tableCode Ra1657.cycles } 233461
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1658.table, code := 9744501582221911075978259151146192961,
        encodes := Ra1658.tableCode_eq ▸ encodesTable_tableCode Ra1658.cycles } 233463
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1659.table, code := 9744582711857907830948736193060409409,
        encodes := Ra1659.tableCode_eq ▸ encodesTable_tableCode Ra1659.cycles } 233465
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1660.table, code := 9744582711857907831020793860112781377,
        encodes := Ra1660.tableCode_eq ▸ encodesTable_tableCode Ra1660.cycles } 233467
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1661.table, code := 9744582711860325682587967659023011905,
        encodes := Ra1661.tableCode_eq ▸ encodesTable_tableCode Ra1661.cycles } 233469
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1662.table, code := 9744582711860325682660025323927900225,
        encodes := Ra1662.tableCode_eq ▸ encodesTable_tableCode Ra1662.cycles } 233470
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1663.table, code := 9744582711860325682660025326075383873,
        encodes := Ra1663.tableCode_eq ▸ encodesTable_tableCode Ra1663.cycles } 233471
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1664.table, code := 9749775006078571104266099225576869953,
        encodes := Ra1664.tableCode_eq ▸ encodesTable_tableCode Ra1664.cycles } 235391
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1600 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1600 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1600 + i.val) 0 ≤ Data.profiles (1600 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1600 + i.val) 0 = Data.canonicalMask (1600 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1600 + i.val) < Data.canonicalMask (1600 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1600 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models025
