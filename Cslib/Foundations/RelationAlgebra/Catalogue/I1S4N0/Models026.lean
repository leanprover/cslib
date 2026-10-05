/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1665
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1666
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1667
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1668
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1669
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1670
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1671
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1672
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1673
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1674
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1675
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1676
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1677
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1678
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1679
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1680
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1681
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1682
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1683
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1684
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1685
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1686
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1687
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1688
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1689
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1690
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1691
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1692
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1693
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1694
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1695
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1696
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1697
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1698
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1699
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1700
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1701
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1702
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1703
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1704
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1705
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1706
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1707
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1708
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1709
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1710
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1711
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1712
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1713
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1714
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1715
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1716
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1717
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1718
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1719
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1720
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1721
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1722
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1723
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1724
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1725
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1726
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1727
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1728

/-!
# Certified models 1665–1728 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models026

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1665.table, code := 9749775008564122589393785604865790017,
        encodes := Ra1665.tableCode_eq ▸ encodesTable_tableCode Ra1665.cycles } 235519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1666.table, code := 9749693876594899152230685858385367105,
        encodes := Ra1666.tableCode_eq ▸ encodesTable_tableCode Ra1666.cycles } 236391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1667.table, code := 9749775006233313758912452033314558017,
        encodes := Ra1667.tableCode_eq ▸ encodesTable_tableCode Ra1667.cycles } 236399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1668.table, code := 9749693876594899154608586526061498433,
        encodes := Ra1668.tableCode_eq ▸ encodesTable_tableCode Ra1668.cycles } 236405
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1669.table, code := 9749693876594899154680644193113870401,
        encodes := Ra1669.tableCode_eq ▸ encodesTable_tableCode Ra1669.cycles } 236407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1670.table, code := 9749775006233313761290352700990689345,
        encodes := Ra1670.tableCode_eq ▸ encodesTable_tableCode Ra1670.cycles } 236413
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1671.table, code := 9749775006233313761362410365895577665,
        encodes := Ra1671.tableCode_eq ▸ encodesTable_tableCode Ra1671.cycles } 236414
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1672.table, code := 9749775006233313761362410368043061313,
        encodes := Ra1672.tableCode_eq ▸ encodesTable_tableCode Ra1672.cycles } 236415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1673.table, code := 9749693879078032785719140771711684673,
        encodes := Ra1673.tableCode_eq ▸ encodesTable_tableCode Ra1673.cycles } 236515
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1674.table, code := 9749693879080450637358372237674287169,
        encodes := Ra1674.tableCode_eq ▸ encodesTable_tableCode Ra1674.cycles } 236519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1675.table, code := 9749775008716447392400906946640875585,
        encodes := Ra1675.tableCode_eq ▸ encodesTable_tableCode Ra1675.cycles } 236523
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1676.table, code := 9749775008718865244040138412603478081,
        encodes := Ra1676.tableCode_eq ▸ encodesTable_tableCode Ra1676.cycles } 236527
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1677.table, code := 9749693879078032788097041439387816001,
        encodes := Ra1677.tableCode_eq ▸ encodesTable_tableCode Ra1677.cycles } 236529
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1678.table, code := 9749693879078032788169099106440187969,
        encodes := Ra1678.tableCode_eq ▸ encodesTable_tableCode Ra1678.cycles } 236531
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1679.table, code := 9749693879080450639736272905350418497,
        encodes := Ra1679.tableCode_eq ▸ encodesTable_tableCode Ra1679.cycles } 236533
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1680.table, code := 9749693879080450639808330572402790465,
        encodes := Ra1680.tableCode_eq ▸ encodesTable_tableCode Ra1680.cycles } 236535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1681.table, code := 9749775008716447394778807614317006913,
        encodes := Ra1681.tableCode_eq ▸ encodesTable_tableCode Ra1681.cycles } 236537
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1682.table, code := 9749775008716447394850865281369378881,
        encodes := Ra1682.tableCode_eq ▸ encodesTable_tableCode Ra1682.cycles } 236539
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1683.table, code := 9749775008718865246418039080279609409,
        encodes := Ra1683.tableCode_eq ▸ encodesTable_tableCode Ra1683.cycles } 236541
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1684.table, code := 9749775008718865246490096745184497729,
        encodes := Ra1684.tableCode_eq ▸ encodesTable_tableCode Ra1684.cycles } 236542
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1685.table, code := 9749775008718865246490096747331981377,
        encodes := Ra1685.tableCode_eq ▸ encodesTable_tableCode Ra1685.cycles } 236543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1686.table, code := 9749693876594899156842371876812755009,
        encodes := Ra1686.tableCode_eq ▸ encodesTable_tableCode Ra1686.cycles } 237415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1687.table, code := 9749775006233313763524138049594462273,
        encodes := Ra1687.tableCode_eq ▸ encodesTable_tableCode Ra1687.cycles } 237422
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1688.table, code := 9749775006233313763524138051741945921,
        encodes := Ra1688.tableCode_eq ▸ encodesTable_tableCode Ra1688.cycles } 237423
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1689.table, code := 9749693876594899159220272544488886337,
        encodes := Ra1689.tableCode_eq ▸ encodesTable_tableCode Ra1689.cycles } 237429
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1690.table, code := 9749693876594899159292330211541258305,
        encodes := Ra1690.tableCode_eq ▸ encodesTable_tableCode Ra1690.cycles } 237431
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1691.table, code := 9749775006233313765902038719418077249,
        encodes := Ra1691.tableCode_eq ▸ encodesTable_tableCode Ra1691.cycles } 237437
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1692.table, code := 9749775006233313765974096384322965569,
        encodes := Ra1692.tableCode_eq ▸ encodesTable_tableCode Ra1692.cycles } 237438
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1693.table, code := 9749775006233313765974096386470449217,
        encodes := Ra1693.tableCode_eq ▸ encodesTable_tableCode Ra1693.cycles } 237439
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1694.table, code := 9749693879078032790330826790139072577,
        encodes := Ra1694.tableCode_eq ▸ encodesTable_tableCode Ra1694.cycles } 237539
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1695.table, code := 9749693879080450641970058256101675073,
        encodes := Ra1695.tableCode_eq ▸ encodesTable_tableCode Ra1695.cycles } 237543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1696.table, code := 9749775008716447397012592965068263489,
        encodes := Ra1696.tableCode_eq ▸ encodesTable_tableCode Ra1696.cycles } 237547
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1697.table, code := 9749775008718865248651824428883382337,
        encodes := Ra1697.tableCode_eq ▸ encodesTable_tableCode Ra1697.cycles } 237550
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1698.table, code := 9749775008718865248651824431030865985,
        encodes := Ra1698.tableCode_eq ▸ encodesTable_tableCode Ra1698.cycles } 237551
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1699.table, code := 9749693879078032792708727457815203905,
        encodes := Ra1699.tableCode_eq ▸ encodesTable_tableCode Ra1699.cycles } 237553
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1700.table, code := 9749693879078032792780785124867575873,
        encodes := Ra1700.tableCode_eq ▸ encodesTable_tableCode Ra1700.cycles } 237555
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1701.table, code := 9749693879080450644347958923777806401,
        encodes := Ra1701.tableCode_eq ▸ encodesTable_tableCode Ra1701.cycles } 237557
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1702.table, code := 9749693879080450644420016590830178369,
        encodes := Ra1702.tableCode_eq ▸ encodesTable_tableCode Ra1702.cycles } 237559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1703.table, code := 9749775008716447399390493632744394817,
        encodes := Ra1703.tableCode_eq ▸ encodesTable_tableCode Ra1703.cycles } 237561
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1704.table, code := 9749775008716447399462551299796766785,
        encodes := Ra1704.tableCode_eq ▸ encodesTable_tableCode Ra1704.cycles } 237563
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1705.table, code := 9749775008718865251029725098706997313,
        encodes := Ra1705.tableCode_eq ▸ encodesTable_tableCode Ra1705.cycles } 237565
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1706.table, code := 9749775008718865251101782763611885633,
        encodes := Ra1706.tableCode_eq ▸ encodesTable_tableCode Ra1706.cycles } 237566
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1707.table, code := 9749775008718865251101782765759369281,
        encodes := Ra1707.tableCode_eq ▸ encodesTable_tableCode Ra1707.cycles } 237567
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1708.table, code := 9658341831999969007383595284106055745,
        encodes := Ra1708.tableCode_eq ▸ encodesTable_tableCode Ra1708.cycles } 239235
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1709.table, code := 9658422961638383614065361456887763009,
        encodes := Ra1709.tableCode_eq ▸ encodesTable_tableCode Ra1709.cycles } 239242
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1710.table, code := 9658422961638383614065361459035246657,
        encodes := Ra1710.tableCode_eq ▸ encodesTable_tableCode Ra1710.cycles } 239243
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1711.table, code := 9658341831999969009833553618834559041,
        encodes := Ra1711.tableCode_eq ▸ encodesTable_tableCode Ra1711.cycles } 239251
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1712.table, code := 9661100239706067996321095584651153473,
        encodes := Ra1712.tableCode_eq ▸ encodesTable_tableCode Ra1712.cycles } 239299
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1713.table, code := 9661181369344482603002861757432860737,
        encodes := Ra1713.tableCode_eq ▸ encodesTable_tableCode Ra1713.cycles } 239306
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1714.table, code := 9661181369344482603002861759580344385,
        encodes := Ra1714.tableCode_eq ▸ encodesTable_tableCode Ra1714.cycles } 239307
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1715.table, code := 9661100239706067998771053919379656769,
        encodes := Ra1715.tableCode_eq ▸ encodesTable_tableCode Ra1715.cycles } 239315
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1716.table, code := 9661181369344482605380762427256475713,
        encodes := Ra1716.tableCode_eq ▸ encodesTable_tableCode Ra1716.cycles } 239321
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1717.table, code := 9661181369344482605452820092161364033,
        encodes := Ra1717.tableCode_eq ▸ encodesTable_tableCode Ra1717.cycles } 239322
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1718.table, code := 9661181369344482605452820094308847681,
        encodes := Ra1718.tableCode_eq ▸ encodesTable_tableCode Ra1718.cycles } 239323
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1719.table, code := 9741743177054556370056882195569840193,
        encodes := Ra1719.tableCode_eq ▸ encodesTable_tableCode Ra1719.cycles } 239367
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1720.table, code := 9741824306692970976738648368351547457,
        encodes := Ra1720.tableCode_eq ▸ encodesTable_tableCode Ra1720.cycles } 239374
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1721.table, code := 9741824306692970976738648370499031105,
        encodes := Ra1721.tableCode_eq ▸ encodesTable_tableCode Ra1721.cycles } 239375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1722.table, code := 9744501584842862391181289291585425473,
        encodes := Ra1722.tableCode_eq ▸ encodesTable_tableCode Ra1722.cycles } 239477
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1723.table, code := 9744501584842862391253346958637797441,
        encodes := Ra1723.tableCode_eq ▸ encodesTable_tableCode Ra1723.cycles } 239479
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1724.table, code := 9744582714481276997863055464367132737,
        encodes := Ra1724.tableCode_eq ▸ encodesTable_tableCode Ra1724.cycles } 239484
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1725.table, code := 9744582714481276997863055466514616385,
        encodes := Ra1725.tableCode_eq ▸ encodesTable_tableCode Ra1725.cycles } 239485
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1726.table, code := 9744582714481276997935113131419504705,
        encodes := Ra1726.tableCode_eq ▸ encodesTable_tableCode Ra1726.cycles } 239486
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1727.table, code := 9744582714481276997935113133566988353,
        encodes := Ra1727.tableCode_eq ▸ encodesTable_tableCode Ra1727.cycles } 239487
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1728.table, code := 9741743179540107855184568574858760257,
        encodes := Ra1728.tableCode_eq ▸ encodesTable_tableCode Ra1728.cycles } 239495
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1664 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1664 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1664 + i.val) 0 ≤ Data.profiles (1664 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1664 + i.val) 0 = Data.canonicalMask (1664 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1664 + i.val) < Data.canonicalMask (1664 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1664 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models026
