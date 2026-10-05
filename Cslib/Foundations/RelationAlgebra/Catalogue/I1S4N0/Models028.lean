/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1793
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1794
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1795
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1796
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1797
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1798
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1799
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1800
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1801
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1802
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1803
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1804
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1805
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1806
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1807
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1808
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1809
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1810
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1811
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1812
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1813
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1814
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1815
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1816
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1817
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1818
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1819
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1820
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1821
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1822
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1823
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1824
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1825
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1826
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1827
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1828
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1829
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1830
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1831
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1832
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1833
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1834
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1835
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1836
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1837
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1838
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1839
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1840
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1841
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1842
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1843
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1844
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1845
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1846
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1847
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1848
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1849
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1850
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1851
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1852
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1853
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1854
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1855
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1856

/-!
# Certified models 1793–1856 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models028

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1793.table, code := 9749775013822950199793267819524919361,
        encodes := Ra1793.tableCode_eq ▸ encodesTable_tableCode Ra1793.cycles } 243705
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1794.table, code := 9749775013822950199865325486577291329,
        encodes := Ra1794.tableCode_eq ▸ encodesTable_tableCode Ra1794.cycles } 243707
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1795.table, code := 9749775013825368051432499283340038209,
        encodes := Ra1795.tableCode_eq ▸ encodesTable_tableCode Ra1795.cycles } 243708
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1796.table, code := 9749775013825368051432499285487521857,
        encodes := Ra1796.tableCode_eq ▸ encodesTable_tableCode Ra1796.cycles } 243709
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1797.table, code := 9749775013825368051504556950392410177,
        encodes := Ra1797.tableCode_eq ▸ encodesTable_tableCode Ra1797.cycles } 243710
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1798.table, code := 9749775013825368051504556952539893825,
        encodes := Ra1798.tableCode_eq ▸ encodesTable_tableCode Ra1798.cycles } 243711
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1799.table, code := 9749693881856144614341457206059470913,
        encodes := Ra1799.tableCode_eq ▸ encodesTable_tableCode Ra1799.cycles } 244583
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1800.table, code := 9749775011494559221023223380988661825,
        encodes := Ra1800.tableCode_eq ▸ encodesTable_tableCode Ra1800.cycles } 244591
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1801.table, code := 9749693881856144616719357873735602241,
        encodes := Ra1801.tableCode_eq ▸ encodesTable_tableCode Ra1801.cycles } 244597
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1802.table, code := 9749693881856144616791415540787974209,
        encodes := Ra1802.tableCode_eq ▸ encodesTable_tableCode Ra1802.cycles } 244599
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1803.table, code := 9749775011494559223401124048664793153,
        encodes := Ra1803.tableCode_eq ▸ encodesTable_tableCode Ra1803.cycles } 244605
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1804.table, code := 9749775011494559223473181713569681473,
        encodes := Ra1804.tableCode_eq ▸ encodesTable_tableCode Ra1804.cycles } 244606
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1805.table, code := 9749775011494559223473181715717165121,
        encodes := Ra1805.tableCode_eq ▸ encodesTable_tableCode Ra1805.cycles } 244607
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1806.table, code := 9749693884259489072110095792282538049,
        encodes := Ra1806.tableCode_eq ▸ encodesTable_tableCode Ra1806.cycles } 244695
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1807.table, code := 9749775013897903678791861965064245313,
        encodes := Ra1807.tableCode_eq ▸ encodesTable_tableCode Ra1807.cycles } 244702
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1808.table, code := 9749775013897903678791861967211728961,
        encodes := Ra1808.tableCode_eq ▸ encodesTable_tableCode Ra1808.cycles } 244703
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1809.table, code := 9749693884339278247829912119385788481,
        encodes := Ra1809.tableCode_eq ▸ encodesTable_tableCode Ra1809.cycles } 244707
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1810.table, code := 9749693884341696099469143585348390977,
        encodes := Ra1810.tableCode_eq ▸ encodesTable_tableCode Ra1810.cycles } 244711
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1811.table, code := 9749775013977692854511678294314979393,
        encodes := Ra1811.tableCode_eq ▸ encodesTable_tableCode Ra1811.cycles } 244715
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1812.table, code := 9749775013980110706150909760277581889,
        encodes := Ra1812.tableCode_eq ▸ encodesTable_tableCode Ra1812.cycles } 244719
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1813.table, code := 9749693884339278250207812787061919809,
        encodes := Ra1813.tableCode_eq ▸ encodesTable_tableCode Ra1813.cycles } 244721
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1814.table, code := 9749693884339278250279870454114291777,
        encodes := Ra1814.tableCode_eq ▸ encodesTable_tableCode Ra1814.cycles } 244723
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1815.table, code := 9749693884341696101847044253024522305,
        encodes := Ra1815.tableCode_eq ▸ encodesTable_tableCode Ra1815.cycles } 244725
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1816.table, code := 9749693884341696101919101920076894273,
        encodes := Ra1816.tableCode_eq ▸ encodesTable_tableCode Ra1816.cycles } 244727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1817.table, code := 9749775013977692856889578961991110721,
        encodes := Ra1817.tableCode_eq ▸ encodesTable_tableCode Ra1817.cycles } 244729
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1818.table, code := 9749775013977692856961636629043482689,
        encodes := Ra1818.tableCode_eq ▸ encodesTable_tableCode Ra1818.cycles } 244731
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1819.table, code := 9749775013980110708528810427953713217,
        encodes := Ra1819.tableCode_eq ▸ encodesTable_tableCode Ra1819.cycles } 244733
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1820.table, code := 9749775013980110708600868092858601537,
        encodes := Ra1820.tableCode_eq ▸ encodesTable_tableCode Ra1820.cycles } 244734
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1821.table, code := 9749775013980110708600868095006085185,
        encodes := Ra1821.tableCode_eq ▸ encodesTable_tableCode Ra1821.cycles } 244735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1822.table, code := 9749693881856144618953143224486858817,
        encodes := Ra1822.tableCode_eq ▸ encodesTable_tableCode Ra1822.cycles } 245607
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1823.table, code := 9749775011494559225634909397268566081,
        encodes := Ra1823.tableCode_eq ▸ encodesTable_tableCode Ra1823.cycles } 245614
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1824.table, code := 9749775011494559225634909399416049729,
        encodes := Ra1824.tableCode_eq ▸ encodesTable_tableCode Ra1824.cycles } 245615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1825.table, code := 9749693881856144621331043892162990145,
        encodes := Ra1825.tableCode_eq ▸ encodesTable_tableCode Ra1825.cycles } 245621
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1826.table, code := 9749693881856144621403101559215362113,
        encodes := Ra1826.tableCode_eq ▸ encodesTable_tableCode Ra1826.cycles } 245623
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1827.table, code := 9749775011494559228012810064944697409,
        encodes := Ra1827.tableCode_eq ▸ encodesTable_tableCode Ra1827.cycles } 245628
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1828.table, code := 9749775011494559228012810067092181057,
        encodes := Ra1828.tableCode_eq ▸ encodesTable_tableCode Ra1828.cycles } 245629
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1829.table, code := 9749775011494559228084867731997069377,
        encodes := Ra1829.tableCode_eq ▸ encodesTable_tableCode Ra1829.cycles } 245630
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1830.table, code := 9749775011494559228084867734144553025,
        encodes := Ra1830.tableCode_eq ▸ encodesTable_tableCode Ra1830.cycles } 245631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1831.table, code := 9749693884259489076721781810709925953,
        encodes := Ra1831.tableCode_eq ▸ encodesTable_tableCode Ra1831.cycles } 245719
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1832.table, code := 9749775013897903683403547983491633217,
        encodes := Ra1832.tableCode_eq ▸ encodesTable_tableCode Ra1832.cycles } 245726
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1833.table, code := 9749775013897903683403547985639116865,
        encodes := Ra1833.tableCode_eq ▸ encodesTable_tableCode Ra1833.cycles } 245727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1834.table, code := 9749693884339278252441598137813176385,
        encodes := Ra1834.tableCode_eq ▸ encodesTable_tableCode Ra1834.cycles } 245731
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1835.table, code := 9749693884341696104080829603775778881,
        encodes := Ra1835.tableCode_eq ▸ encodesTable_tableCode Ra1835.cycles } 245735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1836.table, code := 9749775013977692859123364312742367297,
        encodes := Ra1836.tableCode_eq ▸ encodesTable_tableCode Ra1836.cycles } 245739
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1837.table, code := 9749775013980110710762595776557486145,
        encodes := Ra1837.tableCode_eq ▸ encodesTable_tableCode Ra1837.cycles } 245742
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1838.table, code := 9749775013980110710762595778704969793,
        encodes := Ra1838.tableCode_eq ▸ encodesTable_tableCode Ra1838.cycles } 245743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1839.table, code := 9749693884339278254819498805489307713,
        encodes := Ra1839.tableCode_eq ▸ encodesTable_tableCode Ra1839.cycles } 245745
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1840.table, code := 9749693884339278254891556472541679681,
        encodes := Ra1840.tableCode_eq ▸ encodesTable_tableCode Ra1840.cycles } 245747
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1841.table, code := 9749693884341696106458730271451910209,
        encodes := Ra1841.tableCode_eq ▸ encodesTable_tableCode Ra1841.cycles } 245749
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1842.table, code := 9749693884341696106530787938504282177,
        encodes := Ra1842.tableCode_eq ▸ encodesTable_tableCode Ra1842.cycles } 245751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1843.table, code := 9749775013977692861501264980418498625,
        encodes := Ra1843.tableCode_eq ▸ encodesTable_tableCode Ra1843.cycles } 245753
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1844.table, code := 9749775013977692861573322647470870593,
        encodes := Ra1844.tableCode_eq ▸ encodesTable_tableCode Ra1844.cycles } 245755
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1845.table, code := 9749775013980110713140496444233617473,
        encodes := Ra1845.tableCode_eq ▸ encodesTable_tableCode Ra1845.cycles } 245756
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1846.table, code := 9749775013980110713140496446381101121,
        encodes := Ra1846.tableCode_eq ▸ encodesTable_tableCode Ra1846.cycles } 245757
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1847.table, code := 9749775013980110713212554111285989441,
        encodes := Ra1847.tableCode_eq ▸ encodesTable_tableCode Ra1847.cycles } 245758
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1848.table, code := 9749775013980110713212554113433473089,
        encodes := Ra1848.tableCode_eq ▸ encodesTable_tableCode Ra1848.cycles } 245759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1849.table, code := 9918362553777003917817788317112209473,
        encodes := Ra1849.tableCode_eq ▸ encodesTable_tableCode Ra1849.cycles } 247611
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1850.table, code := 9918362553779421769457019780927328321,
        encodes := Ra1850.tableCode_eq ▸ encodesTable_tableCode Ra1850.cycles } 247614
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1851.table, code := 9918362553779421769457019783074811969,
        encodes := Ra1851.tableCode_eq ▸ encodesTable_tableCode Ra1851.cycles } 247615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1852.table, code := 9921039831844688297623564107999612993,
        encodes := Ra1852.tableCode_eq ▸ encodesTable_tableCode Ra1852.cycles } 247651
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1853.table, code := 9921039831847106149262795573962215489,
        encodes := Ra1853.tableCode_eq ▸ encodesTable_tableCode Ra1853.cycles } 247655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1854.table, code := 9921120961483102904305330282928803905,
        encodes := Ra1854.tableCode_eq ▸ encodesTable_tableCode Ra1854.cycles } 247659
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1855.table, code := 9921120961485520755944561746743922753,
        encodes := Ra1855.tableCode_eq ▸ encodesTable_tableCode Ra1855.cycles } 247662
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1856.table, code := 9921120961485520755944561748891406401,
        encodes := Ra1856.tableCode_eq ▸ encodesTable_tableCode Ra1856.cycles } 247663
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1792 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1792 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1792 + i.val) 0 ≤ Data.profiles (1792 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1792 + i.val) 0 = Data.canonicalMask (1792 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1792 + i.val) < Data.canonicalMask (1792 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1792 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models028
