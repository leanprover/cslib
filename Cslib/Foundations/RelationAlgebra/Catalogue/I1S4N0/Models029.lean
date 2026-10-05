/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1857
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1858
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1859
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1860
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1861
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1862
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1863
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1864
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1865
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1866
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1867
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1868
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1869
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1870
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1871
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1872
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1873
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1874
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1875
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1876
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1877
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1878
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1879
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1880
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1881
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1882
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1883
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1884
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1885
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1886
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1887
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1888
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1889
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1890
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1891
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1892
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1893
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1894
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1895
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1896
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1897
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1898
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1899
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1900
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1901
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1902
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1903
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1904
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1905
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1906
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1907
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1908
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1909
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1910
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1911
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1912
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1913
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1914
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1915
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1916
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1917
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1918
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1919
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1920

/-!
# Certified models 1857–1920 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models029

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1857.table, code := 9921039831844688300073522442728116289,
        encodes := Ra1857.tableCode_eq ▸ encodesTable_tableCode Ra1857.cycles } 247667
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1858.table, code := 9921039831847106151640696241638346817,
        encodes := Ra1858.tableCode_eq ▸ encodesTable_tableCode Ra1858.cycles } 247669
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1859.table, code := 9921039831847106151712753908690718785,
        encodes := Ra1859.tableCode_eq ▸ encodesTable_tableCode Ra1859.cycles } 247671
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1860.table, code := 9921120961483102906683230950604935233,
        encodes := Ra1860.tableCode_eq ▸ encodesTable_tableCode Ra1860.cycles } 247673
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1861.table, code := 9921120961483102906755288617657307201,
        encodes := Ra1861.tableCode_eq ▸ encodesTable_tableCode Ra1861.cycles } 247675
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1862.table, code := 9921120961485520758322462414420054081,
        encodes := Ra1862.tableCode_eq ▸ encodesTable_tableCode Ra1862.cycles } 247676
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1863.table, code := 9921120961485520758322462416567537729,
        encodes := Ra1863.tableCode_eq ▸ encodesTable_tableCode Ra1863.cycles } 247677
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1864.table, code := 9921120961485520758394520081472426049,
        encodes := Ra1864.tableCode_eq ▸ encodesTable_tableCode Ra1864.cycles } 247678
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1865.table, code := 9921120961485520758394520083619909697,
        encodes := Ra1865.tableCode_eq ▸ encodesTable_tableCode Ra1865.cycles } 247679
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1866.table, code := 9918362556262555402945474694253645889,
        encodes := Ra1866.tableCode_eq ▸ encodesTable_tableCode Ra1866.cycles } 247738
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1867.table, code := 9918362556262555402945474696401129537,
        encodes := Ra1867.tableCode_eq ▸ encodesTable_tableCode Ra1867.cycles } 247739
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1868.table, code := 9918362556264973254584706160216248385,
        encodes := Ra1868.tableCode_eq ▸ encodesTable_tableCode Ra1868.cycles } 247742
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1869.table, code := 9918362556264973254584706162363732033,
        encodes := Ra1869.tableCode_eq ▸ encodesTable_tableCode Ra1869.cycles } 247743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1870.table, code := 9921039834330239782751250487288533057,
        encodes := Ra1870.tableCode_eq ▸ encodesTable_tableCode Ra1870.cycles } 247779
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1871.table, code := 9921039834332657634390481953251135553,
        encodes := Ra1871.tableCode_eq ▸ encodesTable_tableCode Ra1871.cycles } 247783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1872.table, code := 9921120963968654389433016660070240321,
        encodes := Ra1872.tableCode_eq ▸ encodesTable_tableCode Ra1872.cycles } 247786
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1873.table, code := 9921120963968654389433016662217723969,
        encodes := Ra1873.tableCode_eq ▸ encodesTable_tableCode Ra1873.cycles } 247787
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1874.table, code := 9921120963971072241072248126032842817,
        encodes := Ra1874.tableCode_eq ▸ encodesTable_tableCode Ra1874.cycles } 247790
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1875.table, code := 9921120963971072241072248128180326465,
        encodes := Ra1875.tableCode_eq ▸ encodesTable_tableCode Ra1875.cycles } 247791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1876.table, code := 9921039834330239785129151154964664385,
        encodes := Ra1876.tableCode_eq ▸ encodesTable_tableCode Ra1876.cycles } 247793
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1877.table, code := 9921039834330239785201208822017036353,
        encodes := Ra1877.tableCode_eq ▸ encodesTable_tableCode Ra1877.cycles } 247795
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1878.table, code := 9921039834332657636768382620927266881,
        encodes := Ra1878.tableCode_eq ▸ encodesTable_tableCode Ra1878.cycles } 247797
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1879.table, code := 9921039834332657636840440287979638849,
        encodes := Ra1879.tableCode_eq ▸ encodesTable_tableCode Ra1879.cycles } 247799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1880.table, code := 9921120963968654391810917329893855297,
        encodes := Ra1880.tableCode_eq ▸ encodesTable_tableCode Ra1880.cycles } 247801
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1881.table, code := 9921120963968654391882974994798743617,
        encodes := Ra1881.tableCode_eq ▸ encodesTable_tableCode Ra1881.cycles } 247802
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1882.table, code := 9921120963968654391882974996946227265,
        encodes := Ra1882.tableCode_eq ▸ encodesTable_tableCode Ra1882.cycles } 247803
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1883.table, code := 9921120963971072243450148793708974145,
        encodes := Ra1883.tableCode_eq ▸ encodesTable_tableCode Ra1883.cycles } 247804
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1884.table, code := 9921120963971072243450148795856457793,
        encodes := Ra1884.tableCode_eq ▸ encodesTable_tableCode Ra1884.cycles } 247805
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1885.table, code := 9921120963971072243522206460761346113,
        encodes := Ra1885.tableCode_eq ▸ encodesTable_tableCode Ra1885.cycles } 247806
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1886.table, code := 9921120963971072243522206462908829761,
        encodes := Ra1886.tableCode_eq ▸ encodesTable_tableCode Ra1886.cycles } 247807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1887.table, code := 9918281424295749822033292434310697025,
        encodes := Ra1887.tableCode_eq ▸ encodesTable_tableCode Ra1887.cycles } 249639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1888.table, code := 9918362553934164428715058607092404289,
        encodes := Ra1888.tableCode_eq ▸ encodesTable_tableCode Ra1888.cycles } 249646
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1889.table, code := 9918362553934164428715058609239887937,
        encodes := Ra1889.tableCode_eq ▸ encodesTable_tableCode Ra1889.cycles } 249647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1890.table, code := 9918281424295749824483250769039200321,
        encodes := Ra1890.tableCode_eq ▸ encodesTable_tableCode Ra1890.cycles } 249655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1891.table, code := 9918362553931746579453727810953416769,
        encodes := Ra1891.tableCode_eq ▸ encodesTable_tableCode Ra1891.cycles } 249657
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1892.table, code := 9918362553931746579525785478005788737,
        encodes := Ra1892.tableCode_eq ▸ encodesTable_tableCode Ra1892.cycles } 249659
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1893.table, code := 9918362553934164431092959276916019265,
        encodes := Ra1893.tableCode_eq ▸ encodesTable_tableCode Ra1893.cycles } 249661
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1894.table, code := 9918362553934164431165016941820907585,
        encodes := Ra1894.tableCode_eq ▸ encodesTable_tableCode Ra1894.cycles } 249662
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1895.table, code := 9918362553934164431165016943968391233,
        encodes := Ra1895.tableCode_eq ▸ encodesTable_tableCode Ra1895.cycles } 249663
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1896.table, code := 9921039831919641783611744941789941825,
        encodes := Ra1896.tableCode_eq ▸ encodesTable_tableCode Ra1896.cycles } 249687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1897.table, code := 9921120961558056390221453449666760769,
        encodes := Ra1897.tableCode_eq ▸ encodesTable_tableCode Ra1897.cycles } 249693
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1898.table, code := 9921120961558056390293511114571649089,
        encodes := Ra1898.tableCode_eq ▸ encodesTable_tableCode Ra1898.cycles } 249694
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1899.table, code := 9921120961558056390293511116719132737,
        encodes := Ra1899.tableCode_eq ▸ encodesTable_tableCode Ra1899.cycles } 249695
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1900.table, code := 9921039832001848810970792734855794753,
        encodes := Ra1900.tableCode_eq ▸ encodesTable_tableCode Ra1900.cycles } 249703
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1901.table, code := 9921120961637845566013327443822383169,
        encodes := Ra1901.tableCode_eq ▸ encodesTable_tableCode Ra1901.cycles } 249707
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1902.table, code := 9921120961640263417652558907637502017,
        encodes := Ra1902.tableCode_eq ▸ encodesTable_tableCode Ra1902.cycles } 249710
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1903.table, code := 9921120961640263417652558909784985665,
        encodes := Ra1903.tableCode_eq ▸ encodesTable_tableCode Ra1903.cycles } 249711
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1904.table, code := 9921039832001848813420751069584298049,
        encodes := Ra1904.tableCode_eq ▸ encodesTable_tableCode Ra1904.cycles } 249719
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1905.table, code := 9921120961637845568391228111498514497,
        encodes := Ra1905.tableCode_eq ▸ encodesTable_tableCode Ra1905.cycles } 249721
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1906.table, code := 9921120961637845568463285778550886465,
        encodes := Ra1906.tableCode_eq ▸ encodesTable_tableCode Ra1906.cycles } 249723
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1907.table, code := 9921120961640263420030459575313633345,
        encodes := Ra1907.tableCode_eq ▸ encodesTable_tableCode Ra1907.cycles } 249724
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1908.table, code := 9921120961640263420030459577461116993,
        encodes := Ra1908.tableCode_eq ▸ encodesTable_tableCode Ra1908.cycles } 249725
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1909.table, code := 9921120961640263420102517242366005313,
        encodes := Ra1909.tableCode_eq ▸ encodesTable_tableCode Ra1909.cycles } 249726
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1910.table, code := 9921120961640263420102517244513488961,
        encodes := Ra1910.tableCode_eq ▸ encodesTable_tableCode Ra1910.cycles } 249727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1911.table, code := 9918281426781301307160978813599617089,
        encodes := Ra1911.tableCode_eq ▸ encodesTable_tableCode Ra1911.cycles } 249767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1912.table, code := 9918362556417298062203513520418721857,
        encodes := Ra1912.tableCode_eq ▸ encodesTable_tableCode Ra1912.cycles } 249770
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1913.table, code := 9918362556417298062203513522566205505,
        encodes := Ra1913.tableCode_eq ▸ encodesTable_tableCode Ra1913.cycles } 249771
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1914.table, code := 9918362556419715913842744986381324353,
        encodes := Ra1914.tableCode_eq ▸ encodesTable_tableCode Ra1914.cycles } 249774
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1915.table, code := 9918362556419715913842744988528808001,
        encodes := Ra1915.tableCode_eq ▸ encodesTable_tableCode Ra1915.cycles } 249775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1916.table, code := 9918281426781301309538879481275748417,
        encodes := Ra1916.tableCode_eq ▸ encodesTable_tableCode Ra1916.cycles } 249781
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1917.table, code := 9918281426781301309610937148328120385,
        encodes := Ra1917.tableCode_eq ▸ encodesTable_tableCode Ra1917.cycles } 249783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1918.table, code := 9918362556417298064581414190242336833,
        encodes := Ra1918.tableCode_eq ▸ encodesTable_tableCode Ra1918.cycles } 249785
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1919.table, code := 9918362556417298064653471855147225153,
        encodes := Ra1919.tableCode_eq ▸ encodesTable_tableCode Ra1919.cycles } 249786
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1920.table, code := 9918362556417298064653471857294708801,
        encodes := Ra1920.tableCode_eq ▸ encodesTable_tableCode Ra1920.cycles } 249787
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1856 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1856 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1856 + i.val) 0 ≤ Data.profiles (1856 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1856 + i.val) 0 = Data.canonicalMask (1856 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1856 + i.val) < Data.canonicalMask (1856 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1856 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models029
