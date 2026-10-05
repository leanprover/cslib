/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1921
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1922
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1923
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1924
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1925
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1926
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1927
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1928
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1929
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1930
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1931
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1932
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1933
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1934
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1935
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1936
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1937
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1938
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1939
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1940
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1941
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1942
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1943
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1944
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1945
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1946
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1947
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1948
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1949
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1950
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1951
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1952
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1953
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1954
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1955
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1956
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1957
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1958
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1959
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1960
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1961
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1962
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1963
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1964
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1965
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1966
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1967
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1968
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1969
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1970
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1971
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1972
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1973
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1974
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1975
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1976
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1977
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1978
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1979
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1980
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1981
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1982
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1983
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1984

/-!
# Certified models 1921–1984 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models030

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1921.table, code := 9918362556419715916220645656204939329,
        encodes := Ra1921.tableCode_eq ▸ encodesTable_tableCode Ra1921.cycles } 249789
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1922.table, code := 9918362556419715916292703321109827649,
        encodes := Ra1922.tableCode_eq ▸ encodesTable_tableCode Ra1922.cycles } 249790
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1923.table, code := 9918362556419715916292703323257311297,
        encodes := Ra1923.tableCode_eq ▸ encodesTable_tableCode Ra1923.cycles } 249791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1924.table, code := 9921039834405193266289472986350358593,
        encodes := Ra1924.tableCode_eq ▸ encodesTable_tableCode Ra1924.cycles } 249799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1925.table, code := 9921120964043607872971239159132065857,
        encodes := Ra1925.tableCode_eq ▸ encodesTable_tableCode Ra1925.cycles } 249806
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1926.table, code := 9921120964043607872971239161279549505,
        encodes := Ra1926.tableCode_eq ▸ encodesTable_tableCode Ra1926.cycles } 249807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1927.table, code := 9921039834405193268739431321078861889,
        encodes := Ra1927.tableCode_eq ▸ encodesTable_tableCode Ra1927.cycles } 249815
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1928.table, code := 9921120964043607875349139828955680833,
        encodes := Ra1928.tableCode_eq ▸ encodesTable_tableCode Ra1928.cycles } 249821
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1929.table, code := 9921120964043607875421197493860569153,
        encodes := Ra1929.tableCode_eq ▸ encodesTable_tableCode Ra1929.cycles } 249822
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1930.table, code := 9921120964043607875421197496008052801,
        encodes := Ra1930.tableCode_eq ▸ encodesTable_tableCode Ra1930.cycles } 249823
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1931.table, code := 9921039834484982444459247648182112321,
        encodes := Ra1931.tableCode_eq ▸ encodesTable_tableCode Ra1931.cycles } 249827
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1932.table, code := 9921039834487400296098479114144714817,
        encodes := Ra1932.tableCode_eq ▸ encodesTable_tableCode Ra1932.cycles } 249831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1933.table, code := 9921120964123397051141013820963819585,
        encodes := Ra1933.tableCode_eq ▸ encodesTable_tableCode Ra1933.cycles } 249834
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1934.table, code := 9921120964123397051141013823111303233,
        encodes := Ra1934.tableCode_eq ▸ encodesTable_tableCode Ra1934.cycles } 249835
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1935.table, code := 9921120964125814902780245286926422081,
        encodes := Ra1935.tableCode_eq ▸ encodesTable_tableCode Ra1935.cycles } 249838
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1936.table, code := 9921120964125814902780245289073905729,
        encodes := Ra1936.tableCode_eq ▸ encodesTable_tableCode Ra1936.cycles } 249839
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1937.table, code := 9921039834484982446837148315858243649,
        encodes := Ra1937.tableCode_eq ▸ encodesTable_tableCode Ra1937.cycles } 249841
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1938.table, code := 9921039834484982446909205982910615617,
        encodes := Ra1938.tableCode_eq ▸ encodesTable_tableCode Ra1938.cycles } 249843
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1939.table, code := 9921039834487400298476379781820846145,
        encodes := Ra1939.tableCode_eq ▸ encodesTable_tableCode Ra1939.cycles } 249845
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1940.table, code := 9921039834487400298548437448873218113,
        encodes := Ra1940.tableCode_eq ▸ encodesTable_tableCode Ra1940.cycles } 249847
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1941.table, code := 9921120964123397053518914490787434561,
        encodes := Ra1941.tableCode_eq ▸ encodesTable_tableCode Ra1941.cycles } 249849
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1942.table, code := 9921120964123397053590972155692322881,
        encodes := Ra1942.tableCode_eq ▸ encodesTable_tableCode Ra1942.cycles } 249850
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1943.table, code := 9921120964123397053590972157839806529,
        encodes := Ra1943.tableCode_eq ▸ encodesTable_tableCode Ra1943.cycles } 249851
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1944.table, code := 9921120964125814905158145954602553409,
        encodes := Ra1944.tableCode_eq ▸ encodesTable_tableCode Ra1944.cycles } 249852
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1945.table, code := 9921120964125814905158145956750037057,
        encodes := Ra1945.tableCode_eq ▸ encodesTable_tableCode Ra1945.cycles } 249853
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1946.table, code := 9921120964125814905230203621654925377,
        encodes := Ra1946.tableCode_eq ▸ encodesTable_tableCode Ra1946.cycles } 249854
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1947.table, code := 9921120964125814905230203623802409025,
        encodes := Ra1947.tableCode_eq ▸ encodesTable_tableCode Ra1947.cycles } 249855
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1948.table, code := 9923554850637961335448818885882810433,
        encodes := Ra1948.tableCode_eq ▸ encodesTable_tableCode Ra1948.cycles } 251694
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1949.table, code := 9923554850637961335448818888030294081,
        encodes := Ra1949.tableCode_eq ▸ encodesTable_tableCode Ra1949.cycles } 251695
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1950.table, code := 9923554850635543486259545756796194881,
        encodes := Ra1950.tableCode_eq ▸ encodesTable_tableCode Ra1950.cycles } 251707
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1951.table, code := 9923554850637961337898777220611313729,
        encodes := Ra1951.tableCode_eq ▸ encodesTable_tableCode Ra1951.cycles } 251710
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1952.table, code := 9923554850637961337898777222758797377,
        encodes := Ra1952.tableCode_eq ▸ encodesTable_tableCode Ra1952.cycles } 251711
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1953.table, code := 9926313258341642472747087722612789313,
        encodes := Ra1953.tableCode_eq ▸ encodesTable_tableCode Ra1953.cycles } 251755
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1954.table, code := 9926313258344060324386319186427908161,
        encodes := Ra1954.tableCode_eq ▸ encodesTable_tableCode Ra1954.cycles } 251758
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1955.table, code := 9926313258344060324386319188575391809,
        encodes := Ra1955.tableCode_eq ▸ encodesTable_tableCode Ra1955.cycles } 251759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1956.table, code := 9926313258341642475197046057341292609,
        encodes := Ra1956.tableCode_eq ▸ encodesTable_tableCode Ra1956.cycles } 251771
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1957.table, code := 9926313258344060326764219856251523137,
        encodes := Ra1957.tableCode_eq ▸ encodesTable_tableCode Ra1957.cycles } 251773
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1958.table, code := 9926313258344060326836277521156411457,
        encodes := Ra1958.tableCode_eq ▸ encodesTable_tableCode Ra1958.cycles } 251774
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1959.table, code := 9926313258344060326836277523303895105,
        encodes := Ra1959.tableCode_eq ▸ encodesTable_tableCode Ra1959.cycles } 251775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1960.table, code := 9923473723482680362255507626427420737,
        encodes := Ra1960.tableCode_eq ▸ encodesTable_tableCode Ra1960.cycles } 251811
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1961.table, code := 9923473723485098213894739092390023233,
        encodes := Ra1961.tableCode_eq ▸ encodesTable_tableCode Ra1961.cycles } 251815
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1962.table, code := 9923554853121094968937273801356611649,
        encodes := Ra1962.tableCode_eq ▸ encodesTable_tableCode Ra1962.cycles } 251819
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1963.table, code := 9923554853123512820576505265171730497,
        encodes := Ra1963.tableCode_eq ▸ encodesTable_tableCode Ra1963.cycles } 251822
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1964.table, code := 9923554853123512820576505267319214145,
        encodes := Ra1964.tableCode_eq ▸ encodesTable_tableCode Ra1964.cycles } 251823
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1965.table, code := 9923473723482680364705465961155924033,
        encodes := Ra1965.tableCode_eq ▸ encodesTable_tableCode Ra1965.cycles } 251827
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1966.table, code := 9923473723485098216344697427118526529,
        encodes := Ra1966.tableCode_eq ▸ encodesTable_tableCode Ra1966.cycles } 251831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1967.table, code := 9923554853121094971387232133937631297,
        encodes := Ra1967.tableCode_eq ▸ encodesTable_tableCode Ra1967.cycles } 251834
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1968.table, code := 9923554853121094971387232136085114945,
        encodes := Ra1968.tableCode_eq ▸ encodesTable_tableCode Ra1968.cycles } 251835
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1969.table, code := 9923554853123512823026463599900233793,
        encodes := Ra1969.tableCode_eq ▸ encodesTable_tableCode Ra1969.cycles } 251838
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1970.table, code := 9923554853123512823026463602047717441,
        encodes := Ra1970.tableCode_eq ▸ encodesTable_tableCode Ra1970.cycles } 251839
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1971.table, code := 9926232131188779351193007926972518465,
        encodes := Ra1971.tableCode_eq ▸ encodesTable_tableCode Ra1971.cycles } 251875
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1972.table, code := 9926232131191197202832239392935120961,
        encodes := Ra1972.tableCode_eq ▸ encodesTable_tableCode Ra1972.cycles } 251879
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1973.table, code := 9926313260827193957874774101901709377,
        encodes := Ra1973.tableCode_eq ▸ encodesTable_tableCode Ra1973.cycles } 251883
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1974.table, code := 9926313260829611809514005565716828225,
        encodes := Ra1974.tableCode_eq ▸ encodesTable_tableCode Ra1974.cycles } 251886
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1975.table, code := 9926313260829611809514005567864311873,
        encodes := Ra1975.tableCode_eq ▸ encodesTable_tableCode Ra1975.cycles } 251887
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1976.table, code := 9926232131188779353570908594648649793,
        encodes := Ra1976.tableCode_eq ▸ encodesTable_tableCode Ra1976.cycles } 251889
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1977.table, code := 9926232131188779353642966261701021761,
        encodes := Ra1977.tableCode_eq ▸ encodesTable_tableCode Ra1977.cycles } 251891
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1978.table, code := 9926232131191197205210140060611252289,
        encodes := Ra1978.tableCode_eq ▸ encodesTable_tableCode Ra1978.cycles } 251893
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1979.table, code := 9926232131191197205282197727663624257,
        encodes := Ra1979.tableCode_eq ▸ encodesTable_tableCode Ra1979.cycles } 251895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1980.table, code := 9926313260827193960252674769577840705,
        encodes := Ra1980.tableCode_eq ▸ encodesTable_tableCode Ra1980.cycles } 251897
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1981.table, code := 9926313260827193960324732434482729025,
        encodes := Ra1981.tableCode_eq ▸ encodesTable_tableCode Ra1981.cycles } 251898
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1982.table, code := 9926313260827193960324732436630212673,
        encodes := Ra1982.tableCode_eq ▸ encodesTable_tableCode Ra1982.cycles } 251899
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1983.table, code := 9926313260829611811891906233392959553,
        encodes := Ra1983.tableCode_eq ▸ encodesTable_tableCode Ra1983.cycles } 251900
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1984.table, code := 9926313260829611811891906235540443201,
        encodes := Ra1984.tableCode_eq ▸ encodesTable_tableCode Ra1984.cycles } 251901
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1920 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1920 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1920 + i.val) 0 ≤ Data.profiles (1920 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1920 + i.val) 0 = Data.canonicalMask (1920 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1920 + i.val) < Data.canonicalMask (1920 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1920 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models030
