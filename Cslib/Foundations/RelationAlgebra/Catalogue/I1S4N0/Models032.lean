/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2049
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2050
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2051
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2052
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2053
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2054
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2055
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2056
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2057
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2058
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2059
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2060
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2061
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2062
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2063
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2064
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2065
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2066
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2067
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2068
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2069
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2070
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2071
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2072
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2073
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2074
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2075
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2076
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2077
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2078
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2079
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2080
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2081
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2082
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2083
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2084
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2085
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2086
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2087
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2088
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2089
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2090
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2091
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2092
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2093
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2094
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2095
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2096
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2097
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2098
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2099
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2100
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2101
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2102
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2103
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2104
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2105
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2106
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2107
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2108
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2109
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2110
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2111
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2112

/-!
# Certified models 2049–2112 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models032

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2049.table, code := 9926232131263732837181188760762847297,
        encodes := Ra2049.tableCode_eq ▸ encodesTable_tableCode Ra2049.cycles } 253911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2050.table, code := 9926313260902147443790897268639666241,
        encodes := Ra2050.tableCode_eq ▸ encodesTable_tableCode Ra2050.cycles } 253917
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2051.table, code := 9926313260902147443862954933544554561,
        encodes := Ra2051.tableCode_eq ▸ encodesTable_tableCode Ra2051.cycles } 253918
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2052.table, code := 9926313260902147443862954935692038209,
        encodes := Ra2052.tableCode_eq ▸ encodesTable_tableCode Ra2052.cycles } 253919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2053.table, code := 9926232131343522012901005087866097729,
        encodes := Ra2053.tableCode_eq ▸ encodesTable_tableCode Ra2053.cycles } 253923
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2054.table, code := 9926232131345939864540236553828700225,
        encodes := Ra2054.tableCode_eq ▸ encodesTable_tableCode Ra2054.cycles } 253927
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2055.table, code := 9926313260981936619582771262795288641,
        encodes := Ra2055.tableCode_eq ▸ encodesTable_tableCode Ra2055.cycles } 253931
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2056.table, code := 9926313260984354471222002726610407489,
        encodes := Ra2056.tableCode_eq ▸ encodesTable_tableCode Ra2056.cycles } 253934
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2057.table, code := 9926313260984354471222002728757891137,
        encodes := Ra2057.tableCode_eq ▸ encodesTable_tableCode Ra2057.cycles } 253935
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2058.table, code := 9926232131343522015278905755542229057,
        encodes := Ra2058.tableCode_eq ▸ encodesTable_tableCode Ra2058.cycles } 253937
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2059.table, code := 9926232131343522015350963422594601025,
        encodes := Ra2059.tableCode_eq ▸ encodesTable_tableCode Ra2059.cycles } 253939
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2060.table, code := 9926232131345939866918137221504831553,
        encodes := Ra2060.tableCode_eq ▸ encodesTable_tableCode Ra2060.cycles } 253941
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2061.table, code := 9926232131345939866990194888557203521,
        encodes := Ra2061.tableCode_eq ▸ encodesTable_tableCode Ra2061.cycles } 253943
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2062.table, code := 9926313260981936621960671930471419969,
        encodes := Ra2062.tableCode_eq ▸ encodesTable_tableCode Ra2062.cycles } 253945
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2063.table, code := 9926313260981936622032729595376308289,
        encodes := Ra2063.tableCode_eq ▸ encodesTable_tableCode Ra2063.cycles } 253946
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2064.table, code := 9926313260981936622032729597523791937,
        encodes := Ra2064.tableCode_eq ▸ encodesTable_tableCode Ra2064.cycles } 253947
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2065.table, code := 9926313260984354473599903394286538817,
        encodes := Ra2065.tableCode_eq ▸ encodesTable_tableCode Ra2065.cycles } 253948
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2066.table, code := 9926313260984354473599903396434022465,
        encodes := Ra2066.tableCode_eq ▸ encodesTable_tableCode Ra2066.cycles } 253949
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2067.table, code := 9926313260984354473671961061338910785,
        encodes := Ra2067.tableCode_eq ▸ encodesTable_tableCode Ra2067.cycles } 253950
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2068.table, code := 9926313260984354473671961063486394433,
        encodes := Ra2068.tableCode_eq ▸ encodesTable_tableCode Ra2068.cycles } 253951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2069.table, code := 9918362561523800864984188377022861377,
        encodes := Ra2069.tableCode_eq ▸ encodesTable_tableCode Ra2069.cycles } 255929
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2070.table, code := 9918362561523800865056246041927749697,
        encodes := Ra2070.tableCode_eq ▸ encodesTable_tableCode Ra2070.cycles } 255930
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2071.table, code := 9918362561523800865056246044075233345,
        encodes := Ra2071.tableCode_eq ▸ encodesTable_tableCode Ra2071.cycles } 255931
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2072.table, code := 9918362561526218716623419842985463873,
        encodes := Ra2072.tableCode_eq ▸ encodesTable_tableCode Ra2072.cycles } 255933
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2073.table, code := 9918362561526218716695477507890352193,
        encodes := Ra2073.tableCode_eq ▸ encodesTable_tableCode Ra2073.cycles } 255934
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2074.table, code := 9918362561526218716695477510037835841,
        encodes := Ra2074.tableCode_eq ▸ encodesTable_tableCode Ra2074.cycles } 255935
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2075.table, code := 9921039839591485244862021834962636865,
        encodes := Ra2075.tableCode_eq ▸ encodesTable_tableCode Ra2075.cycles } 255971
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2076.table, code := 9921039839593903096501253300925239361,
        encodes := Ra2076.tableCode_eq ▸ encodesTable_tableCode Ra2076.cycles } 255975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2077.table, code := 9921120969229899851543788007744344129,
        encodes := Ra2077.tableCode_eq ▸ encodesTable_tableCode Ra2077.cycles } 255978
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2078.table, code := 9921120969229899851543788009891827777,
        encodes := Ra2078.tableCode_eq ▸ encodesTable_tableCode Ra2078.cycles } 255979
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2079.table, code := 9921120969232317703183019473706946625,
        encodes := Ra2079.tableCode_eq ▸ encodesTable_tableCode Ra2079.cycles } 255982
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2080.table, code := 9921120969232317703183019475854430273,
        encodes := Ra2080.tableCode_eq ▸ encodesTable_tableCode Ra2080.cycles } 255983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2081.table, code := 9921039839591485247311980169691140161,
        encodes := Ra2081.tableCode_eq ▸ encodesTable_tableCode Ra2081.cycles } 255987
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2082.table, code := 9921039839593903098879153968601370689,
        encodes := Ra2082.tableCode_eq ▸ encodesTable_tableCode Ra2082.cycles } 255989
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2083.table, code := 9921039839593903098951211635653742657,
        encodes := Ra2083.tableCode_eq ▸ encodesTable_tableCode Ra2083.cycles } 255991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2084.table, code := 9921120969229899853921688677567959105,
        encodes := Ra2084.tableCode_eq ▸ encodesTable_tableCode Ra2084.cycles } 255993
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2085.table, code := 9921120969229899853993746342472847425,
        encodes := Ra2085.tableCode_eq ▸ encodesTable_tableCode Ra2085.cycles } 255994
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2086.table, code := 9921120969229899853993746344620331073,
        encodes := Ra2086.tableCode_eq ▸ encodesTable_tableCode Ra2086.cycles } 255995
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2087.table, code := 9921120969232317705560920143530561601,
        encodes := Ra2087.tableCode_eq ▸ encodesTable_tableCode Ra2087.cycles } 255997
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2088.table, code := 9921120969232317705632977808435449921,
        encodes := Ra2088.tableCode_eq ▸ encodesTable_tableCode Ra2088.cycles } 255998
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2089.table, code := 9921120969232317705632977810582933569,
        encodes := Ra2089.tableCode_eq ▸ encodesTable_tableCode Ra2089.cycles } 255999
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2090.table, code := 9918281432042546769271750161273720897,
        encodes := Ra2090.tableCode_eq ▸ encodesTable_tableCode Ra2090.cycles } 257959
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2091.table, code := 9918362561678543524314284868092825665,
        encodes := Ra2091.tableCode_eq ▸ encodesTable_tableCode Ra2091.cycles } 257962
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2092.table, code := 9918362561678543524314284870240309313,
        encodes := Ra2092.tableCode_eq ▸ encodesTable_tableCode Ra2092.cycles } 257963
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2093.table, code := 9918362561680961375953516334055428161,
        encodes := Ra2093.tableCode_eq ▸ encodesTable_tableCode Ra2093.cycles } 257966
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2094.table, code := 9918362561680961375953516336202911809,
        encodes := Ra2094.tableCode_eq ▸ encodesTable_tableCode Ra2094.cycles } 257967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2095.table, code := 9918281432042546771721708496002224193,
        encodes := Ra2095.tableCode_eq ▸ encodesTable_tableCode Ra2095.cycles } 257975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2096.table, code := 9918362561678543526692185537916440641,
        encodes := Ra2096.tableCode_eq ▸ encodesTable_tableCode Ra2096.cycles } 257977
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2097.table, code := 9918362561678543526764243202821328961,
        encodes := Ra2097.tableCode_eq ▸ encodesTable_tableCode Ra2097.cycles } 257978
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2098.table, code := 9918362561678543526764243204968812609,
        encodes := Ra2098.tableCode_eq ▸ encodesTable_tableCode Ra2098.cycles } 257979
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2099.table, code := 9918362561680961378331417003879043137,
        encodes := Ra2099.tableCode_eq ▸ encodesTable_tableCode Ra2099.cycles } 257981
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2100.table, code := 9918362561680961378403474668783931457,
        encodes := Ra2100.tableCode_eq ▸ encodesTable_tableCode Ra2100.cycles } 257982
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2101.table, code := 9918362561680961378403474670931415105,
        encodes := Ra2101.tableCode_eq ▸ encodesTable_tableCode Ra2101.cycles } 257983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2102.table, code := 9921039839666438728400244334024462401,
        encodes := Ra2102.tableCode_eq ▸ encodesTable_tableCode Ra2102.cycles } 257991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2103.table, code := 9921120969304853335082010506806169665,
        encodes := Ra2103.tableCode_eq ▸ encodesTable_tableCode Ra2103.cycles } 257998
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2104.table, code := 9921120969304853335082010508953653313,
        encodes := Ra2104.tableCode_eq ▸ encodesTable_tableCode Ra2104.cycles } 257999
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2105.table, code := 9921039839666438730850202668752965697,
        encodes := Ra2105.tableCode_eq ▸ encodesTable_tableCode Ra2105.cycles } 258007
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2106.table, code := 9921120969304853337459911176629784641,
        encodes := Ra2106.tableCode_eq ▸ encodesTable_tableCode Ra2106.cycles } 258013
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2107.table, code := 9921120969304853337531968841534672961,
        encodes := Ra2107.tableCode_eq ▸ encodesTable_tableCode Ra2107.cycles } 258014
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2108.table, code := 9921120969304853337531968843682156609,
        encodes := Ra2108.tableCode_eq ▸ encodesTable_tableCode Ra2108.cycles } 258015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2109.table, code := 9921039839748645758209250461818818625,
        encodes := Ra2109.tableCode_eq ▸ encodesTable_tableCode Ra2109.cycles } 258023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2110.table, code := 9921120969384642513251785168637923393,
        encodes := Ra2110.tableCode_eq ▸ encodesTable_tableCode Ra2110.cycles } 258026
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2111.table, code := 9921120969384642513251785170785407041,
        encodes := Ra2111.tableCode_eq ▸ encodesTable_tableCode Ra2111.cycles } 258027
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2112.table, code := 9921120969387060364891016634600525889,
        encodes := Ra2112.tableCode_eq ▸ encodesTable_tableCode Ra2112.cycles } 258030
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2048 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2048 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2048 + i.val) 0 ≤ Data.profiles (2048 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2048 + i.val) 0 = Data.canonicalMask (2048 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2048 + i.val) < Data.canonicalMask (2048 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2048 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models032
