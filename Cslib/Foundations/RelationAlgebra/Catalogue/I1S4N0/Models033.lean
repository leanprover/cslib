/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2113
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2114
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2115
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2116
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2117
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2118
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2119
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2120
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2121
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2122
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2123
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2124
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2125
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2126
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2127
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2128
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2129
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2130
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2131
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2132
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2133
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2134
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2135
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2136
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2137
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2138
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2139
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2140
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2141
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2142
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2143
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2144
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2145
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2146
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2147
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2148
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2149
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2150
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2151
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2152
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2153
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2154
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2155
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2156
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2157
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2158
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2159
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2160
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2161
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2162
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2163
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2164
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2165
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2166
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2167
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2168
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2169
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2170
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2171
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2172
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2173
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2174
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2175
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2176

/-!
# Certified models 2113–2176 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models033

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2113.table, code := 9921120969387060364891016636748009537,
        encodes := Ra2113.tableCode_eq ▸ encodesTable_tableCode Ra2113.cycles } 258031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2114.table, code := 9921039839748645760659208796547321921,
        encodes := Ra2114.tableCode_eq ▸ encodesTable_tableCode Ra2114.cycles } 258039
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2115.table, code := 9921120969384642515629685838461538369,
        encodes := Ra2115.tableCode_eq ▸ encodesTable_tableCode Ra2115.cycles } 258041
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2116.table, code := 9921120969384642515701743503366426689,
        encodes := Ra2116.tableCode_eq ▸ encodesTable_tableCode Ra2116.cycles } 258042
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2117.table, code := 9921120969384642515701743505513910337,
        encodes := Ra2117.tableCode_eq ▸ encodesTable_tableCode Ra2117.cycles } 258043
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2118.table, code := 9921120969387060367268917304424140865,
        encodes := Ra2118.tableCode_eq ▸ encodesTable_tableCode Ra2118.cycles } 258045
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2119.table, code := 9921120969387060367340974969329029185,
        encodes := Ra2119.tableCode_eq ▸ encodesTable_tableCode Ra2119.cycles } 258046
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2120.table, code := 9921120969387060367340974971476512833,
        encodes := Ra2120.tableCode_eq ▸ encodesTable_tableCode Ra2120.cycles } 258047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2121.table, code := 9923554858382340428886317463184347201,
        encodes := Ra2121.tableCode_eq ▸ encodesTable_tableCode Ra2121.cycles } 259002
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2122.table, code := 9923554858382340428886317465331830849,
        encodes := Ra2122.tableCode_eq ▸ encodesTable_tableCode Ra2122.cycles } 259003
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2123.table, code := 9923554858384758280525548929146949697,
        encodes := Ra2123.tableCode_eq ▸ encodesTable_tableCode Ra2123.cycles } 259006
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2124.table, code := 9923554858384758280525548931294433345,
        encodes := Ra2124.tableCode_eq ▸ encodesTable_tableCode Ra2124.cycles } 259007
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2125.table, code := 9926313266088439417823817763729444929,
        encodes := Ra2125.tableCode_eq ▸ encodesTable_tableCode Ra2125.cycles } 259066
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2126.table, code := 9926313266088439417823817765876928577,
        encodes := Ra2126.tableCode_eq ▸ encodesTable_tableCode Ra2126.cycles } 259067
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2127.table, code := 9926313266090857269463049229692047425,
        encodes := Ra2127.tableCode_eq ▸ encodesTable_tableCode Ra2127.cycles } 259070
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2128.table, code := 9926313266090857269463049231839531073,
        encodes := Ra2128.tableCode_eq ▸ encodesTable_tableCode Ra2128.cycles } 259071
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2129.table, code := 9923554858382340431048045149030715457,
        encodes := Ra2129.tableCode_eq ▸ encodesTable_tableCode Ra2129.cycles } 260011
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2130.table, code := 9923554858384758282687276612845834305,
        encodes := Ra2130.tableCode_eq ▸ encodesTable_tableCode Ra2130.cycles } 260014
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2131.table, code := 9923554858384758282687276614993317953,
        encodes := Ra2131.tableCode_eq ▸ encodesTable_tableCode Ra2131.cycles } 260015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2132.table, code := 9923554858382340433498003483759218753,
        encodes := Ra2132.tableCode_eq ▸ encodesTable_tableCode Ra2132.cycles } 260027
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2133.table, code := 9923554858384758285065177282669449281,
        encodes := Ra2133.tableCode_eq ▸ encodesTable_tableCode Ra2133.cycles } 260029
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2134.table, code := 9923554858384758285137234947574337601,
        encodes := Ra2134.tableCode_eq ▸ encodesTable_tableCode Ra2134.cycles } 260030
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2135.table, code := 9923554858384758285137234949721821249,
        encodes := Ra2135.tableCode_eq ▸ encodesTable_tableCode Ra2135.cycles } 260031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2136.table, code := 9926313266088439419985545449575813185,
        encodes := Ra2136.tableCode_eq ▸ encodesTable_tableCode Ra2136.cycles } 260075
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2137.table, code := 9926313266090857271624776913390932033,
        encodes := Ra2137.tableCode_eq ▸ encodesTable_tableCode Ra2137.cycles } 260078
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2138.table, code := 9926313266090857271624776915538415681,
        encodes := Ra2138.tableCode_eq ▸ encodesTable_tableCode Ra2138.cycles } 260079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2139.table, code := 9926313266088439422435503784304316481,
        encodes := Ra2139.tableCode_eq ▸ encodesTable_tableCode Ra2139.cycles } 260091
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2140.table, code := 9926313266090857274002677583214547009,
        encodes := Ra2140.tableCode_eq ▸ encodesTable_tableCode Ra2140.cycles } 260093
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2141.table, code := 9926313266090857274074735248119435329,
        encodes := Ra2141.tableCode_eq ▸ encodesTable_tableCode Ra2141.cycles } 260094
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2142.table, code := 9926313266090857274074735250266918977,
        encodes := Ra2142.tableCode_eq ▸ encodesTable_tableCode Ra2142.cycles } 260095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2143.table, code := 9923554858457293912424539962246172737,
        encodes := Ra2143.tableCode_eq ▸ encodesTable_tableCode Ra2143.cycles } 261022
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2144.table, code := 9923554858457293912424539964393656385,
        encodes := Ra2144.tableCode_eq ▸ encodesTable_tableCode Ra2144.cycles } 261023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2145.table, code := 9923554858539500942161488425135640641,
        encodes := Ra2145.tableCode_eq ▸ encodesTable_tableCode Ra2145.cycles } 261053
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2146.table, code := 9923554858539500942233546090040528961,
        encodes := Ra2146.tableCode_eq ▸ encodesTable_tableCode Ra2146.cycles } 261054
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2147.table, code := 9923554858539500942233546092188012609,
        encodes := Ra2147.tableCode_eq ▸ encodesTable_tableCode Ra2147.cycles } 261055
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2148.table, code := 9926313266163392901289982597886382145,
        encodes := Ra2148.tableCode_eq ▸ encodesTable_tableCode Ra2148.cycles } 261085
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2149.table, code := 9926313266163392901362040262791270465,
        encodes := Ra2149.tableCode_eq ▸ encodesTable_tableCode Ra2149.cycles } 261086
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2150.table, code := 9926313266163392901362040264938754113,
        encodes := Ra2150.tableCode_eq ▸ encodesTable_tableCode Ra2150.cycles } 261087
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2151.table, code := 9926313266245599928721088058004607041,
        encodes := Ra2151.tableCode_eq ▸ encodesTable_tableCode Ra2151.cycles } 261103
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2152.table, code := 9926313266245599931098988725680738369,
        encodes := Ra2152.tableCode_eq ▸ encodesTable_tableCode Ra2152.cycles } 261117
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2153.table, code := 9926313266245599931171046390585626689,
        encodes := Ra2153.tableCode_eq ▸ encodesTable_tableCode Ra2153.cycles } 261118
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2154.table, code := 9926313266245599931171046392733110337,
        encodes := Ra2154.tableCode_eq ▸ encodesTable_tableCode Ra2154.cycles } 261119
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2155.table, code := 9923554858457293917036225982821044289,
        encodes := Ra2155.tableCode_eq ▸ encodesTable_tableCode Ra2155.cycles } 262047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2156.table, code := 9923554858539500944395273775886897217,
        encodes := Ra2156.tableCode_eq ▸ encodesTable_tableCode Ra2156.cycles } 262063
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2157.table, code := 9923554858539500946845232110615400513,
        encodes := Ra2157.tableCode_eq ▸ encodesTable_tableCode Ra2157.cycles } 262079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2158.table, code := 9926313266163392903523767948637638721,
        encodes := Ra2158.tableCode_eq ▸ encodesTable_tableCode Ra2158.cycles } 262095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2159.table, code := 9926313266163392905973726283366142017,
        encodes := Ra2159.tableCode_eq ▸ encodesTable_tableCode Ra2159.cycles } 262111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2160.table, code := 9926313266245599933332774076431994945,
        encodes := Ra2160.tableCode_eq ▸ encodesTable_tableCode Ra2160.cycles } 262127
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2161.table, code := 9926313266245599935782732411160498241,
        encodes := Ra2161.tableCode_eq ▸ encodesTable_tableCode Ra2161.cycles } 262143
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2162.table, code := 20624473086668962321541049374002647105,
        encodes := Ra2162.tableCode_eq ▸ encodesTable_tableCode Ra2162.cycles } 362023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2163.table, code := 20624473086668962323991007708731150401,
        encodes := Ra2163.tableCode_eq ▸ encodesTable_tableCode Ra2163.cycles } 362039
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2164.table, code := 20624473089154513809118694088020070465,
        encodes := Ra2164.tableCode_eq ▸ encodesTable_tableCode Ra2164.cycles } 362167
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2165.table, code := 20710713974036748400899702388284461121,
        encodes := Ra2165.tableCode_eq ▸ encodesTable_tableCode Ra2165.cycles } 362495
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2166.table, code := 20624473086741497953440040407101870145,
        encodes := Ra2166.tableCode_eq ▸ encodesTable_tableCode Ra2166.cycles } 364039
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2167.table, code := 20624554216379912560121806579883577409,
        encodes := Ra2167.tableCode_eq ▸ encodesTable_tableCode Ra2167.cycles } 364046
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2168.table, code := 20624554216379912560121806582031061057,
        encodes := Ra2168.tableCode_eq ▸ encodesTable_tableCode Ra2168.cycles } 364047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2169.table, code := 20624473086741497955889998741830373441,
        encodes := Ra2169.tableCode_eq ▸ encodesTable_tableCode Ra2169.cycles } 364055
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2170.table, code := 20624473086823704983249046534896226369,
        encodes := Ra2170.tableCode_eq ▸ encodesTable_tableCode Ra2170.cycles } 364071
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2171.table, code := 20624473086823704985699004869624729665,
        encodes := Ra2171.tableCode_eq ▸ encodesTable_tableCode Ra2171.cycles } 364087
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2172.table, code := 20627231494447596942377540707646967873,
        encodes := Ra2172.tableCode_eq ▸ encodesTable_tableCode Ra2172.cycles } 364103
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2173.table, code := 20627312624086011549059306880428675137,
        encodes := Ra2173.tableCode_eq ▸ encodesTable_tableCode Ra2173.cycles } 364110
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2174.table, code := 20627312624086011549059306882576158785,
        encodes := Ra2174.tableCode_eq ▸ encodesTable_tableCode Ra2174.cycles } 364111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2175.table, code := 20627231494447596944827499042375471169,
        encodes := Ra2175.tableCode_eq ▸ encodesTable_tableCode Ra2175.cycles } 364119
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2176.table, code := 20627312624086011551437207550252290113,
        encodes := Ra2176.tableCode_eq ▸ encodesTable_tableCode Ra2176.cycles } 364125
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2112 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2112 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2112 + i.val) 0 ≤ Data.profiles (2112 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2112 + i.val) 0 = Data.canonicalMask (2112 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2112 + i.val) < Data.canonicalMask (2112 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2112 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models033
