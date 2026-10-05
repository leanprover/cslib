/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2177
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2178
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2179
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2180
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2181
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2182
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2183
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2184
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2185
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2186
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2187
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2188
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2189
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2190
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2191
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2192
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2193
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2194
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2195
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2196
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2197
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2198
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2199
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2200
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2201
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2202
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2203
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2204
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2205
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2206
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2207
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2208
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2209
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2210
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2211
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2212
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2213
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2214
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2215
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2216
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2217
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2218
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2219
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2220
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2221
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2222
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2223
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2224
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2225
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2226
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2227
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2228
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2229
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2230
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2231
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2232
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2233
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2234
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2235
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2236
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2237
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2238
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2239
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2240

/-!
# Certified models 2177–2240 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models034

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2177.table, code := 20627312624086011551509265215157178433,
        encodes := Ra2177.tableCode_eq ▸ encodesTable_tableCode Ra2177.cycles } 364126
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2178.table, code := 20627312624086011551509265217304662081,
        encodes := Ra2178.tableCode_eq ▸ encodesTable_tableCode Ra2178.cycles } 364127
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2179.table, code := 20624473089227049440945627454066921537,
        encodes := Ra2179.tableCode_eq ▸ encodesTable_tableCode Ra2179.cycles } 364181
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2180.table, code := 20624473089306838616737501448222543937,
        encodes := Ra2180.tableCode_eq ▸ encodesTable_tableCode Ra2180.cycles } 364195
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2181.table, code := 20624473089309256468376732914185146433,
        encodes := Ra2181.tableCode_eq ▸ encodesTable_tableCode Ra2181.cycles } 364199
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2182.table, code := 20624473089309256470754633581861277761,
        encodes := Ra2182.tableCode_eq ▸ encodesTable_tableCode Ra2182.cycles } 364213
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2183.table, code := 20624473089309256470826691248913649729,
        encodes := Ra2183.tableCode_eq ▸ encodesTable_tableCode Ra2183.cycles } 364215
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2184.table, code := 20710632841985317938539282532437069889,
        encodes := Ra2184.tableCode_eq ▸ encodesTable_tableCode Ra2184.cycles } 364359
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2185.table, code := 20710713971623732545221048705218777153,
        encodes := Ra2185.tableCode_eq ▸ encodesTable_tableCode Ra2185.cycles } 364366
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2186.table, code := 20710713971623732545221048707366260801,
        encodes := Ra2186.tableCode_eq ▸ encodesTable_tableCode Ra2186.cycles } 364367
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2187.table, code := 20710632844550658604214644241233875009,
        encodes := Ra2187.tableCode_eq ▸ encodesTable_tableCode Ra2187.cycles } 364529
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2188.table, code := 20710632844550658604286701908286246977,
        encodes := Ra2188.tableCode_eq ▸ encodesTable_tableCode Ra2188.cycles } 364531
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2189.table, code := 20710632844553076455853875707196477505,
        encodes := Ra2189.tableCode_eq ▸ encodesTable_tableCode Ra2189.cycles } 364533
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2190.table, code := 20710632844553076455925933374248849473,
        encodes := Ra2190.tableCode_eq ▸ encodesTable_tableCode Ra2190.cycles } 364535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2191.table, code := 20710713974189073210896410416163065921,
        encodes := Ra2191.tableCode_eq ▸ encodesTable_tableCode Ra2191.cycles } 364537
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2192.table, code := 20710713974189073210968468083215437889,
        encodes := Ra2192.tableCode_eq ▸ encodesTable_tableCode Ra2192.cycles } 364539
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2193.table, code := 20710713974191491062535641882125668417,
        encodes := Ra2193.tableCode_eq ▸ encodesTable_tableCode Ra2193.cycles } 364541
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2194.table, code := 20710713974191491062607699547030556737,
        encodes := Ra2194.tableCode_eq ▸ encodesTable_tableCode Ra2194.cycles } 364542
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2195.table, code := 20710713974191491062607699549178040385,
        encodes := Ra2195.tableCode_eq ▸ encodesTable_tableCode Ra2195.cycles } 364543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2196.table, code := 20632504920872015485602073289160921153,
        encodes := Ra2196.tableCode_eq ▸ encodesTable_tableCode Ra2196.cycles } 366191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2197.table, code := 20632504920872015488052031623889424449,
        encodes := Ra2197.tableCode_eq ▸ encodesTable_tableCode Ra2197.cycles } 366207
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2198.table, code := 20715906270895287966891501493239943233,
        encodes := Ra2198.tableCode_eq ▸ encodesTable_tableCode Ra2198.cycles } 366575
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2199.table, code := 20715906270895287969341459827968446529,
        encodes := Ra2199.tableCode_eq ▸ encodesTable_tableCode Ra2199.cycles } 366591
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2200.table, code := 20629746513238452126401836335868678209,
        encodes := Ra2200.tableCode_eq ▸ encodesTable_tableCode Ra2200.cycles } 367134
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2201.table, code := 20629746513238452126401836338016161857,
        encodes := Ra2201.tableCode_eq ▸ encodesTable_tableCode Ra2201.cycles } 367135
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2202.table, code := 20632504920944551115339336636413775937,
        encodes := Ra2202.tableCode_eq ▸ encodesTable_tableCode Ra2202.cycles } 367198
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2203.table, code := 20632504920944551115339336638561259585,
        encodes := Ra2203.tableCode_eq ▸ encodesTable_tableCode Ra2203.cycles } 367199
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2204.table, code := 20632504921026758145076285099303243841,
        encodes := Ra2204.tableCode_eq ▸ encodesTable_tableCode Ra2204.cycles } 367229
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2205.table, code := 20632504921026758145148342764208132161,
        encodes := Ra2205.tableCode_eq ▸ encodesTable_tableCode Ra2205.cycles } 367230
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2206.table, code := 20632504921026758145148342766355615809,
        encodes := Ra2206.tableCode_eq ▸ encodesTable_tableCode Ra2206.cycles } 367231
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2207.table, code := 20629665386085589004775698875323519041,
        encodes := Ra2207.tableCode_eq ▸ encodesTable_tableCode Ra2207.cycles } 367253
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2208.table, code := 20715825141409198168044715662490472513,
        encodes := Ra2208.tableCode_eq ▸ encodesTable_tableCode Ra2208.cycles } 367601
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2209.table, code := 20715825141409198168116773329542844481,
        encodes := Ra2209.tableCode_eq ▸ encodesTable_tableCode Ra2209.cycles } 367603
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2210.table, code := 20715825141411616019683947128453075009,
        encodes := Ra2210.tableCode_eq ▸ encodesTable_tableCode Ra2210.cycles } 367605
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2211.table, code := 20715825141411616019756004795505446977,
        encodes := Ra2211.tableCode_eq ▸ encodesTable_tableCode Ra2211.cycles } 367607
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2212.table, code := 20715906271047612774798539504472035393,
        encodes := Ra2212.tableCode_eq ▸ encodesTable_tableCode Ra2212.cycles } 367611
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2213.table, code := 20715906271050030626437770968287154241,
        encodes := Ra2213.tableCode_eq ▸ encodesTable_tableCode Ra2213.cycles } 367614
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2214.table, code := 20715906271050030626437770970434637889,
        encodes := Ra2214.tableCode_eq ▸ encodesTable_tableCode Ra2214.cycles } 367615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2215.table, code := 20629746513238452131013522356443549761,
        encodes := Ra2215.tableCode_eq ▸ encodesTable_tableCode Ra2215.cycles } 368159
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2216.table, code := 20632504920944551117501064322260144193,
        encodes := Ra2216.tableCode_eq ▸ encodesTable_tableCode Ra2216.cycles } 368207
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2217.table, code := 20632504920944551119951022656988647489,
        encodes := Ra2217.tableCode_eq ▸ encodesTable_tableCode Ra2217.cycles } 368223
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2218.table, code := 20632504921026758147310070450054500417,
        encodes := Ra2218.tableCode_eq ▸ encodesTable_tableCode Ra2218.cycles } 368239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2219.table, code := 20632504921026758149760028784783003713,
        encodes := Ra2219.tableCode_eq ▸ encodesTable_tableCode Ra2219.cycles } 368255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2220.table, code := 20629665386085589009387384893750906945,
        encodes := Ra2220.tableCode_eq ▸ encodesTable_tableCode Ra2220.cycles } 368277
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2221.table, code := 20715825138843857509430998306849558593,
        encodes := Ra2221.tableCode_eq ▸ encodesTable_tableCode Ra2221.cycles } 368471
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2222.table, code := 20715906268482272116112764479631265857,
        encodes := Ra2222.tableCode_eq ▸ encodesTable_tableCode Ra2222.cycles } 368478
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2223.table, code := 20715906268482272116112764481778749505,
        encodes := Ra2223.tableCode_eq ▸ encodesTable_tableCode Ra2223.cycles } 368479
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2224.table, code := 20715825141409198170278501013241729089,
        encodes := Ra2224.tableCode_eq ▸ encodesTable_tableCode Ra2224.cycles } 368611
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2225.table, code := 20715825141411616021917732479204331585,
        encodes := Ra2225.tableCode_eq ▸ encodesTable_tableCode Ra2225.cycles } 368615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2226.table, code := 20715906271047612776960267188170920001,
        encodes := Ra2226.tableCode_eq ▸ encodesTable_tableCode Ra2226.cycles } 368619
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2227.table, code := 20715906271050030628599498651986038849,
        encodes := Ra2227.tableCode_eq ▸ encodesTable_tableCode Ra2227.cycles } 368622
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2228.table, code := 20715906271050030628599498654133522497,
        encodes := Ra2228.tableCode_eq ▸ encodesTable_tableCode Ra2228.cycles } 368623
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2229.table, code := 20715825141409198172656401680917860417,
        encodes := Ra2229.tableCode_eq ▸ encodesTable_tableCode Ra2229.cycles } 368625
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2230.table, code := 20715825141409198172728459347970232385,
        encodes := Ra2230.tableCode_eq ▸ encodesTable_tableCode Ra2230.cycles } 368627
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2231.table, code := 20715825141411616024295633146880462913,
        encodes := Ra2231.tableCode_eq ▸ encodesTable_tableCode Ra2231.cycles } 368629
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2232.table, code := 20715825141411616024367690813932834881,
        encodes := Ra2232.tableCode_eq ▸ encodesTable_tableCode Ra2232.cycles } 368631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2233.table, code := 20715906271047612779338167855847051329,
        encodes := Ra2233.tableCode_eq ▸ encodesTable_tableCode Ra2233.cycles } 368633
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2234.table, code := 20715906271047612779410225522899423297,
        encodes := Ra2234.tableCode_eq ▸ encodesTable_tableCode Ra2234.cycles } 368635
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2235.table, code := 20715906271050030630977399321809653825,
        encodes := Ra2235.tableCode_eq ▸ encodesTable_tableCode Ra2235.cycles } 368637
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2236.table, code := 20715906271050030631049456986714542145,
        encodes := Ra2236.tableCode_eq ▸ encodesTable_tableCode Ra2236.cycles } 368638
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2237.table, code := 20715906271050030631049456988862025793,
        encodes := Ra2237.tableCode_eq ▸ encodesTable_tableCode Ra2237.cycles } 368639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2238.table, code := 20624473094488294903128456468793397313,
        encodes := Ra2238.tableCode_eq ▸ encodesTable_tableCode Ra2238.cycles } 372375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2239.table, code := 20624473094570501932937462596587753537,
        encodes := Ra2239.tableCode_eq ▸ encodesTable_tableCode Ra2239.cycles } 372407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2240.table, code := 20710632847246563400650053880111173697,
        encodes := Ra2240.tableCode_eq ▸ encodesTable_tableCode Ra2240.cycles } 372551
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2176 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2176 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2176 + i.val) 0 ≤ Data.profiles (2176 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2176 + i.val) 0 = Data.canonicalMask (2176 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2176 + i.val) < Data.canonicalMask (2176 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2176 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models034
