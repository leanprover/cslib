/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2241
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2242
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2243
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2244
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2245
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2246
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2247
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2248
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2249
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2250
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2251
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2252
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2253
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2254
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2255
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2256
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2257
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2258
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2259
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2260
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2261
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2262
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2263
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2264
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2265
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2266
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2267
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2268
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2269
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2270
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2271
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2272
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2273
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2274
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2275
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2276
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2277
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2278
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2279
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2280
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2281
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2282
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2283
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2284
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2285
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2286
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2287
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2288
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2289
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2290
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2291
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2292
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2293
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2294
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2295
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2296
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2297
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2298
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2299
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2300
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2301
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2302
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2303
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2304

/-!
# Certified models 2241–2304 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models035

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2241.table, code := 20710713976884978007331820052892880961,
        encodes := Ra2241.tableCode_eq ▸ encodesTable_tableCode Ra2241.cycles } 372558
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2242.table, code := 20710713976884978007331820055040364609,
        encodes := Ra2242.tableCode_eq ▸ encodesTable_tableCode Ra2242.cycles } 372559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2243.table, code := 20710632849811904066325415588907978817,
        encodes := Ra2243.tableCode_eq ▸ encodesTable_tableCode Ra2243.cycles } 372721
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2244.table, code := 20710632849811904066397473255960350785,
        encodes := Ra2244.tableCode_eq ▸ encodesTable_tableCode Ra2244.cycles } 372723
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2245.table, code := 20710632849814321918036704721922953281,
        encodes := Ra2245.tableCode_eq ▸ encodesTable_tableCode Ra2245.cycles } 372727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2246.table, code := 20710713979450318673007181763837169729,
        encodes := Ra2246.tableCode_eq ▸ encodesTable_tableCode Ra2246.cycles } 372729
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2247.table, code := 20710713979450318673079239430889541697,
        encodes := Ra2247.tableCode_eq ▸ encodesTable_tableCode Ra2247.cycles } 372731
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2248.table, code := 20710713979452736524718470894704660545,
        encodes := Ra2248.tableCode_eq ▸ encodesTable_tableCode Ra2248.cycles } 372734
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2249.table, code := 20710713979452736524718470896852144193,
        encodes := Ra2249.tableCode_eq ▸ encodesTable_tableCode Ra2249.cycles } 372735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2250.table, code := 20715825144032567337120762619643564097,
        encodes := Ra2250.tableCode_eq ▸ encodesTable_tableCode Ra2250.cycles } 374629
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2251.table, code := 20715825144032567337192820286695936065,
        encodes := Ra2251.tableCode_eq ▸ encodesTable_tableCode Ra2251.cycles } 374631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2252.table, code := 20715906273670981943802528794572755009,
        encodes := Ra2252.tableCode_eq ▸ encodesTable_tableCode Ra2252.cycles } 374637
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2253.table, code := 20715906273670981943874586459477643329,
        encodes := Ra2253.tableCode_eq ▸ encodesTable_tableCode Ra2253.cycles } 374638
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2254.table, code := 20715906273670981943874586461625126977,
        encodes := Ra2254.tableCode_eq ▸ encodesTable_tableCode Ra2254.cycles } 374639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2255.table, code := 20715825144032567339570720954372067393,
        encodes := Ra2255.tableCode_eq ▸ encodesTable_tableCode Ra2255.cycles } 374645
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2256.table, code := 20715825144032567339642778621424439361,
        encodes := Ra2256.tableCode_eq ▸ encodesTable_tableCode Ra2256.cycles } 374647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2257.table, code := 20715906273670981946252487129301258305,
        encodes := Ra2257.tableCode_eq ▸ encodesTable_tableCode Ra2257.cycles } 374653
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2258.table, code := 20715906273670981946324544794206146625,
        encodes := Ra2258.tableCode_eq ▸ encodesTable_tableCode Ra2258.cycles } 374654
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2259.table, code := 20715906273670981946324544796353630273,
        encodes := Ra2259.tableCode_eq ▸ encodesTable_tableCode Ra2259.cycles } 374655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2260.table, code := 20715825146515700970609217532969881665,
        encodes := Ra2260.tableCode_eq ▸ encodesTable_tableCode Ra2260.cycles } 374753
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2261.table, code := 20715825146515700970681275200022253633,
        encodes := Ra2261.tableCode_eq ▸ encodesTable_tableCode Ra2261.cycles } 374755
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2262.table, code := 20715825146518118822248448998932484161,
        encodes := Ra2262.tableCode_eq ▸ encodesTable_tableCode Ra2262.cycles } 374757
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2263.table, code := 20715825146518118822320506665984856129,
        encodes := Ra2263.tableCode_eq ▸ encodesTable_tableCode Ra2263.cycles } 374759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2264.table, code := 20715906276154115577290983707899072577,
        encodes := Ra2264.tableCode_eq ▸ encodesTable_tableCode Ra2264.cycles } 374761
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2265.table, code := 20715906276154115577363041374951444545,
        encodes := Ra2265.tableCode_eq ▸ encodesTable_tableCode Ra2265.cycles } 374763
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2266.table, code := 20715906276156533428930215173861675073,
        encodes := Ra2266.tableCode_eq ▸ encodesTable_tableCode Ra2266.cycles } 374765
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2267.table, code := 20715906276156533429002272838766563393,
        encodes := Ra2267.tableCode_eq ▸ encodesTable_tableCode Ra2267.cycles } 374766
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2268.table, code := 20715906276156533429002272840914047041,
        encodes := Ra2268.tableCode_eq ▸ encodesTable_tableCode Ra2268.cycles } 374767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2269.table, code := 20715825146515700973059175867698384961,
        encodes := Ra2269.tableCode_eq ▸ encodesTable_tableCode Ra2269.cycles } 374769
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2270.table, code := 20715825146515700973131233534750756929,
        encodes := Ra2270.tableCode_eq ▸ encodesTable_tableCode Ra2270.cycles } 374771
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2271.table, code := 20715825146518118824698407333660987457,
        encodes := Ra2271.tableCode_eq ▸ encodesTable_tableCode Ra2271.cycles } 374773
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2272.table, code := 20715825146518118824770465000713359425,
        encodes := Ra2272.tableCode_eq ▸ encodesTable_tableCode Ra2272.cycles } 374775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2273.table, code := 20715906276154115579740942042627575873,
        encodes := Ra2273.tableCode_eq ▸ encodesTable_tableCode Ra2273.cycles } 374777
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2274.table, code := 20715906276154115579812999709679947841,
        encodes := Ra2274.tableCode_eq ▸ encodesTable_tableCode Ra2274.cycles } 374779
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2275.table, code := 20715906276156533431380173508590178369,
        encodes := Ra2275.tableCode_eq ▸ encodesTable_tableCode Ra2275.cycles } 374781
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2276.table, code := 20715906276156533431452231173495066689,
        encodes := Ra2276.tableCode_eq ▸ encodesTable_tableCode Ra2276.cycles } 374782
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2277.table, code := 20715906276156533431452231175642550337,
        encodes := Ra2277.tableCode_eq ▸ encodesTable_tableCode Ra2277.cycles } 374783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2278.table, code := 20713066736478793156162357997382930497,
        encodes := Ra2278.tableCode_eq ▸ encodesTable_tableCode Ra2278.cycles } 375603
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2279.table, code := 20713066736481211007801589463345532993,
        encodes := Ra2279.tableCode_eq ▸ encodesTable_tableCode Ra2279.cycles } 375607
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2280.table, code := 20713147866117207762844124172312121409,
        encodes := Ra2280.tableCode_eq ▸ encodesTable_tableCode Ra2280.cycles } 375611
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2281.table, code := 20713147866119625614483355636127240257,
        encodes := Ra2281.tableCode_eq ▸ encodesTable_tableCode Ra2281.cycles } 375614
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2282.table, code := 20713147866119625614483355638274723905,
        encodes := Ra2282.tableCode_eq ▸ encodesTable_tableCode Ra2282.cycles } 375615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2283.table, code := 20715825144184892145027800630875656257,
        encodes := Ra2283.tableCode_eq ▸ encodesTable_tableCode Ra2283.cycles } 375665
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2284.table, code := 20715825144184892145099858297928028225,
        encodes := Ra2284.tableCode_eq ▸ encodesTable_tableCode Ra2284.cycles } 375667
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2285.table, code := 20715825144187309996667032096838258753,
        encodes := Ra2285.tableCode_eq ▸ encodesTable_tableCode Ra2285.cycles } 375669
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2286.table, code := 20715825144187309996739089763890630721,
        encodes := Ra2286.tableCode_eq ▸ encodesTable_tableCode Ra2286.cycles } 375671
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2287.table, code := 20715906273823306751709566805804847169,
        encodes := Ra2287.tableCode_eq ▸ encodesTable_tableCode Ra2287.cycles } 375673
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2288.table, code := 20715906273823306751781624472857219137,
        encodes := Ra2288.tableCode_eq ▸ encodesTable_tableCode Ra2288.cycles } 375675
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2289.table, code := 20715906273825724603348798271767449665,
        encodes := Ra2289.tableCode_eq ▸ encodesTable_tableCode Ra2289.cycles } 375677
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2290.table, code := 20715906273825724603420855936672337985,
        encodes := Ra2290.tableCode_eq ▸ encodesTable_tableCode Ra2290.cycles } 375678
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2291.table, code := 20715906273825724603420855938819821633,
        encodes := Ra2291.tableCode_eq ▸ encodesTable_tableCode Ra2291.cycles } 375679
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2292.table, code := 20713066738966762492929275842634453057,
        encodes := Ra2292.tableCode_eq ▸ encodesTable_tableCode Ra2292.cycles } 375735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2293.table, code := 20713147868602759247971810551601041473,
        encodes := Ra2293.tableCode_eq ▸ encodesTable_tableCode Ra2293.cycles } 375739
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2294.table, code := 20713147868605177099611042015416160321,
        encodes := Ra2294.tableCode_eq ▸ encodesTable_tableCode Ra2294.cycles } 375742
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2295.table, code := 20713147868605177099611042017563643969,
        encodes := Ra2295.tableCode_eq ▸ encodesTable_tableCode Ra2295.cycles } 375743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2296.table, code := 20715825146670443630155487010164576321,
        encodes := Ra2296.tableCode_eq ▸ encodesTable_tableCode Ra2296.cycles } 375793
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2297.table, code := 20715825146670443630227544677216948289,
        encodes := Ra2297.tableCode_eq ▸ encodesTable_tableCode Ra2297.cycles } 375795
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2298.table, code := 20715825146672861481794718476127178817,
        encodes := Ra2298.tableCode_eq ▸ encodesTable_tableCode Ra2298.cycles } 375797
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2299.table, code := 20715825146672861481866776143179550785,
        encodes := Ra2299.tableCode_eq ▸ encodesTable_tableCode Ra2299.cycles } 375799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2300.table, code := 20715906276308858236837253185093767233,
        encodes := Ra2300.tableCode_eq ▸ encodesTable_tableCode Ra2300.cycles } 375801
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2301.table, code := 20715906276308858236909310852146139201,
        encodes := Ra2301.tableCode_eq ▸ encodesTable_tableCode Ra2301.cycles } 375803
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2302.table, code := 20715906276311276088476484651056369729,
        encodes := Ra2302.tableCode_eq ▸ encodesTable_tableCode Ra2302.cycles } 375805
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2303.table, code := 20715906276311276088548542315961258049,
        encodes := Ra2303.tableCode_eq ▸ encodesTable_tableCode Ra2303.cycles } 375806
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2304.table, code := 20715906276311276088548542318108741697,
        encodes := Ra2304.tableCode_eq ▸ encodesTable_tableCode Ra2304.cycles } 375807
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2240 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2240 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2240 + i.val) 0 ≤ Data.profiles (2240 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2240 + i.val) 0 = Data.canonicalMask (2240 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2240 + i.val) < Data.canonicalMask (2240 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2240 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models035
