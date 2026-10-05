/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2305
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2306
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2307
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2308
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2309
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2310
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2311
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2312
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2313
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2314
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2315
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2316
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2317
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2318
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2319
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2320
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2321
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2322
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2323
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2324
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2325
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2326
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2327
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2328
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2329
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2330
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2331
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2332
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2333
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2334
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2335
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2336
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2337
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2338
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2339
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2340
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2341
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2342
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2343
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2344
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2345
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2346
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2347
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2348
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2349
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2350
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2351
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2352
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2353
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2354
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2355
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2356
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2357
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2358
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2359
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2360
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2361
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2362
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2363
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2364
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2365
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2366
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2367
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2368

/-!
# Certified models 2305–2368 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models036

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2305.table, code := 20713066736478793160774044015810318401,
        encodes := Ra2305.tableCode_eq ▸ encodesTable_tableCode Ra2305.cycles } 376627
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2306.table, code := 20713066736481211012413275481772920897,
        encodes := Ra2306.tableCode_eq ▸ encodesTable_tableCode Ra2306.cycles } 376631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2307.table, code := 20713147866117207767455810190739509313,
        encodes := Ra2307.tableCode_eq ▸ encodesTable_tableCode Ra2307.cycles } 376635
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2308.table, code := 20713147866119625619095041654554628161,
        encodes := Ra2308.tableCode_eq ▸ encodesTable_tableCode Ra2308.cycles } 376638
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2309.table, code := 20713147866119625619095041656702111809,
        encodes := Ra2309.tableCode_eq ▸ encodesTable_tableCode Ra2309.cycles } 376639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2310.table, code := 20715825144184892147189528314574540865,
        encodes := Ra2310.tableCode_eq ▸ encodesTable_tableCode Ra2310.cycles } 376673
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2311.table, code := 20715825144184892147261585981626912833,
        encodes := Ra2311.tableCode_eq ▸ encodesTable_tableCode Ra2311.cycles } 376675
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2312.table, code := 20715825144187309998828759780537143361,
        encodes := Ra2312.tableCode_eq ▸ encodesTable_tableCode Ra2312.cycles } 376677
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2313.table, code := 20715825144187309998900817447589515329,
        encodes := Ra2313.tableCode_eq ▸ encodesTable_tableCode Ra2313.cycles } 376679
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2314.table, code := 20715906273823306753871294489503731777,
        encodes := Ra2314.tableCode_eq ▸ encodesTable_tableCode Ra2314.cycles } 376681
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2315.table, code := 20715906273823306753943352156556103745,
        encodes := Ra2315.tableCode_eq ▸ encodesTable_tableCode Ra2315.cycles } 376683
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2316.table, code := 20715906273825724605510525955466334273,
        encodes := Ra2316.tableCode_eq ▸ encodesTable_tableCode Ra2316.cycles } 376685
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2317.table, code := 20715906273825724605582583620371222593,
        encodes := Ra2317.tableCode_eq ▸ encodesTable_tableCode Ra2317.cycles } 376686
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2318.table, code := 20715906273825724605582583622518706241,
        encodes := Ra2318.tableCode_eq ▸ encodesTable_tableCode Ra2318.cycles } 376687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2319.table, code := 20715825144184892149639486649303044161,
        encodes := Ra2319.tableCode_eq ▸ encodesTable_tableCode Ra2319.cycles } 376689
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2320.table, code := 20715825144184892149711544316355416129,
        encodes := Ra2320.tableCode_eq ▸ encodesTable_tableCode Ra2320.cycles } 376691
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2321.table, code := 20715825144187310001278718115265646657,
        encodes := Ra2321.tableCode_eq ▸ encodesTable_tableCode Ra2321.cycles } 376693
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2322.table, code := 20715825144187310001350775782318018625,
        encodes := Ra2322.tableCode_eq ▸ encodesTable_tableCode Ra2322.cycles } 376695
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2323.table, code := 20715906273823306756321252824232235073,
        encodes := Ra2323.tableCode_eq ▸ encodesTable_tableCode Ra2323.cycles } 376697
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2324.table, code := 20715906273823306756393310491284607041,
        encodes := Ra2324.tableCode_eq ▸ encodesTable_tableCode Ra2324.cycles } 376699
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2325.table, code := 20715906273825724607960484290194837569,
        encodes := Ra2325.tableCode_eq ▸ encodesTable_tableCode Ra2325.cycles } 376701
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2326.table, code := 20715906273825724608032541955099725889,
        encodes := Ra2326.tableCode_eq ▸ encodesTable_tableCode Ra2326.cycles } 376702
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2327.table, code := 20715906273825724608032541957247209537,
        encodes := Ra2327.tableCode_eq ▸ encodesTable_tableCode Ra2327.cycles } 376703
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2328.table, code := 20713066738966762497540961861061840961,
        encodes := Ra2328.tableCode_eq ▸ encodesTable_tableCode Ra2328.cycles } 376759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2329.table, code := 20713147868602759252583496570028429377,
        encodes := Ra2329.tableCode_eq ▸ encodesTable_tableCode Ra2329.cycles } 376763
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2330.table, code := 20713147868605177104222728033843548225,
        encodes := Ra2330.tableCode_eq ▸ encodesTable_tableCode Ra2330.cycles } 376766
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2331.table, code := 20713147868605177104222728035991031873,
        encodes := Ra2331.tableCode_eq ▸ encodesTable_tableCode Ra2331.cycles } 376767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2332.table, code := 20715825146670443632317214693863460929,
        encodes := Ra2332.tableCode_eq ▸ encodesTable_tableCode Ra2332.cycles } 376801
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2333.table, code := 20715825146670443632389272360915832897,
        encodes := Ra2333.tableCode_eq ▸ encodesTable_tableCode Ra2333.cycles } 376803
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2334.table, code := 20715825146672861483956446159826063425,
        encodes := Ra2334.tableCode_eq ▸ encodesTable_tableCode Ra2334.cycles } 376805
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2335.table, code := 20715825146672861484028503826878435393,
        encodes := Ra2335.tableCode_eq ▸ encodesTable_tableCode Ra2335.cycles } 376807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2336.table, code := 20715906276308858238998980868792651841,
        encodes := Ra2336.tableCode_eq ▸ encodesTable_tableCode Ra2336.cycles } 376809
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2337.table, code := 20715906276308858239071038535845023809,
        encodes := Ra2337.tableCode_eq ▸ encodesTable_tableCode Ra2337.cycles } 376811
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2338.table, code := 20715906276311276090638212334755254337,
        encodes := Ra2338.tableCode_eq ▸ encodesTable_tableCode Ra2338.cycles } 376813
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2339.table, code := 20715906276311276090710269999660142657,
        encodes := Ra2339.tableCode_eq ▸ encodesTable_tableCode Ra2339.cycles } 376814
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2340.table, code := 20715906276311276090710270001807626305,
        encodes := Ra2340.tableCode_eq ▸ encodesTable_tableCode Ra2340.cycles } 376815
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2341.table, code := 20715825146670443634767173028591964225,
        encodes := Ra2341.tableCode_eq ▸ encodesTable_tableCode Ra2341.cycles } 376817
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2342.table, code := 20715825146670443634839230695644336193,
        encodes := Ra2342.tableCode_eq ▸ encodesTable_tableCode Ra2342.cycles } 376819
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2343.table, code := 20715825146672861486406404494554566721,
        encodes := Ra2343.tableCode_eq ▸ encodesTable_tableCode Ra2343.cycles } 376821
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2344.table, code := 20715825146672861486478462161606938689,
        encodes := Ra2344.tableCode_eq ▸ encodesTable_tableCode Ra2344.cycles } 376823
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2345.table, code := 20715906276308858241448939203521155137,
        encodes := Ra2345.tableCode_eq ▸ encodesTable_tableCode Ra2345.cycles } 376825
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2346.table, code := 20715906276308858241520996870573527105,
        encodes := Ra2346.tableCode_eq ▸ encodesTable_tableCode Ra2346.cycles } 376827
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2347.table, code := 20715906276311276093088170669483757633,
        encodes := Ra2347.tableCode_eq ▸ encodesTable_tableCode Ra2347.cycles } 376829
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2348.table, code := 20715906276311276093160228334388645953,
        encodes := Ra2348.tableCode_eq ▸ encodesTable_tableCode Ra2348.cycles } 376830
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2349.table, code := 20715906276311276093160228336536129601,
        encodes := Ra2349.tableCode_eq ▸ encodesTable_tableCode Ra2349.cycles } 376831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2350.table, code := 20887171094175853677499180664049897537,
        encodes := Ra2350.tableCode_eq ▸ encodesTable_tableCode Ra2350.cycles } 378721
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2351.table, code := 20887171094175853677571238331102269505,
        encodes := Ra2351.tableCode_eq ▸ encodesTable_tableCode Ra2351.cycles } 378723
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2352.table, code := 20887171094178271529210469797064872001,
        encodes := Ra2352.tableCode_eq ▸ encodesTable_tableCode Ra2352.cycles } 378727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2353.table, code := 20887252223814268284180946838979088449,
        encodes := Ra2353.tableCode_eq ▸ encodesTable_tableCode Ra2353.cycles } 378729
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2354.table, code := 20887252223814268284253004506031460417,
        encodes := Ra2354.tableCode_eq ▸ encodesTable_tableCode Ra2354.cycles } 378731
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2355.table, code := 20887252223816686135892235969846579265,
        encodes := Ra2355.tableCode_eq ▸ encodesTable_tableCode Ra2355.cycles } 378734
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2356.table, code := 20887252223816686135892235971994062913,
        encodes := Ra2356.tableCode_eq ▸ encodesTable_tableCode Ra2356.cycles } 378735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2357.table, code := 20887171094175853680021196665830772801,
        encodes := Ra2357.tableCode_eq ▸ encodesTable_tableCode Ra2357.cycles } 378739
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2358.table, code := 20887171094178271531588370464741003329,
        encodes := Ra2358.tableCode_eq ▸ encodesTable_tableCode Ra2358.cycles } 378741
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2359.table, code := 20887171094178271531660428131793375297,
        encodes := Ra2359.tableCode_eq ▸ encodesTable_tableCode Ra2359.cycles } 378743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2360.table, code := 20887252223814268286630905173707591745,
        encodes := Ra2360.tableCode_eq ▸ encodesTable_tableCode Ra2360.cycles } 378745
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2361.table, code := 20887252223814268286702962840759963713,
        encodes := Ra2361.tableCode_eq ▸ encodesTable_tableCode Ra2361.cycles } 378747
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2362.table, code := 20887252223816686138270136639670194241,
        encodes := Ra2362.tableCode_eq ▸ encodesTable_tableCode Ra2362.cycles } 378749
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2363.table, code := 20887252223816686138342194304575082561,
        encodes := Ra2363.tableCode_eq ▸ encodesTable_tableCode Ra2363.cycles } 378750
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2364.table, code := 20887252223816686138342194306722566209,
        encodes := Ra2364.tableCode_eq ▸ encodesTable_tableCode Ra2364.cycles } 378751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2365.table, code := 20887171096661405165076825378067320897,
        encodes := Ra2365.tableCode_eq ▸ encodesTable_tableCode Ra2365.cycles } 378865
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2366.table, code := 20887171096661405165148883045119692865,
        encodes := Ra2366.tableCode_eq ▸ encodesTable_tableCode Ra2366.cycles } 378867
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2367.table, code := 20887171096663823016788114511082295361,
        encodes := Ra2367.tableCode_eq ▸ encodesTable_tableCode Ra2367.cycles } 378871
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2368.table, code := 20887252226299819771758591552996511809,
        encodes := Ra2368.tableCode_eq ▸ encodesTable_tableCode Ra2368.cycles } 378873
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2304 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2304 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2304 + i.val) 0 ≤ Data.profiles (2304 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2304 + i.val) 0 = Data.canonicalMask (2304 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2304 + i.val) < Data.canonicalMask (2304 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2304 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models036
