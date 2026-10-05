/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2369
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2370
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2371
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2372
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2373
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2374
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2375
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2376
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2377
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2378
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2379
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2380
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2381
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2382
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2383
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2384
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2385
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2386
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2387
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2388
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2389
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2390
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2391
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2392
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2393
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2394
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2395
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2396
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2397
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2398
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2399
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2400
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2401
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2402
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2403
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2404
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2405
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2406
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2407
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2408
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2409
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2410
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2411
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2412
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2413
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2414
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2415
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2416
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2417
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2418
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2419
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2420
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2421
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2422
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2423
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2424
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2425
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2426
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2427
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2428
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2429
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2430
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2431
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2432

/-!
# Certified models 2369–2432 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models037

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2369.table, code := 20887252226299819771830649220048883777,
        encodes := Ra2369.tableCode_eq ▸ encodesTable_tableCode Ra2369.cycles } 378875
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2370.table, code := 20887252226302237623469880683864002625,
        encodes := Ra2370.tableCode_eq ▸ encodesTable_tableCode Ra2370.cycles } 378878
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2371.table, code := 20887252226302237623469880686011486273,
        encodes := Ra2371.tableCode_eq ▸ encodesTable_tableCode Ra2371.cycles } 378879
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2372.table, code := 20887171094333014190918466957958451265,
        encodes := Ra2372.tableCode_eq ▸ encodesTable_tableCode Ra2372.cycles } 380775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2373.table, code := 20887252223969010945888943999872667713,
        encodes := Ra2373.tableCode_eq ▸ encodesTable_tableCode Ra2373.cycles } 380777
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2374.table, code := 20887252223969010945961001666925039681,
        encodes := Ra2374.tableCode_eq ▸ encodesTable_tableCode Ra2374.cycles } 380779
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2375.table, code := 20887252223971428797528175465835270209,
        encodes := Ra2375.tableCode_eq ▸ encodesTable_tableCode Ra2375.cycles } 380781
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2376.table, code := 20887252223971428797600233130740158529,
        encodes := Ra2376.tableCode_eq ▸ encodesTable_tableCode Ra2376.cycles } 380782
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2377.table, code := 20887252223971428797600233132887642177,
        encodes := Ra2377.tableCode_eq ▸ encodesTable_tableCode Ra2377.cycles } 380783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2378.table, code := 20887171094333014193368425292686954561,
        encodes := Ra2378.tableCode_eq ▸ encodesTable_tableCode Ra2378.cycles } 380791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2379.table, code := 20887252223969010948338902334601171009,
        encodes := Ra2379.tableCode_eq ▸ encodesTable_tableCode Ra2379.cycles } 380793
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2380.table, code := 20887252223969010948410960001653542977,
        encodes := Ra2380.tableCode_eq ▸ encodesTable_tableCode Ra2380.cycles } 380795
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2381.table, code := 20887252223971428799978133800563773505,
        encodes := Ra2381.tableCode_eq ▸ encodesTable_tableCode Ra2381.cycles } 380797
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2382.table, code := 20887252223971428800050191465468661825,
        encodes := Ra2382.tableCode_eq ▸ encodesTable_tableCode Ra2382.cycles } 380798
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2383.table, code := 20887252223971428800050191467616145473,
        encodes := Ra2383.tableCode_eq ▸ encodesTable_tableCode Ra2383.cycles } 380799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2384.table, code := 20887171096733940794597915743490412609,
        encodes := Ra2384.tableCode_eq ▸ encodesTable_tableCode Ra2384.cycles } 380867
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2385.table, code := 20887171096736358646237147209453015105,
        encodes := Ra2385.tableCode_eq ▸ encodesTable_tableCode Ra2385.cycles } 380871
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2386.table, code := 20887252226372355401279681918419603521,
        encodes := Ra2386.tableCode_eq ▸ encodesTable_tableCode Ra2386.cycles } 380875
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2387.table, code := 20887252226374773252918913384382206017,
        encodes := Ra2387.tableCode_eq ▸ encodesTable_tableCode Ra2387.cycles } 380879
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2388.table, code := 20887171096736358648687105544181518401,
        encodes := Ra2388.tableCode_eq ▸ encodesTable_tableCode Ra2388.cycles } 380887
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2389.table, code := 20887252226372355403729640253148106817,
        encodes := Ra2389.tableCode_eq ▸ encodesTable_tableCode Ra2389.cycles } 380891
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2390.table, code := 20887252226374773255368871716963225665,
        encodes := Ra2390.tableCode_eq ▸ encodesTable_tableCode Ra2390.cycles } 380894
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2391.table, code := 20887252226374773255368871719110709313,
        encodes := Ra2391.tableCode_eq ▸ encodesTable_tableCode Ra2391.cycles } 380895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2392.table, code := 20887171096816147824406921871284768833,
        encodes := Ra2392.tableCode_eq ▸ encodesTable_tableCode Ra2392.cycles } 380899
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2393.table, code := 20887171096818565676046153337247371329,
        encodes := Ra2393.tableCode_eq ▸ encodesTable_tableCode Ra2393.cycles } 380903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2394.table, code := 20887252226454562431016630379161587777,
        encodes := Ra2394.tableCode_eq ▸ encodesTable_tableCode Ra2394.cycles } 380905
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2395.table, code := 20887252226454562431088688046213959745,
        encodes := Ra2395.tableCode_eq ▸ encodesTable_tableCode Ra2395.cycles } 380907
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2396.table, code := 20887252226456980282655861845124190273,
        encodes := Ra2396.tableCode_eq ▸ encodesTable_tableCode Ra2396.cycles } 380909
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2397.table, code := 20887252226456980282727919510029078593,
        encodes := Ra2397.tableCode_eq ▸ encodesTable_tableCode Ra2397.cycles } 380910
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2398.table, code := 20887252226456980282727919512176562241,
        encodes := Ra2398.tableCode_eq ▸ encodesTable_tableCode Ra2398.cycles } 380911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2399.table, code := 20887171096818565678424054004923502657,
        encodes := Ra2399.tableCode_eq ▸ encodesTable_tableCode Ra2399.cycles } 380917
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2400.table, code := 20887171096818565678496111671975874625,
        encodes := Ra2400.tableCode_eq ▸ encodesTable_tableCode Ra2400.cycles } 380919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2401.table, code := 20887252226454562433466588713890091073,
        encodes := Ra2401.tableCode_eq ▸ encodesTable_tableCode Ra2401.cycles } 380921
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2402.table, code := 20887252226454562433538646380942463041,
        encodes := Ra2402.tableCode_eq ▸ encodesTable_tableCode Ra2402.cycles } 380923
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2403.table, code := 20887252226456980285105820179852693569,
        encodes := Ra2403.tableCode_eq ▸ encodesTable_tableCode Ra2403.cycles } 380925
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2404.table, code := 20887252226456980285177877844757581889,
        encodes := Ra2404.tableCode_eq ▸ encodesTable_tableCode Ra2404.cycles } 380926
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2405.table, code := 20887252226456980285177877846905065537,
        encodes := Ra2405.tableCode_eq ▸ encodesTable_tableCode Ra2405.cycles } 380927
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2406.table, code := 20889686112969126715396493111132950593,
        encodes := Ra2406.tableCode_eq ▸ encodesTable_tableCode Ra2406.cycles } 382767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2407.table, code := 20889686112966708866207219979898851393,
        encodes := Ra2407.tableCode_eq ▸ encodesTable_tableCode Ra2407.cycles } 382779
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2408.table, code := 20889686112969126717846451443713970241,
        encodes := Ra2408.tableCode_eq ▸ encodesTable_tableCode Ra2408.cycles } 382782
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2409.table, code := 20889686112969126717846451445861453889,
        encodes := Ra2409.tableCode_eq ▸ encodesTable_tableCode Ra2409.cycles } 382783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2410.table, code := 20892444520672807852622704278663073857,
        encodes := Ra2410.tableCode_eq ▸ encodesTable_tableCode Ra2410.cycles } 382825
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2411.table, code := 20892444520672807852694761945715445825,
        encodes := Ra2411.tableCode_eq ▸ encodesTable_tableCode Ra2411.cycles } 382827
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2412.table, code := 20892444520675225704261935744625676353,
        encodes := Ra2412.tableCode_eq ▸ encodesTable_tableCode Ra2412.cycles } 382829
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2413.table, code := 20892444520675225704333993411678048321,
        encodes := Ra2413.tableCode_eq ▸ encodesTable_tableCode Ra2413.cycles } 382831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2414.table, code := 20892444520672807855144720280443949121,
        encodes := Ra2414.tableCode_eq ▸ encodesTable_tableCode Ra2414.cycles } 382843
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2415.table, code := 20892444520675225706711894079354179649,
        encodes := Ra2415.tableCode_eq ▸ encodesTable_tableCode Ra2415.cycles } 382845
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2416.table, code := 20892444520675225706783951744259067969,
        encodes := Ra2416.tableCode_eq ▸ encodesTable_tableCode Ra2416.cycles } 382846
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2417.table, code := 20892444520675225706783951746406551617,
        encodes := Ra2417.tableCode_eq ▸ encodesTable_tableCode Ra2417.cycles } 382847
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2418.table, code := 20889686115452260348884948024459268161,
        encodes := Ra2418.tableCode_eq ▸ encodesTable_tableCode Ra2418.cycles } 382891
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2419.table, code := 20889686115454678200524179490421870657,
        encodes := Ra2419.tableCode_eq ▸ encodesTable_tableCode Ra2419.cycles } 382895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2420.table, code := 20889686115452260351334906359187771457,
        encodes := Ra2420.tableCode_eq ▸ encodesTable_tableCode Ra2420.cycles } 382907
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2421.table, code := 20889686115454678202974137823002890305,
        encodes := Ra2421.tableCode_eq ▸ encodesTable_tableCode Ra2421.cycles } 382910
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2422.table, code := 20889686115454678202974137825150373953,
        encodes := Ra2422.tableCode_eq ▸ encodesTable_tableCode Ra2422.cycles } 382911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2423.table, code := 20892363393522362582707855948985405505,
        encodes := Ra2423.tableCode_eq ▸ encodesTable_tableCode Ra2423.cycles } 382949
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2424.table, code := 20892363393522362582779913616037777473,
        encodes := Ra2424.tableCode_eq ▸ encodesTable_tableCode Ra2424.cycles } 382951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2425.table, code := 20892444523158359337750390657951993921,
        encodes := Ra2425.tableCode_eq ▸ encodesTable_tableCode Ra2425.cycles } 382953
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2426.table, code := 20892444523158359337822448325004365889,
        encodes := Ra2426.tableCode_eq ▸ encodesTable_tableCode Ra2426.cycles } 382955
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2427.table, code := 20892444523160777189389622123914596417,
        encodes := Ra2427.tableCode_eq ▸ encodesTable_tableCode Ra2427.cycles } 382957
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2428.table, code := 20892444523160777189461679788819484737,
        encodes := Ra2428.tableCode_eq ▸ encodesTable_tableCode Ra2428.cycles } 382958
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2429.table, code := 20892444523160777189461679790966968385,
        encodes := Ra2429.tableCode_eq ▸ encodesTable_tableCode Ra2429.cycles } 382959
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2430.table, code := 20892363393522362585157814283713908801,
        encodes := Ra2430.tableCode_eq ▸ encodesTable_tableCode Ra2430.cycles } 382965
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2431.table, code := 20892363393522362585229871950766280769,
        encodes := Ra2431.tableCode_eq ▸ encodesTable_tableCode Ra2431.cycles } 382967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2432.table, code := 20892444523158359340200348992680497217,
        encodes := Ra2432.tableCode_eq ▸ encodesTable_tableCode Ra2432.cycles } 382969
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2368 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2368 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2368 + i.val) 0 ≤ Data.profiles (2368 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2368 + i.val) 0 = Data.canonicalMask (2368 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2368 + i.val) < Data.canonicalMask (2368 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2368 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models037
