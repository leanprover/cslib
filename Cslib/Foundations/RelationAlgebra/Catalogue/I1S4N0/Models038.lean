/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2433
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2434
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2435
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2436
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2437
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2438
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2439
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2440
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2441
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2442
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2443
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2444
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2445
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2446
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2447
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2448
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2449
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2450
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2451
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2452
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2453
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2454
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2455
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2456
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2457
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2458
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2459
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2460
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2461
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2462
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2463
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2464
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2465
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2466
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2467
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2468
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2469
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2470
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2471
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2472
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2473
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2474
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2475
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2476
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2477
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2478
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2479
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2480
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2481
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2482
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2483
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2484
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2485
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2486
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2487
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2488
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2489
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2490
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2491
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2492
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2493
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2494
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2495
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2496

/-!
# Certified models 2433–2496 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models038

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2433.table, code := 20892444523158359340272406659732869185,
        encodes := Ra2433.tableCode_eq ▸ encodesTable_tableCode Ra2433.cycles } 382971
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2434.table, code := 20892444523160777191839580458643099713,
        encodes := Ra2434.tableCode_eq ▸ encodesTable_tableCode Ra2434.cycles } 382973
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2435.table, code := 20892444523160777191911638123547988033,
        encodes := Ra2435.tableCode_eq ▸ encodesTable_tableCode Ra2435.cycles } 382974
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2436.table, code := 20892444523160777191911638125695471681,
        encodes := Ra2436.tableCode_eq ▸ encodesTable_tableCode Ra2436.cycles } 382975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2437.table, code := 20889686113123869374942762586180161601,
        encodes := Ra2437.tableCode_eq ▸ encodesTable_tableCode Ra2437.cycles } 383806
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2438.table, code := 20889686113123869374942762588327645249,
        encodes := Ra2438.tableCode_eq ▸ encodesTable_tableCode Ra2438.cycles } 383807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2439.table, code := 20892444520829968363880262886725259329,
        encodes := Ra2439.tableCode_eq ▸ encodesTable_tableCode Ra2439.cycles } 383870
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2440.table, code := 20892444520829968363880262888872742977,
        encodes := Ra2440.tableCode_eq ▸ encodesTable_tableCode Ra2440.cycles } 383871
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2441.table, code := 20889686115607003008431217501653962817,
        encodes := Ra2441.tableCode_eq ▸ encodesTable_tableCode Ra2441.cycles } 383931
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2442.table, code := 20889686115609420860070448965469081665,
        encodes := Ra2442.tableCode_eq ▸ encodesTable_tableCode Ra2442.cycles } 383934
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2443.table, code := 20889686115609420860070448967616565313,
        encodes := Ra2443.tableCode_eq ▸ encodesTable_tableCode Ra2443.cycles } 383935
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2444.table, code := 20892363393677105242254125426180100161,
        encodes := Ra2444.tableCode_eq ▸ encodesTable_tableCode Ra2444.cycles } 383989
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2445.table, code := 20892363393677105242326183093232472129,
        encodes := Ra2445.tableCode_eq ▸ encodesTable_tableCode Ra2445.cycles } 383991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2446.table, code := 20892444523313101997368717802199060545,
        encodes := Ra2446.tableCode_eq ▸ encodesTable_tableCode Ra2446.cycles } 383995
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2447.table, code := 20892444523315519849007949266014179393,
        encodes := Ra2447.tableCode_eq ▸ encodesTable_tableCode Ra2447.cycles } 383998
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2448.table, code := 20892444523315519849007949268161663041,
        encodes := Ra2448.tableCode_eq ▸ encodesTable_tableCode Ra2448.cycles } 383999
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2449.table, code := 20889686113123869377104490272026529857,
        encodes := Ra2449.tableCode_eq ▸ encodesTable_tableCode Ra2449.cycles } 384815
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2450.table, code := 20889686113123869379554448606755033153,
        encodes := Ra2450.tableCode_eq ▸ encodesTable_tableCode Ra2450.cycles } 384831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2451.table, code := 20892444520829968365969932905519255617,
        encodes := Ra2451.tableCode_eq ▸ encodesTable_tableCode Ra2451.cycles } 384877
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2452.table, code := 20892444520829968366041990572571627585,
        encodes := Ra2452.tableCode_eq ▸ encodesTable_tableCode Ra2452.cycles } 384879
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2453.table, code := 20892444520829968368491948907300130881,
        encodes := Ra2453.tableCode_eq ▸ encodesTable_tableCode Ra2453.cycles } 384895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2454.table, code := 20889686115527213834873128856102113345,
        encodes := Ra2454.tableCode_eq ▸ encodesTable_tableCode Ra2454.cycles } 384926
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2455.table, code := 20889686115527213834873128858249596993,
        encodes := Ra2455.tableCode_eq ▸ encodesTable_tableCode Ra2455.cycles } 384927
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2456.table, code := 20889686115607003010592945185352847425,
        encodes := Ra2456.tableCode_eq ▸ encodesTable_tableCode Ra2456.cycles } 384939
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2457.table, code := 20889686115609420862232176651315449921,
        encodes := Ra2457.tableCode_eq ▸ encodesTable_tableCode Ra2457.cycles } 384943
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2458.table, code := 20889686115607003012970845853028978753,
        encodes := Ra2458.tableCode_eq ▸ encodesTable_tableCode Ra2458.cycles } 384953
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2459.table, code := 20889686115607003013042903520081350721,
        encodes := Ra2459.tableCode_eq ▸ encodesTable_tableCode Ra2459.cycles } 384955
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2460.table, code := 20889686115609420864610077318991581249,
        encodes := Ra2460.tableCode_eq ▸ encodesTable_tableCode Ra2460.cycles } 384957
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2461.table, code := 20889686115609420864682134983896469569,
        encodes := Ra2461.tableCode_eq ▸ encodesTable_tableCode Ra2461.cycles } 384958
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2462.table, code := 20889686115609420864682134986043953217,
        encodes := Ra2462.tableCode_eq ▸ encodesTable_tableCode Ra2462.cycles } 384959
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2463.table, code := 20892363393594898214678904649137000513,
        encodes := Ra2463.tableCode_eq ▸ encodesTable_tableCode Ra2463.cycles } 384967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2464.table, code := 20892444523230894969721439358103588929,
        encodes := Ra2464.tableCode_eq ▸ encodesTable_tableCode Ra2464.cycles } 384971
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2465.table, code := 20892444523233312821360670824066191425,
        encodes := Ra2465.tableCode_eq ▸ encodesTable_tableCode Ra2465.cycles } 384975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2466.table, code := 20892363393594898217128862983865503809,
        encodes := Ra2466.tableCode_eq ▸ encodesTable_tableCode Ra2466.cycles } 384983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2467.table, code := 20892444523230894972171397692832092225,
        encodes := Ra2467.tableCode_eq ▸ encodesTable_tableCode Ra2467.cycles } 384987
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2468.table, code := 20892444523233312823810629156647211073,
        encodes := Ra2468.tableCode_eq ▸ encodesTable_tableCode Ra2468.cycles } 384990
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2469.table, code := 20892444523233312823810629158794694721,
        encodes := Ra2469.tableCode_eq ▸ encodesTable_tableCode Ra2469.cycles } 384991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2470.table, code := 20892363393677105244487910776931356737,
        encodes := Ra2470.tableCode_eq ▸ encodesTable_tableCode Ra2470.cycles } 384999
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2471.table, code := 20892444523313101999458387818845573185,
        encodes := Ra2471.tableCode_eq ▸ encodesTable_tableCode Ra2471.cycles } 385001
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2472.table, code := 20892444523313101999530445485897945153,
        encodes := Ra2472.tableCode_eq ▸ encodesTable_tableCode Ra2472.cycles } 385003
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2473.table, code := 20892444523315519851097619284808175681,
        encodes := Ra2473.tableCode_eq ▸ encodesTable_tableCode Ra2473.cycles } 385005
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2474.table, code := 20892444523315519851169676949713064001,
        encodes := Ra2474.tableCode_eq ▸ encodesTable_tableCode Ra2474.cycles } 385006
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2475.table, code := 20892444523315519851169676951860547649,
        encodes := Ra2475.tableCode_eq ▸ encodesTable_tableCode Ra2475.cycles } 385007
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2476.table, code := 20892363393677105246865811444607488065,
        encodes := Ra2476.tableCode_eq ▸ encodesTable_tableCode Ra2476.cycles } 385013
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2477.table, code := 20892363393677105246937869111659860033,
        encodes := Ra2477.tableCode_eq ▸ encodesTable_tableCode Ra2477.cycles } 385015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2478.table, code := 20892444523313102001908346153574076481,
        encodes := Ra2478.tableCode_eq ▸ encodesTable_tableCode Ra2478.cycles } 385017
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2479.table, code := 20892444523313102001980403820626448449,
        encodes := Ra2479.tableCode_eq ▸ encodesTable_tableCode Ra2479.cycles } 385019
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2480.table, code := 20892444523315519853547577619536678977,
        encodes := Ra2480.tableCode_eq ▸ encodesTable_tableCode Ra2480.cycles } 385021
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2481.table, code := 20892444523315519853619635284441567297,
        encodes := Ra2481.tableCode_eq ▸ encodesTable_tableCode Ra2481.cycles } 385022
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2482.table, code := 20892444523315519853619635286589050945,
        encodes := Ra2482.tableCode_eq ▸ encodesTable_tableCode Ra2482.cycles } 385023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2483.table, code := 20887171101997604110797876891855622209,
        encodes := Ra2483.tableCode_eq ▸ encodesTable_tableCode Ra2483.cycles } 389079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2484.table, code := 20887252231633600865768353933769838657,
        encodes := Ra2484.tableCode_eq ▸ encodesTable_tableCode Ra2484.cycles } 389081
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2485.table, code := 20887252231633600865840411600822210625,
        encodes := Ra2485.tableCode_eq ▸ encodesTable_tableCode Ra2485.cycles } 389083
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2486.table, code := 20887252231636018717479643064637329473,
        encodes := Ra2486.tableCode_eq ▸ encodesTable_tableCode Ra2486.cycles } 389086
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2487.table, code := 20887252231636018717479643066784813121,
        encodes := Ra2487.tableCode_eq ▸ encodesTable_tableCode Ra2487.cycles } 389087
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2488.table, code := 20887171102079811140606883019649978433,
        encodes := Ra2488.tableCode_eq ▸ encodesTable_tableCode Ra2488.cycles } 389111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2489.table, code := 20887252231715807895577360061564194881,
        encodes := Ra2489.tableCode_eq ▸ encodesTable_tableCode Ra2489.cycles } 389113
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2490.table, code := 20887252231715807895649417728616566849,
        encodes := Ra2490.tableCode_eq ▸ encodesTable_tableCode Ra2490.cycles } 389115
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2491.table, code := 20887252231718225747288649192431685697,
        encodes := Ra2491.tableCode_eq ▸ encodesTable_tableCode Ra2491.cycles } 389118
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2492.table, code := 20887252231718225747288649194579169345,
        encodes := Ra2492.tableCode_eq ▸ encodesTable_tableCode Ra2492.cycles } 389119
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2493.table, code := 20889686120713505810995719372133371969,
        encodes := Ra2493.tableCode_eq ▸ encodesTable_tableCode Ra2493.cycles } 391083
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2494.table, code := 20889686120715923662634950838095974465,
        encodes := Ra2494.tableCode_eq ▸ encodesTable_tableCode Ra2494.cycles } 391087
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2495.table, code := 20889686120713505813445677706861875265,
        encodes := Ra2495.tableCode_eq ▸ encodesTable_tableCode Ra2495.cycles } 391099
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2496.table, code := 20889686120715923665012851505772105793,
        encodes := Ra2496.tableCode_eq ▸ encodesTable_tableCode Ra2496.cycles } 391101
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2432 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2432 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2432 + i.val) 0 ≤ Data.profiles (2432 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2432 + i.val) 0 = Data.canonicalMask (2432 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2432 + i.val) < Data.canonicalMask (2432 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2432 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models038
