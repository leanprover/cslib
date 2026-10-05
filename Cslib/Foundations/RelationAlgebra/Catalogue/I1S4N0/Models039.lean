/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2497
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2498
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2499
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2500
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2501
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2502
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2503
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2504
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2505
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2506
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2507
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2508
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2509
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2510
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2511
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2512
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2513
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2514
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2515
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2516
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2517
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2518
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2519
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2520
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2521
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2522
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2523
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2524
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2525
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2526
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2527
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2528
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2529
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2530
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2531
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2532
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2533
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2534
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2535
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2536
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2537
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2538
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2539
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2540
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2541
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2542
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2543
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2544
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2545
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2546
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2547
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2548
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2549
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2550
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2551
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2552
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2553
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2554
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2555
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2556
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2557
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2558
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2559
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2560

/-!
# Certified models 2497–2560 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models039

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2497.table, code := 20889686120715923665084909170676994113,
        encodes := Ra2497.tableCode_eq ▸ encodesTable_tableCode Ra2497.cycles } 391102
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2498.table, code := 20889686120715923665084909172824477761,
        encodes := Ra2498.tableCode_eq ▸ encodesTable_tableCode Ra2498.cycles } 391103
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2499.table, code := 20892444528337397770124213544884113473,
        encodes := Ra2499.tableCode_eq ▸ encodesTable_tableCode Ra2499.cycles } 391115
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2500.table, code := 20892444528339815621763445010846715969,
        encodes := Ra2500.tableCode_eq ▸ encodesTable_tableCode Ra2500.cycles } 391119
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2501.table, code := 20892444528337397772574171879612616769,
        encodes := Ra2501.tableCode_eq ▸ encodesTable_tableCode Ra2501.cycles } 391131
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2502.table, code := 20892444528339815624141345678522847297,
        encodes := Ra2502.tableCode_eq ▸ encodesTable_tableCode Ra2502.cycles } 391133
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2503.table, code := 20892444528339815624213403343427735617,
        encodes := Ra2503.tableCode_eq ▸ encodesTable_tableCode Ra2503.cycles } 391134
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2504.table, code := 20892444528339815624213403345575219265,
        encodes := Ra2504.tableCode_eq ▸ encodesTable_tableCode Ra2504.cycles } 391135
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2505.table, code := 20892444528419604799861162005626097729,
        encodes := Ra2505.tableCode_eq ▸ encodesTable_tableCode Ra2505.cycles } 391145
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2506.table, code := 20892444528419604799933219672678469697,
        encodes := Ra2506.tableCode_eq ▸ encodesTable_tableCode Ra2506.cycles } 391147
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2507.table, code := 20892444528422022651500393471588700225,
        encodes := Ra2507.tableCode_eq ▸ encodesTable_tableCode Ra2507.cycles } 391149
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2508.table, code := 20892444528422022651572451138641072193,
        encodes := Ra2508.tableCode_eq ▸ encodesTable_tableCode Ra2508.cycles } 391151
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2509.table, code := 20892444528419604802383178007406972993,
        encodes := Ra2509.tableCode_eq ▸ encodesTable_tableCode Ra2509.cycles } 391163
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2510.table, code := 20892444528422022653950351806317203521,
        encodes := Ra2510.tableCode_eq ▸ encodesTable_tableCode Ra2510.cycles } 391165
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2511.table, code := 20892444528422022654022409471222091841,
        encodes := Ra2511.tableCode_eq ▸ encodesTable_tableCode Ra2511.cycles } 391166
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2512.table, code := 20892444528422022654022409473369575489,
        encodes := Ra2512.tableCode_eq ▸ encodesTable_tableCode Ra2512.cycles } 391167
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2513.table, code := 20889686120788459292372214185348829249,
        encodes := Ra2513.tableCode_eq ▸ encodesTable_tableCode Ra2513.cycles } 392094
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2514.table, code := 20889686120788459292372214187496312897,
        encodes := Ra2514.tableCode_eq ▸ encodesTable_tableCode Ra2514.cycles } 392095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2515.table, code := 20889686120870666322181220313143185473,
        encodes := Ra2515.tableCode_eq ▸ encodesTable_tableCode Ra2515.cycles } 392126
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2516.table, code := 20889686120870666322181220315290669121,
        encodes := Ra2516.tableCode_eq ▸ encodesTable_tableCode Ra2516.cycles } 392127
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2517.table, code := 20892444528494558281309714485893926977,
        encodes := Ra2517.tableCode_eq ▸ encodesTable_tableCode Ra2517.cycles } 392158
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2518.table, code := 20892444528494558281309714488041410625,
        encodes := Ra2518.tableCode_eq ▸ encodesTable_tableCode Ra2518.cycles } 392159
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2519.table, code := 20892444528576765311046662948783394881,
        encodes := Ra2519.tableCode_eq ▸ encodesTable_tableCode Ra2519.cycles } 392189
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2520.table, code := 20892444528576765311118720613688283201,
        encodes := Ra2520.tableCode_eq ▸ encodesTable_tableCode Ra2520.cycles } 392190
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2521.table, code := 20892444528576765311118720615835766849,
        encodes := Ra2521.tableCode_eq ▸ encodesTable_tableCode Ra2521.cycles } 392191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2522.table, code := 20889686120788459296983900205923700801,
        encodes := Ra2522.tableCode_eq ▸ encodesTable_tableCode Ra2522.cycles } 393119
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2523.table, code := 20889686120870666324342947998989553729,
        encodes := Ra2523.tableCode_eq ▸ encodesTable_tableCode Ra2523.cycles } 393135
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2524.table, code := 20889686120870666326792906333718057025,
        encodes := Ra2524.tableCode_eq ▸ encodesTable_tableCode Ra2524.cycles } 393151
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2525.table, code := 20892444528494558283471442171740295233,
        encodes := Ra2525.tableCode_eq ▸ encodesTable_tableCode Ra2525.cycles } 393167
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2526.table, code := 20892444528494558285921400506468798529,
        encodes := Ra2526.tableCode_eq ▸ encodesTable_tableCode Ra2526.cycles } 393183
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2527.table, code := 20892444528576765313208390632482279489,
        encodes := Ra2527.tableCode_eq ▸ encodesTable_tableCode Ra2527.cycles } 393197
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2528.table, code := 20892444528576765313280448299534651457,
        encodes := Ra2528.tableCode_eq ▸ encodesTable_tableCode Ra2528.cycles } 393199
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2529.table, code := 20892444528576765315730406634263154753,
        encodes := Ra2529.tableCode_eq ▸ encodesTable_tableCode Ra2529.cycles } 393215
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2530.table, code := 20962053846747648413206638401270583361,
        encodes := Ra2530.tableCode_eq ▸ encodesTable_tableCode Ra2530.cycles } 440990
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2531.table, code := 20962053846747648413206638403418067009,
        encodes := Ra2531.tableCode_eq ▸ encodesTable_tableCode Ra2531.cycles } 440991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2532.table, code := 20962053846829855443015644529064939585,
        encodes := Ra2532.tableCode_eq ▸ encodesTable_tableCode Ra2532.cycles } 441022
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2533.table, code := 20962053846829855443015644531212423233,
        encodes := Ra2533.tableCode_eq ▸ encodesTable_tableCode Ra2533.cycles } 441023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2534.table, code := 20964812254535954431953144829610037313,
        encodes := Ra2534.tableCode_eq ▸ encodesTable_tableCode Ra2534.cycles } 441086
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2535.table, code := 20964812254535954431953144831757520961,
        encodes := Ra2535.tableCode_eq ▸ encodesTable_tableCode Ra2535.cycles } 441087
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2536.table, code := 21048213602073675428114886654400139329,
        encodes := Ra2536.tableCode_eq ▸ encodesTable_tableCode Ra2536.cycles } 441342
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2537.table, code := 21048213602073675428114886656547622977,
        encodes := Ra2537.tableCode_eq ▸ encodesTable_tableCode Ra2537.cycles } 441343
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2538.table, code := 20962053846747648417818324421845454913,
        encodes := Ra2538.tableCode_eq ▸ encodesTable_tableCode Ra2538.cycles } 442015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2539.table, code := 20962053846829855447627330549639811137,
        encodes := Ra2539.tableCode_eq ▸ encodesTable_tableCode Ra2539.cycles } 442047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2540.table, code := 20964812254535954434042814848404033601,
        encodes := Ra2540.tableCode_eq ▸ encodesTable_tableCode Ra2540.cycles } 442093
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2541.table, code := 20964812254535954434114872515456405569,
        encodes := Ra2541.tableCode_eq ▸ encodesTable_tableCode Ra2541.cycles } 442095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2542.table, code := 20964812254535954436564830850184908865,
        encodes := Ra2542.tableCode_eq ▸ encodesTable_tableCode Ra2542.cycles } 442111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2543.table, code := 21045455194285369413980066244488073281,
        encodes := Ra2543.tableCode_eq ▸ encodesTable_tableCode Ra2543.cycles } 442270
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2544.table, code := 21045455194285369413980066246635556929,
        encodes := Ra2544.tableCode_eq ▸ encodesTable_tableCode Ra2544.cycles } 442271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2545.table, code := 21045455194367576443717014707377541185,
        encodes := Ra2545.tableCode_eq ▸ encodesTable_tableCode Ra2545.cycles } 442301
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2546.table, code := 21045455194367576443789072372282429505,
        encodes := Ra2546.tableCode_eq ▸ encodesTable_tableCode Ra2546.cycles } 442302
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2547.table, code := 21045455194367576443789072374429913153,
        encodes := Ra2547.tableCode_eq ▸ encodesTable_tableCode Ra2547.cycles } 442303
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2548.table, code := 21048213602073675430204556673194135617,
        encodes := Ra2548.tableCode_eq ▸ encodesTable_tableCode Ra2548.cycles } 442349
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2549.table, code := 21048213602073675430276614340246507585,
        encodes := Ra2549.tableCode_eq ▸ encodesTable_tableCode Ra2549.cycles } 442351
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2550.table, code := 21048213602073675432654515007922638913,
        encodes := Ra2550.tableCode_eq ▸ encodesTable_tableCode Ra2550.cycles } 442365
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2551.table, code := 21048213602073675432726572672827527233,
        encodes := Ra2551.tableCode_eq ▸ encodesTable_tableCode Ra2551.cycles } 442366
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2552.table, code := 21048213602073675432726572674975010881,
        encodes := Ra2552.tableCode_eq ▸ encodesTable_tableCode Ra2552.cycles } 442367
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2553.table, code := 21224751854339164650685064952127164481,
        encodes := Ra2553.tableCode_eq ▸ encodesTable_tableCode Ra2553.cycles } 457726
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2554.table, code := 21224751854339164650685064954274648129,
        encodes := Ra2554.tableCode_eq ▸ encodesTable_tableCode Ra2554.cycles } 457727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2555.table, code := 21221993446550858636550244544362582081,
        encodes := Ra2555.tableCode_eq ▸ encodesTable_tableCode Ra2555.cycles } 458655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2556.table, code := 21221993446633065663909292337428435009,
        encodes := Ra2556.tableCode_eq ▸ encodesTable_tableCode Ra2556.cycles } 458671
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2557.table, code := 21221993446633065666359250672156938305,
        encodes := Ra2557.tableCode_eq ▸ encodesTable_tableCode Ra2557.cycles } 458687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2558.table, code := 21224751854339164652774734970921160769,
        encodes := Ra2558.tableCode_eq ▸ encodesTable_tableCode Ra2558.cycles } 458733
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2559.table, code := 21224751854339164652846792637973532737,
        encodes := Ra2559.tableCode_eq ▸ encodesTable_tableCode Ra2559.cycles } 458735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2560.table, code := 21224751854339164655296750972702036033,
        encodes := Ra2560.tableCode_eq ▸ encodesTable_tableCode Ra2560.cycles } 458751
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2496 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2496 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2496 + i.val) 0 ≤ Data.profiles (2496 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2496 + i.val) 0 = Data.canonicalMask (2496 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2496 + i.val) < Data.canonicalMask (2496 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2496 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models039
