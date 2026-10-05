/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2561
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2562
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2563
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2564
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2565
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2566
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2567
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2568
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2569
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2570
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2571
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2572
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2573
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2574
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2575
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2576
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2577
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2578
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2579
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2580
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2581
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2582
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2583
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2584
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2585
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2586
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2587
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2588
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2589
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2590
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2591
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2592
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2593
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2594
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2595
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2596
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2597
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2598
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2599
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2600
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2601
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2602
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2603
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2604
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2605
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2606
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2607
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2608
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2609
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2610
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2611
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2612
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2613
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2614
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2615
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2616
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2617
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2618
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2619
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2620
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2621
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2622
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2623
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2624

/-!
# Certified models 2561–2624 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models040

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2561.table, code := 21048213604075656135613201651582898241,
        encodes := Ra2561.tableCode_eq ▸ encodesTable_tableCode Ra2561.cycles } 497519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2562.table, code := 21048213604075656138063159986311401537,
        encodes := Ra2562.tableCode_eq ▸ encodesTable_tableCode Ra2562.cycles } 497535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2563.table, code := 21048213606561207623190846365600321601,
        encodes := Ra2563.tableCode_eq ▸ encodesTable_tableCode Ra2563.cycles } 497663
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2564.table, code := 21045455196521881959122367713644908609,
        encodes := Ra2564.tableCode_eq ▸ encodesTable_tableCode Ra2564.cycles } 499513
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2565.table, code := 21045455196521881959194425380697280577,
        encodes := Ra2565.tableCode_eq ▸ encodesTable_tableCode Ra2565.cycles } 499515
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2566.table, code := 21045455196524299810761599179607511105,
        encodes := Ra2566.tableCode_eq ▸ encodesTable_tableCode Ra2566.cycles } 499517
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2567.table, code := 21045455196524299810833656846659883073,
        encodes := Ra2567.tableCode_eq ▸ encodesTable_tableCode Ra2567.cycles } 499519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2568.table, code := 21048213604227980945681967346513875009,
        encodes := Ra2568.tableCode_eq ▸ encodesTable_tableCode Ra2568.cycles } 499563
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2569.table, code := 21048213604230398797321198812476477505,
        encodes := Ra2569.tableCode_eq ▸ encodesTable_tableCode Ra2569.cycles } 499567
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2570.table, code := 21048213604227980948059868014190006337,
        encodes := Ra2570.tableCode_eq ▸ encodesTable_tableCode Ra2570.cycles } 499577
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2571.table, code := 21048213604227980948131925681242378305,
        encodes := Ra2571.tableCode_eq ▸ encodesTable_tableCode Ra2571.cycles } 499579
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2572.table, code := 21048213604230398799699099480152608833,
        encodes := Ra2572.tableCode_eq ▸ encodesTable_tableCode Ra2572.cycles } 499581
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2573.table, code := 21048213604230398799771157147204980801,
        encodes := Ra2573.tableCode_eq ▸ encodesTable_tableCode Ra2573.cycles } 499583
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2574.table, code := 21045455199007433444322111759986200641,
        encodes := Ra2574.tableCode_eq ▸ encodesTable_tableCode Ra2574.cycles } 499643
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2575.table, code := 21045455199009851295889285558896431169,
        encodes := Ra2575.tableCode_eq ▸ encodesTable_tableCode Ra2575.cycles } 499645
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2576.table, code := 21045455199009851295961343225948803137,
        encodes := Ra2576.tableCode_eq ▸ encodesTable_tableCode Ra2576.cycles } 499647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2577.table, code := 21048213606713532430809653725802795073,
        encodes := Ra2577.tableCode_eq ▸ encodesTable_tableCode Ra2577.cycles } 499691
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2578.table, code := 21048213606715950282448885191765397569,
        encodes := Ra2578.tableCode_eq ▸ encodesTable_tableCode Ra2578.cycles } 499695
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2579.table, code := 21048213606713532433187554393478926401,
        encodes := Ra2579.tableCode_eq ▸ encodesTable_tableCode Ra2579.cycles } 499705
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2580.table, code := 21048213606713532433259612060531298369,
        encodes := Ra2580.tableCode_eq ▸ encodesTable_tableCode Ra2580.cycles } 499707
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2581.table, code := 21048213606715950284826785859441528897,
        encodes := Ra2581.tableCode_eq ▸ encodesTable_tableCode Ra2581.cycles } 499709
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2582.table, code := 21048213606715950284898843526493900865,
        encodes := Ra2582.tableCode_eq ▸ encodesTable_tableCode Ra2582.cycles } 499711
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2583.table, code := 20962053856651168732101366621038448705,
        encodes := Ra2583.tableCode_eq ▸ encodesTable_tableCode Ra2583.cycles } 507551
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2584.table, code := 20962053856733375761910372748832804929,
        encodes := Ra2584.tableCode_eq ▸ encodesTable_tableCode Ra2584.cycles } 507583
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2585.table, code := 20964812264357267721038866921583546433,
        encodes := Ra2585.tableCode_eq ▸ encodesTable_tableCode Ra2585.cycles } 507615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2586.table, code := 20964812264439474748325857047597027393,
        encodes := Ra2586.tableCode_eq ▸ encodesTable_tableCode Ra2586.cycles } 507629
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2587.table, code := 20964812264439474748397914714649399361,
        encodes := Ra2587.tableCode_eq ▸ encodesTable_tableCode Ra2587.cycles } 507631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2588.table, code := 20964812264439474750847873049377902657,
        encodes := Ra2588.tableCode_eq ▸ encodesTable_tableCode Ra2588.cycles } 507647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2589.table, code := 21048213609489226407720681027135606849,
        encodes := Ra2589.tableCode_eq ▸ encodesTable_tableCode Ra2589.cycles } 507753
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2590.table, code := 21048213609489226407792738694187978817,
        encodes := Ra2590.tableCode_eq ▸ encodesTable_tableCode Ra2590.cycles } 507755
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2591.table, code := 21048213609491644259431970160150581313,
        encodes := Ra2591.tableCode_eq ▸ encodesTable_tableCode Ra2591.cycles } 507759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2592.table, code := 21048213609489226410170639361864110145,
        encodes := Ra2592.tableCode_eq ▸ encodesTable_tableCode Ra2592.cycles } 507769
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2593.table, code := 21048213609489226410242697028916482113,
        encodes := Ra2593.tableCode_eq ▸ encodesTable_tableCode Ra2593.cycles } 507771
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2594.table, code := 21048213609491644261809870827826712641,
        encodes := Ra2594.tableCode_eq ▸ encodesTable_tableCode Ra2594.cycles } 507773
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2595.table, code := 21048213609491644261881928494879084609,
        encodes := Ra2595.tableCode_eq ▸ encodesTable_tableCode Ra2595.cycles } 507775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2596.table, code := 21048213611892570865561377280411045953,
        encodes := Ra2596.tableCode_eq ▸ encodesTable_tableCode Ra2596.cycles } 507867
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2597.table, code := 21048213611894988717200608746373648449,
        encodes := Ra2597.tableCode_eq ▸ encodesTable_tableCode Ra2597.cycles } 507871
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2598.table, code := 21048213611974777895298325741153030209,
        encodes := Ra2598.tableCode_eq ▸ encodesTable_tableCode Ra2598.cycles } 507897
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2599.table, code := 21048213611974777895370383408205402177,
        encodes := Ra2599.tableCode_eq ▸ encodesTable_tableCode Ra2599.cycles } 507899
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2600.table, code := 21048213611977195747009614874168004673,
        encodes := Ra2600.tableCode_eq ▸ encodesTable_tableCode Ra2600.cycles } 507903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2601.table, code := 21224751856338727506472090816294948929,
        encodes := Ra2601.tableCode_eq ▸ encodesTable_tableCode Ra2601.cycles } 513897
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2602.table, code := 21224751856338727506544148483347320897,
        encodes := Ra2602.tableCode_eq ▸ encodesTable_tableCode Ra2602.cycles } 513899
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2603.table, code := 21224751856341145358183379949309923393,
        encodes := Ra2603.tableCode_eq ▸ encodesTable_tableCode Ra2603.cycles } 513903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2604.table, code := 21224751856338727508994106818075824193,
        encodes := Ra2604.tableCode_eq ▸ encodesTable_tableCode Ra2604.cycles } 513915
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2605.table, code := 21224751856341145360561280616986054721,
        encodes := Ra2605.tableCode_eq ▸ encodesTable_tableCode Ra2605.cycles } 513917
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2606.table, code := 21224751856341145360633338284038426689,
        encodes := Ra2606.tableCode_eq ▸ encodesTable_tableCode Ra2606.cycles } 513919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2607.table, code := 21224751858824278994049735530312372289,
        encodes := Ra2607.tableCode_eq ▸ encodesTable_tableCode Ra2607.cycles } 514041
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2608.table, code := 21224751858824278994121793197364744257,
        encodes := Ra2608.tableCode_eq ▸ encodesTable_tableCode Ra2608.cycles } 514043
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2609.table, code := 21224751858826696845761024663327346753,
        encodes := Ra2609.tableCode_eq ▸ encodesTable_tableCode Ra2609.cycles } 514047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2610.table, code := 21224751856413680990082370982409146433,
        encodes := Ra2610.tableCode_eq ▸ encodesTable_tableCode Ra2610.cycles } 515919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2611.table, code := 21224751856413680992532329317137649729,
        encodes := Ra2611.tableCode_eq ▸ encodesTable_tableCode Ra2611.cycles } 515935
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2612.table, code := 21224751856495888019891377110203502657,
        encodes := Ra2612.tableCode_eq ▸ encodesTable_tableCode Ra2612.cycles } 515951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2613.table, code := 21224751856495888022341335444932005953,
        encodes := Ra2613.tableCode_eq ▸ encodesTable_tableCode Ra2613.cycles } 515967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2614.table, code := 21224751858896814623570825895735464001,
        encodes := Ra2614.tableCode_eq ▸ encodesTable_tableCode Ra2614.cycles } 516043
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2615.table, code := 21224751858899232475210057361698066497,
        encodes := Ra2615.tableCode_eq ▸ encodesTable_tableCode Ra2615.cycles } 516047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2616.table, code := 21224751858899232477587958029374197825,
        encodes := Ra2616.tableCode_eq ▸ encodesTable_tableCode Ra2616.cycles } 516061
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2617.table, code := 21224751858899232477660015696426569793,
        encodes := Ra2617.tableCode_eq ▸ encodesTable_tableCode Ra2617.cycles } 516063
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2618.table, code := 21224751858979021653379832023529820225,
        encodes := Ra2618.tableCode_eq ▸ encodesTable_tableCode Ra2618.cycles } 516075
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2619.table, code := 21224751858981439505019063489492422721,
        encodes := Ra2619.tableCode_eq ▸ encodesTable_tableCode Ra2619.cycles } 516079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2620.table, code := 21224751858981439507396964157168554049,
        encodes := Ra2620.tableCode_eq ▸ encodesTable_tableCode Ra2620.cycles } 516093
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2621.table, code := 21224751858981439507469021824220926017,
        encodes := Ra2621.tableCode_eq ▸ encodesTable_tableCode Ra2621.cycles } 516095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2622.table, code := 21224751864160477939770787044100673601,
        encodes := Ra2622.tableCode_eq ▸ encodesTable_tableCode Ra2622.cycles } 524255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2623.table, code := 21224751864242684969579793171895029825,
        encodes := Ra2623.tableCode_eq ▸ encodesTable_tableCode Ra2623.cycles } 524287
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2624.table, code := 25342242138024495641968272887016329281,
        encodes := Ra2624.tableCode_eq ▸ encodesTable_tableCode Ra2624.cycles } 591871
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2560 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2560 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2560 + i.val) 0 ≤ Data.profiles (2560 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2560 + i.val) 0 = Data.canonicalMask (2560 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2560 + i.val) < Data.canonicalMask (2560 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2560 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models040
