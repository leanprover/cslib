/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2625
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2626
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2627
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2628
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2629
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2630
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2631
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2632
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2633
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2634
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2635
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2636
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2637
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2638
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2639
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2640
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2641
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2642
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2643
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2644
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2645
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2646
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2647
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2648
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2649
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2650
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2651
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2652
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2653
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2654
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2655
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2656
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2657
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2658
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2659
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2660
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2661
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2662
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2663
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2664
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2665
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2666
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2667
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2668
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2669
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2670
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2671
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2672
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2673
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2674
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2675
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2676
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2677
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2678
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2679
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2680
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2681
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2682
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2683
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2684
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2685
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2686
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2687
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2688

/-!
# Certified models 2625–2688 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models041

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2625.table, code := 25342242138179238303676270047909908545,
        encodes := Ra2625.tableCode_eq ▸ encodesTable_tableCode Ra2625.cycles } 593919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2626.table, code := 22685570996086771768910033630357884993,
        encodes := Ra2626.tableCode_eq ▸ encodesTable_tableCode Ra2626.cycles } 597277
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2627.table, code := 22685570998572323254037720009646805057,
        encodes := Ra2627.tableCode_eq ▸ encodesTable_tableCode Ra2627.cycles } 597405
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2628.table, code := 25344676027249471853299463392202068033,
        encodes := Ra2628.tableCode_eq ▸ encodesTable_tableCode Ra2628.cycles } 597917
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2629.table, code := 25347434435037777872118027487593893953,
        encodes := Ra2629.tableCode_eq ▸ encodesTable_tableCode Ra2629.cycles } 598015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2630.table, code := 25342242143440483765787041395584012353,
        encodes := Ra2630.tableCode_eq ▸ encodesTable_tableCode Ra2630.cycles } 602111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2631.table, code := 22685571001275481596743913277256634433,
        encodes := Ra2631.tableCode_eq ▸ encodesTable_tableCode Ra2631.cycles } 603439
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2632.table, code := 22685571003761033081871599656545554497,
        encodes := Ra2632.tableCode_eq ▸ encodesTable_tableCode Ra2632.cycles } 603567
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2633.table, code := 25347434437658729187393115295085498433,
        encodes := Ra2633.tableCode_eq ▸ encodesTable_tableCode Ra2633.cycles } 604031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2634.table, code := 25347434440144280672520801674374418497,
        encodes := Ra2634.tableCode_eq ▸ encodesTable_tableCode Ra2634.cycles } 604159
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2635.table, code := 22685571001430224260901868772878716993,
        encodes := Ra2635.tableCode_eq ▸ encodesTable_tableCode Ra2635.cycles } 605503
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2636.table, code := 22685571003915775746029555152167637057,
        encodes := Ra2636.tableCode_eq ▸ encodesTable_tableCode Ra2636.cycles } 605631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2637.table, code := 25347434437813471849101112455979077697,
        encodes := Ra2637.tableCode_eq ▸ encodesTable_tableCode Ra2637.cycles } 606079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2638.table, code := 25347434440299023334228798835267997761,
        encodes := Ra2638.tableCode_eq ▸ encodesTable_tableCode Ra2638.cycles } 606207
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2639.table, code := 22859594229486452319306007780226502721,
        encodes := Ra2639.tableCode_eq ▸ encodesTable_tableCode Ra2639.cycles } 607585
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2640.table, code := 22859675359127284777699063088170668097,
        encodes := Ra2640.tableCode_eq ▸ encodesTable_tableCode Ra2640.cycles } 607599
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2641.table, code := 22859675359127284780076963755846799425,
        encodes := Ra2641.tableCode_eq ▸ encodesTable_tableCode Ra2641.cycles } 607613
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2642.table, code := 22859675359127284780149021422899171393,
        encodes := Ra2642.tableCode_eq ▸ encodesTable_tableCode Ra2642.cycles } 607615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2643.table, code := 22859675361610418413565418669173116993,
        encodes := Ra2643.tableCode_eq ▸ encodesTable_tableCode Ra2643.cycles } 607737
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2644.table, code := 22859675361610418413637476336225488961,
        encodes := Ra2644.tableCode_eq ▸ encodesTable_tableCode Ra2644.cycles } 607739
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2645.table, code := 22859675361612836265276707802188091457,
        encodes := Ra2645.tableCode_eq ▸ encodesTable_tableCode Ra2645.cycles } 607743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2646.table, code := 25518699260649152406145395876799189057,
        encodes := Ra2646.tableCode_eq ▸ encodesTable_tableCode Ra2646.cycles } 608241
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2647.table, code := 25518699260649152406217453543851561025,
        encodes := Ra2647.tableCode_eq ▸ encodesTable_tableCode Ra2647.cycles } 608243
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2648.table, code := 25518699260651570257856685009814163521,
        encodes := Ra2648.tableCode_eq ▸ encodesTable_tableCode Ra2648.cycles } 608247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2649.table, code := 25518780390289984864538451184743354433,
        encodes := Ra2649.tableCode_eq ▸ encodesTable_tableCode Ra2649.cycles } 608255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2650.table, code := 22859594229643612832725294074135056449,
        encodes := Ra2650.tableCode_eq ▸ encodesTable_tableCode Ra2650.cycles } 609639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2651.table, code := 22859675359282027439407060249064247361,
        encodes := Ra2651.tableCode_eq ▸ encodesTable_tableCode Ra2651.cycles } 609647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2652.table, code := 22859594229643612835175252408863559745,
        encodes := Ra2652.tableCode_eq ▸ encodesTable_tableCode Ra2652.cycles } 609655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2653.table, code := 22859675359282027441784960916740378689,
        encodes := Ra2653.tableCode_eq ▸ encodesTable_tableCode Ra2653.cycles } 609661
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2654.table, code := 22859675359282027441857018583792750657,
        encodes := Ra2654.tableCode_eq ▸ encodesTable_tableCode Ra2654.cycles } 609663
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2655.table, code := 22859594232126746466213748987461374017,
        encodes := Ra2655.tableCode_eq ▸ encodesTable_tableCode Ra2655.cycles } 609763
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2656.table, code := 22859594232129164317852980453423976513,
        encodes := Ra2656.tableCode_eq ▸ encodesTable_tableCode Ra2656.cycles } 609767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2657.table, code := 22859675361765161072895515162390564929,
        encodes := Ra2657.tableCode_eq ▸ encodesTable_tableCode Ra2657.cycles } 609771
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2658.table, code := 22859675361767578924534746628353167425,
        encodes := Ra2658.tableCode_eq ▸ encodesTable_tableCode Ra2658.cycles } 609775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2659.table, code := 22859594232129164320230881121100107841,
        encodes := Ra2659.tableCode_eq ▸ encodesTable_tableCode Ra2659.cycles } 609781
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2660.table, code := 22859594232129164320302938788152479809,
        encodes := Ra2660.tableCode_eq ▸ encodesTable_tableCode Ra2660.cycles } 609783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2661.table, code := 22859675361765161075273415830066696257,
        encodes := Ra2661.tableCode_eq ▸ encodesTable_tableCode Ra2661.cycles } 609785
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2662.table, code := 22859675361765161075345473497119068225,
        encodes := Ra2662.tableCode_eq ▸ encodesTable_tableCode Ra2662.cycles } 609787
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2663.table, code := 22859675361767578926912647296029298753,
        encodes := Ra2663.tableCode_eq ▸ encodesTable_tableCode Ra2663.cycles } 609789
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2664.table, code := 22859675361767578926984704963081670721,
        encodes := Ra2664.tableCode_eq ▸ encodesTable_tableCode Ra2664.cycles } 609791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2665.table, code := 25518699258320761431987037456690319425,
        encodes := Ra2665.tableCode_eq ▸ encodesTable_tableCode Ra2665.cycles } 610151
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2666.table, code := 25518780387959176038668803631619510337,
        encodes := Ra2666.tableCode_eq ▸ encodesTable_tableCode Ra2666.cycles } 610159
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2667.table, code := 25518699258320761434364938124366450753,
        encodes := Ra2667.tableCode_eq ▸ encodesTable_tableCode Ra2667.cycles } 610165
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2668.table, code := 25518699258320761434436995791418822721,
        encodes := Ra2668.tableCode_eq ▸ encodesTable_tableCode Ra2668.cycles } 610167
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2669.table, code := 25518780387959176041046704299295641665,
        encodes := Ra2669.tableCode_eq ▸ encodesTable_tableCode Ra2669.cycles } 610173
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2670.table, code := 25518780387959176041118761966348013633,
        encodes := Ra2670.tableCode_eq ▸ encodesTable_tableCode Ra2670.cycles } 610175
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2671.table, code := 25518699260803895065475492370016636993,
        encodes := Ra2671.tableCode_eq ▸ encodesTable_tableCode Ra2671.cycles } 610275
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2672.table, code := 25518699260806312917114723835979239489,
        encodes := Ra2672.tableCode_eq ▸ encodesTable_tableCode Ra2672.cycles } 610279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2673.table, code := 25518780390442309672157258544945827905,
        encodes := Ra2673.tableCode_eq ▸ encodesTable_tableCode Ra2673.cycles } 610283
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2674.table, code := 25518780390444727523796490010908430401,
        encodes := Ra2674.tableCode_eq ▸ encodesTable_tableCode Ra2674.cycles } 610287
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2675.table, code := 25518699260803895067853393037692768321,
        encodes := Ra2675.tableCode_eq ▸ encodesTable_tableCode Ra2675.cycles } 610289
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2676.table, code := 25518699260803895067925450704745140289,
        encodes := Ra2676.tableCode_eq ▸ encodesTable_tableCode Ra2676.cycles } 610291
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2677.table, code := 25518699260806312919492624503655370817,
        encodes := Ra2677.tableCode_eq ▸ encodesTable_tableCode Ra2677.cycles } 610293
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2678.table, code := 25518699260806312919564682170707742785,
        encodes := Ra2678.tableCode_eq ▸ encodesTable_tableCode Ra2678.cycles } 610295
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2679.table, code := 25518780390442309674535159212621959233,
        encodes := Ra2679.tableCode_eq ▸ encodesTable_tableCode Ra2679.cycles } 610297
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2680.table, code := 25518780390442309674607216879674331201,
        encodes := Ra2680.tableCode_eq ▸ encodesTable_tableCode Ra2680.cycles } 610299
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2681.table, code := 25518780390444727526174390678584561729,
        encodes := Ra2681.tableCode_eq ▸ encodesTable_tableCode Ra2681.cycles } 610301
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2682.table, code := 25518780390444727526246448345636933697,
        encodes := Ra2682.tableCode_eq ▸ encodesTable_tableCode Ra2682.cycles } 610303
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2683.table, code := 22864867656140567007848817688748232769,
        encodes := Ra2683.tableCode_eq ▸ encodesTable_tableCode Ra2683.cycles } 613743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2684.table, code := 22864867656140567010298776023476736065,
        encodes := Ra2684.tableCode_eq ▸ encodesTable_tableCode Ra2684.cycles } 613759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2685.table, code := 22864867658543911463167497940242796609,
        encodes := Ra2685.tableCode_eq ▸ encodesTable_tableCode Ra2685.cycles } 613839
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2686.table, code := 22864786528905496858935690100042108993,
        encodes := Ra2686.tableCode_eq ▸ encodesTable_tableCode Ra2686.cycles } 613847
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2687.table, code := 22864867658543911465617456274971299905,
        encodes := Ra2687.tableCode_eq ▸ encodesTable_tableCode Ra2687.cycles } 613855
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2688.table, code := 22864786528987703886294737893107961921,
        encodes := Ra2688.tableCode_eq ▸ encodesTable_tableCode Ra2688.cycles } 613863
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2624 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2624 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2624 + i.val) 0 ≤ Data.profiles (2624 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2624 + i.val) 0 = Data.canonicalMask (2624 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2624 + i.val) < Data.canonicalMask (2624 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2624 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models041
