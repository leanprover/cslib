/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2689
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2690
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2691
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2692
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2693
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2694
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2695
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2696
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2697
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2698
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2699
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2700
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2701
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2702
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2703
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2704
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2705
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2706
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2707
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2708
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2709
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2710
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2711
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2712
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2713
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2714
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2715
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2716
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2717
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2718
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2719
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2720
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2721
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2722
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2723
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2724
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2725
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2726
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2727
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2728
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2729
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2730
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2731
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2732
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2733
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2734
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2735
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2736
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2737
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2738
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2739
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2740
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2741
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2742
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2743
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2744
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2745
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2746
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2747
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2748
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2749
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2750
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2751
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2752

/-!
# Certified models 2689–2752 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models042

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2689.table, code := 22864867658623700641337272602074550337,
        encodes := Ra2689.tableCode_eq ▸ encodesTable_tableCode Ra2689.cycles } 613867
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2690.table, code := 22864867658626118492976504068037152833,
        encodes := Ra2690.tableCode_eq ▸ encodesTable_tableCode Ra2690.cycles } 613871
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2691.table, code := 22864786528987703888672638560784093249,
        encodes := Ra2691.tableCode_eq ▸ encodesTable_tableCode Ra2691.cycles } 613877
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2692.table, code := 22864786528987703888744696227836465217,
        encodes := Ra2692.tableCode_eq ▸ encodesTable_tableCode Ra2692.cycles } 613879
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2693.table, code := 22864867658623700643715173269750681665,
        encodes := Ra2693.tableCode_eq ▸ encodesTable_tableCode Ra2693.cycles } 613881
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2694.table, code := 22864867658623700643787230936803053633,
        encodes := Ra2694.tableCode_eq ▸ encodesTable_tableCode Ra2694.cycles } 613883
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2695.table, code := 22864867658626118495354404735713284161,
        encodes := Ra2695.tableCode_eq ▸ encodesTable_tableCode Ra2695.cycles } 613885
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2696.table, code := 22864867658626118495426462402765656129,
        encodes := Ra2696.tableCode_eq ▸ encodesTable_tableCode Ra2696.cycles } 613887
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2697.table, code := 25437731802336407621386902224247197761,
        encodes := Ra2697.tableCode_eq ▸ encodesTable_tableCode Ra2697.cycles } 614033
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2698.table, code := 25437812932057029257877674526970744897,
        encodes := Ra2698.tableCode_eq ▸ encodesTable_tableCode Ra2698.cycles } 614073
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2699.table, code := 25440571339765546098526463960530817089,
        encodes := Ra2699.tableCode_eq ▸ encodesTable_tableCode Ra2699.cycles } 614143
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2700.table, code := 25521214279514961075941699356981465153,
        encodes := Ra2700.tableCode_eq ▸ encodesTable_tableCode Ra2700.cycles } 614303
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2701.table, code := 25521214279594750251661515684084715585,
        encodes := Ra2701.tableCode_eq ▸ encodesTable_tableCode Ra2701.cycles } 614315
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2702.table, code := 25521214279597168103300747150047318081,
        encodes := Ra2702.tableCode_eq ▸ encodesTable_tableCode Ra2702.cycles } 614319
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2703.table, code := 25521214279594750254111474018813218881,
        encodes := Ra2703.tableCode_eq ▸ encodesTable_tableCode Ra2703.cycles } 614331
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2704.table, code := 25521214279597168105750705484775821377,
        encodes := Ra2704.tableCode_eq ▸ encodesTable_tableCode Ra2704.cycles } 614335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2705.table, code := 25523891557662434633917249809700622401,
        encodes := Ra2705.tableCode_eq ▸ encodesTable_tableCode Ra2705.cycles } 614371
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2706.table, code := 25523891557664852485556481275663224897,
        encodes := Ra2706.tableCode_eq ▸ encodesTable_tableCode Ra2706.cycles } 614375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2707.table, code := 25523972687303267092238247450592415809,
        encodes := Ra2707.tableCode_eq ▸ encodesTable_tableCode Ra2707.cycles } 614383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2708.table, code := 25523891557662434636295150477376753729,
        encodes := Ra2708.tableCode_eq ▸ encodesTable_tableCode Ra2708.cycles } 614385
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2709.table, code := 25523891557662434636367208144429125697,
        encodes := Ra2709.tableCode_eq ▸ encodesTable_tableCode Ra2709.cycles } 614387
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2710.table, code := 25523891557664852487934381943339356225,
        encodes := Ra2710.tableCode_eq ▸ encodesTable_tableCode Ra2710.cycles } 614389
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2711.table, code := 25523891557664852488006439610391728193,
        encodes := Ra2711.tableCode_eq ▸ encodesTable_tableCode Ra2711.cycles } 614391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2712.table, code := 25523972687303267094616148118268547137,
        encodes := Ra2712.tableCode_eq ▸ encodesTable_tableCode Ra2712.cycles } 614397
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2713.table, code := 25523972687303267094688205785320919105,
        encodes := Ra2713.tableCode_eq ▸ encodesTable_tableCode Ra2713.cycles } 614399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2714.table, code := 22859594237308202752604704008032227393,
        encodes := Ra2714.tableCode_eq ▸ encodesTable_tableCode Ra2714.cycles } 617943
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2715.table, code := 22859675366946617359286470182961418305,
        encodes := Ra2715.tableCode_eq ▸ encodesTable_tableCode Ra2715.cycles } 617951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2716.table, code := 22859594237390409782413710135826583617,
        encodes := Ra2716.tableCode_eq ▸ encodesTable_tableCode Ra2716.cycles } 617975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2717.table, code := 22859675367026406537384187177740800065,
        encodes := Ra2717.tableCode_eq ▸ encodesTable_tableCode Ra2717.cycles } 617977
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2718.table, code := 22859675367026406537456244844793172033,
        encodes := Ra2718.tableCode_eq ▸ encodesTable_tableCode Ra2718.cycles } 617979
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2719.table, code := 22859675367028824389095476310755774529,
        encodes := Ra2719.tableCode_eq ▸ encodesTable_tableCode Ra2719.cycles } 617983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2720.table, code := 25518699263499799866738761011298570305,
        encodes := Ra2720.tableCode_eq ▸ encodesTable_tableCode Ra2720.cycles } 618327
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2721.table, code := 25518780393138214473420527186227761217,
        encodes := Ra2721.tableCode_eq ▸ encodesTable_tableCode Ra2721.cycles } 618335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2722.table, code := 25518699263582006894097808804364423233,
        encodes := Ra2722.tableCode_eq ▸ encodesTable_tableCode Ra2722.cycles } 618343
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2723.table, code := 25518780393220421500779574979293614145,
        encodes := Ra2723.tableCode_eq ▸ encodesTable_tableCode Ra2723.cycles } 618351
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2724.table, code := 25518699263582006896475709472040554561,
        encodes := Ra2724.tableCode_eq ▸ encodesTable_tableCode Ra2724.cycles } 618357
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2725.table, code := 25518699263582006896547767139092926529,
        encodes := Ra2725.tableCode_eq ▸ encodesTable_tableCode Ra2725.cycles } 618359
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2726.table, code := 25518780393220421503157475646969745473,
        encodes := Ra2726.tableCode_eq ▸ encodesTable_tableCode Ra2726.cycles } 618365
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2727.table, code := 25518780393220421503229533314022117441,
        encodes := Ra2727.tableCode_eq ▸ encodesTable_tableCode Ra2727.cycles } 618367
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2728.table, code := 25518699265985351351866447390587490369,
        encodes := Ra2728.tableCode_eq ▸ encodesTable_tableCode Ra2728.cycles } 618455
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2729.table, code := 25518780395623765958548213565516681281,
        encodes := Ra2729.tableCode_eq ▸ encodesTable_tableCode Ra2729.cycles } 618463
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2730.table, code := 25518699266065140529964164385366872129,
        encodes := Ra2730.tableCode_eq ▸ encodesTable_tableCode Ra2730.cycles } 618481
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2731.table, code := 25518699266065140530036222052419244097,
        encodes := Ra2731.tableCode_eq ▸ encodesTable_tableCode Ra2731.cycles } 618483
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2732.table, code := 25518699266067558381675453518381846593,
        encodes := Ra2732.tableCode_eq ▸ encodesTable_tableCode Ra2732.cycles } 618487
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2733.table, code := 25518780395703555136645930560296063041,
        encodes := Ra2733.tableCode_eq ▸ encodesTable_tableCode Ra2733.cycles } 618489
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2734.table, code := 25518780395703555136717988227348435009,
        encodes := Ra2734.tableCode_eq ▸ encodesTable_tableCode Ra2734.cycles } 618491
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2735.table, code := 25518780395705972988357219693311037505,
        encodes := Ra2735.tableCode_eq ▸ encodesTable_tableCode Ra2735.cycles } 618495
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2736.table, code := 22864867663730203441740046788855074881,
        encodes := Ra2736.tableCode_eq ▸ encodesTable_tableCode Ra2736.cycles } 620011
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2737.table, code := 22864867663732621293379278254817677377,
        encodes := Ra2737.tableCode_eq ▸ encodesTable_tableCode Ra2737.cycles } 620015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2738.table, code := 22864867663730203444190005123583578177,
        encodes := Ra2738.tableCode_eq ▸ encodesTable_tableCode Ra2738.cycles } 620027
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2739.table, code := 22864867663732621295757178922493808705,
        encodes := Ra2739.tableCode_eq ▸ encodesTable_tableCode Ra2739.cycles } 620029
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2740.table, code := 22864867663732621295829236589546180673,
        encodes := Ra2740.tableCode_eq ▸ encodesTable_tableCode Ra2740.cycles } 620031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2741.table, code := 25521214282218119418575834957538922561,
        encodes := Ra2741.tableCode_eq ▸ encodesTable_tableCode Ra2741.cycles } 620335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2742.table, code := 25521214282218119421025793292267425857,
        encodes := Ra2742.tableCode_eq ▸ encodesTable_tableCode Ra2742.cycles } 620351
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2743.table, code := 25523891560285803800831569083154829377,
        encodes := Ra2743.tableCode_eq ▸ encodesTable_tableCode Ra2743.cycles } 620391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2744.table, code := 25523972689924218407513335258084020289,
        encodes := Ra2744.tableCode_eq ▸ encodesTable_tableCode Ra2744.cycles } 620399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2745.table, code := 25523891560285803803281527417883332673,
        encodes := Ra2745.tableCode_eq ▸ encodesTable_tableCode Ra2745.cycles } 620407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2746.table, code := 25523972689924218409891235925760151617,
        encodes := Ra2746.tableCode_eq ▸ encodesTable_tableCode Ra2746.cycles } 620413
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2747.table, code := 25523972689924218409963293592812523585,
        encodes := Ra2747.tableCode_eq ▸ encodesTable_tableCode Ra2747.cycles } 620415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2748.table, code := 25521214284701253052064289870865240129,
        encodes := Ra2748.tableCode_eq ▸ encodesTable_tableCode Ra2748.cycles } 620459
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2749.table, code := 25521214284703670903703521336827842625,
        encodes := Ra2749.tableCode_eq ▸ encodesTable_tableCode Ra2749.cycles } 620463
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2750.table, code := 25521214284701253054514248205593743425,
        encodes := Ra2750.tableCode_eq ▸ encodesTable_tableCode Ra2750.cycles } 620475
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2751.table, code := 25521214284703670906153479671556345921,
        encodes := Ra2751.tableCode_eq ▸ encodesTable_tableCode Ra2751.cycles } 620479
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2752.table, code := 25523891562768937434320023996481146945,
        encodes := Ra2752.tableCode_eq ▸ encodesTable_tableCode Ra2752.cycles } 620515
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2688 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2688 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2688 + i.val) 0 ≤ Data.profiles (2688 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2688 + i.val) 0 = Data.canonicalMask (2688 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2688 + i.val) < Data.canonicalMask (2688 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2688 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models042
