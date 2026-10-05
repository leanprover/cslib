/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2753
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2754
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2755
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2756
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2757
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2758
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2759
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2760
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2761
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2762
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2763
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2764
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2765
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2766
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2767
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2768
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2769
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2770
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2771
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2772
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2773
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2774
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2775
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2776
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2777
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2778
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2779
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2780
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2781
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2782
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2783
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2784
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2785
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2786
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2787
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2788
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2789
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2790
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2791
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2792
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2793
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2794
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2795
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2796
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2797
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2798
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2799
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2800
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2801
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2802
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2803
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2804
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2805
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2806
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2807
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2808
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2809
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2810
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2811
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2812
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2813
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2814
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2815
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2816

/-!
# Certified models 2753–2816 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models043

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2753.table, code := 25523891562771355285959255462443749441,
        encodes := Ra2753.tableCode_eq ▸ encodesTable_tableCode Ra2753.cycles } 620519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2754.table, code := 25523972692407352041001790171410337857,
        encodes := Ra2754.tableCode_eq ▸ encodesTable_tableCode Ra2754.cycles } 620523
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2755.table, code := 25523972692409769892641021637372940353,
        encodes := Ra2755.tableCode_eq ▸ encodesTable_tableCode Ra2755.cycles } 620527
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2756.table, code := 25523891562768937436697924664157278273,
        encodes := Ra2756.tableCode_eq ▸ encodesTable_tableCode Ra2756.cycles } 620529
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2757.table, code := 25523891562768937436769982331209650241,
        encodes := Ra2757.tableCode_eq ▸ encodesTable_tableCode Ra2757.cycles } 620531
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2758.table, code := 25523891562771355288337156130119880769,
        encodes := Ra2758.tableCode_eq ▸ encodesTable_tableCode Ra2758.cycles } 620533
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2759.table, code := 25523891562771355288409213797172252737,
        encodes := Ra2759.tableCode_eq ▸ encodesTable_tableCode Ra2759.cycles } 620535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2760.table, code := 25523972692407352043379690839086469185,
        encodes := Ra2760.tableCode_eq ▸ encodesTable_tableCode Ra2760.cycles } 620537
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2761.table, code := 25523972692407352043451748506138841153,
        encodes := Ra2761.tableCode_eq ▸ encodesTable_tableCode Ra2761.cycles } 620539
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2762.table, code := 25523972692409769895018922305049071681,
        encodes := Ra2762.tableCode_eq ▸ encodesTable_tableCode Ra2762.cycles } 620541
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2763.table, code := 25523972692409769895090979972101443649,
        encodes := Ra2763.tableCode_eq ▸ encodesTable_tableCode Ra2763.cycles } 620543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2764.table, code := 22864867663805156925278269287916900417,
        encodes := Ra2764.tableCode_eq ▸ encodesTable_tableCode Ra2764.cycles } 622031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2765.table, code := 22864867663805156927728227622645403713,
        encodes := Ra2765.tableCode_eq ▸ encodesTable_tableCode Ra2765.cycles } 622047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2766.table, code := 22864867663887363955087275415711256641,
        encodes := Ra2766.tableCode_eq ▸ encodesTable_tableCode Ra2766.cycles } 622063
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2767.table, code := 22864867663887363957537233750439759937,
        encodes := Ra2767.tableCode_eq ▸ encodesTable_tableCode Ra2767.cycles } 622079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2768.table, code := 25437731807597653083497673571921301569,
        encodes := Ra2768.tableCode_eq ▸ encodesTable_tableCode Ra2768.cycles } 622225
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2769.table, code := 25437812937318274719988445874644848705,
        encodes := Ra2769.tableCode_eq ▸ encodesTable_tableCode Ra2769.cycles } 622265
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2770.table, code := 25440490215388376953955469133275729985,
        encodes := Ra2770.tableCode_eq ▸ encodesTable_tableCode Ra2770.cycles } 622327
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2771.table, code := 25440571345026791560637235308204920897,
        encodes := Ra2771.tableCode_eq ▸ encodesTable_tableCode Ra2771.cycles } 622335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2772.table, code := 25521214282372862080283832118432501825,
        encodes := Ra2772.tableCode_eq ▸ encodesTable_tableCode Ra2772.cycles } 622383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2773.table, code := 25521214282372862082733790453161005121,
        encodes := Ra2773.tableCode_eq ▸ encodesTable_tableCode Ra2773.cycles } 622399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2774.table, code := 25523972690078961069221332418977599553,
        encodes := Ra2774.tableCode_eq ▸ encodesTable_tableCode Ra2774.cycles } 622447
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2775.table, code := 25523972690078961071671290753706102849,
        encodes := Ra2775.tableCode_eq ▸ encodesTable_tableCode Ra2775.cycles } 622463
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2776.table, code := 25521214284776206538052470704655568961,
        encodes := Ra2776.tableCode_eq ▸ encodesTable_tableCode Ra2776.cycles } 622495
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2777.table, code := 25521214284855995713772287031758819393,
        encodes := Ra2777.tableCode_eq ▸ encodesTable_tableCode Ra2777.cycles } 622507
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2778.table, code := 25521214284858413565411518497721421889,
        encodes := Ra2778.tableCode_eq ▸ encodesTable_tableCode Ra2778.cycles } 622511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2779.table, code := 25521214284855995716222245366487322689,
        encodes := Ra2779.tableCode_eq ▸ encodesTable_tableCode Ra2779.cycles } 622523
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2780.table, code := 25521214284858413567861476832449925185,
        encodes := Ra2780.tableCode_eq ▸ encodesTable_tableCode Ra2780.cycles } 622527
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2781.table, code := 25523891562843890917858246495542972481,
        encodes := Ra2781.tableCode_eq ▸ encodesTable_tableCode Ra2781.cycles } 622535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2782.table, code := 25523972692482305524540012670472163393,
        encodes := Ra2782.tableCode_eq ▸ encodesTable_tableCode Ra2782.cycles } 622543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2783.table, code := 25523891562843890920236147163219103809,
        encodes := Ra2783.tableCode_eq ▸ encodesTable_tableCode Ra2783.cycles } 622549
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2784.table, code := 25523891562843890920308204830271475777,
        encodes := Ra2784.tableCode_eq ▸ encodesTable_tableCode Ra2784.cycles } 622551
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2785.table, code := 25523972692482305526917913338148294721,
        encodes := Ra2785.tableCode_eq ▸ encodesTable_tableCode Ra2785.cycles } 622557
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2786.table, code := 25523972692482305526989971005200666689,
        encodes := Ra2786.tableCode_eq ▸ encodesTable_tableCode Ra2786.cycles } 622559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2787.table, code := 25523891562923680096028021157374726209,
        encodes := Ra2787.tableCode_eq ▸ encodesTable_tableCode Ra2787.cycles } 622563
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2788.table, code := 25523891562926097947667252623337328705,
        encodes := Ra2788.tableCode_eq ▸ encodesTable_tableCode Ra2788.cycles } 622567
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2789.table, code := 25523972692562094702709787332303917121,
        encodes := Ra2789.tableCode_eq ▸ encodesTable_tableCode Ra2789.cycles } 622571
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2790.table, code := 25523972692564512554349018798266519617,
        encodes := Ra2790.tableCode_eq ▸ encodesTable_tableCode Ra2790.cycles } 622575
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2791.table, code := 25523891562923680098405921825050857537,
        encodes := Ra2791.tableCode_eq ▸ encodesTable_tableCode Ra2791.cycles } 622577
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2792.table, code := 25523891562923680098477979492103229505,
        encodes := Ra2792.tableCode_eq ▸ encodesTable_tableCode Ra2792.cycles } 622579
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2793.table, code := 25523891562926097950045153291013460033,
        encodes := Ra2793.tableCode_eq ▸ encodesTable_tableCode Ra2793.cycles } 622581
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2794.table, code := 25523891562926097950117210958065832001,
        encodes := Ra2794.tableCode_eq ▸ encodesTable_tableCode Ra2794.cycles } 622583
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2795.table, code := 25523972692562094705087687999980048449,
        encodes := Ra2795.tableCode_eq ▸ encodesTable_tableCode Ra2795.cycles } 622585
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2796.table, code := 25523972692562094705159745667032420417,
        encodes := Ra2796.tableCode_eq ▸ encodesTable_tableCode Ra2796.cycles } 622587
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2797.table, code := 25523972692564512556726919465942650945,
        encodes := Ra2797.tableCode_eq ▸ encodesTable_tableCode Ra2797.cycles } 622589
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2798.table, code := 25523972692564512556798977132995022913,
        encodes := Ra2798.tableCode_eq ▸ encodesTable_tableCode Ra2798.cycles } 622591
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2799.table, code := 30677164906071256774477861176641589313,
        encodes := Ra2799.tableCode_eq ▸ encodesTable_tableCode Ra2799.cycles } 632719
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2800.table, code := 30679923313859562795674325939709546561,
        encodes := Ra2800.tableCode_eq ▸ encodesTable_tableCode Ra2800.cycles } 632831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2801.table, code := 30679923314014305457382323100603125825,
        encodes := Ra2801.tableCode_eq ▸ encodesTable_tableCode Ra2801.cycles } 634879
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2802.table, code := 30685115610872845025824080540287111233,
        encodes := Ra2802.tableCode_eq ▸ encodesTable_tableCode Ra2802.cycles } 638975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2803.table, code := 30856380436484219557473548261816275009,
        encodes := Ra2803.tableCode_eq ▸ encodesTable_tableCode Ra2803.cycles } 649187
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2804.table, code := 30856380436486637409112779727778877505,
        encodes := Ra2804.tableCode_eq ▸ encodesTable_tableCode Ra2804.cycles } 649191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2805.table, code := 30856461566125052015794545902708068417,
        encodes := Ra2805.tableCode_eq ▸ encodesTable_tableCode Ra2805.cycles } 649199
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2806.table, code := 30856380436484219559923506596544778305,
        encodes := Ra2806.tableCode_eq ▸ encodesTable_tableCode Ra2806.cycles } 649203
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2807.table, code := 30856380436486637411490680395455008833,
        encodes := Ra2807.tableCode_eq ▸ encodesTable_tableCode Ra2807.cycles } 649205
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2808.table, code := 30856380436486637411562738062507380801,
        encodes := Ra2808.tableCode_eq ▸ encodesTable_tableCode Ra2808.cycles } 649207
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2809.table, code := 30856461566125052018172446570384199745,
        encodes := Ra2809.tableCode_eq ▸ encodesTable_tableCode Ra2809.cycles } 649213
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2810.table, code := 30856461566125052018244504237436571713,
        encodes := Ra2810.tableCode_eq ▸ encodesTable_tableCode Ra2810.cycles } 649215
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2811.table, code := 30856380436559173041011770760878100545,
        encodes := Ra2811.tableCode_eq ▸ encodesTable_tableCode Ra2811.cycles } 651207
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2812.table, code := 30856461566197587647693536935807291457,
        encodes := Ra2812.tableCode_eq ▸ encodesTable_tableCode Ra2812.cycles } 651215
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2813.table, code := 30856380436559173043461729095606603841,
        encodes := Ra2813.tableCode_eq ▸ encodesTable_tableCode Ra2813.cycles } 651223
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2814.table, code := 30856461566197587650071437603483422785,
        encodes := Ra2814.tableCode_eq ▸ encodesTable_tableCode Ra2814.cycles } 651229
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2815.table, code := 30856461566197587650143495270535794753,
        encodes := Ra2815.tableCode_eq ▸ encodesTable_tableCode Ra2815.cycles } 651231
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2816.table, code := 30856380436641380070820776888672456769,
        encodes := Ra2816.tableCode_eq ▸ encodesTable_tableCode Ra2816.cycles } 651239
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2752 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2752 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2752 + i.val) 0 ≤ Data.profiles (2752 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2752 + i.val) 0 = Data.canonicalMask (2752 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2752 + i.val) < Data.canonicalMask (2752 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2752 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models043
