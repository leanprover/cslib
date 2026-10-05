/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2817
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2818
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2819
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2820
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2821
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2822
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2823
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2824
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2825
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2826
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2827
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2828
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2829
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2830
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2831
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2832
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2833
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2834
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2835
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2836
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2837
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2838
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2839
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2840
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2841
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2842
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2843
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2844
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2845
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2846
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2847
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2848
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2849
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2850
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2851
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2852
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2853
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2854
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2855
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2856
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2857
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2858
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2859
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2860
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2861
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2862
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2863
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2864
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2865
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2866
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2867
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2868
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2869
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2870
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2871
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2872
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2873
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2874
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2875
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2876
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2877
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2878
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2879
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2880

/-!
# Certified models 2817–2880 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models044

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2817.table, code := 30856461566277376825863311597639045185,
        encodes := Ra2817.tableCode_eq ▸ encodesTable_tableCode Ra2817.cycles } 651243
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2818.table, code := 30856461566279794677502543063601647681,
        encodes := Ra2818.tableCode_eq ▸ encodesTable_tableCode Ra2818.cycles } 651247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2819.table, code := 30856380436641380073270735223400960065,
        encodes := Ra2819.tableCode_eq ▸ encodesTable_tableCode Ra2819.cycles } 651255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2820.table, code := 30856461566277376828313269932367548481,
        encodes := Ra2820.tableCode_eq ▸ encodesTable_tableCode Ra2820.cycles } 651259
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2821.table, code := 30856461566279794679880443731277779009,
        encodes := Ra2821.tableCode_eq ▸ encodesTable_tableCode Ra2821.cycles } 651261
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2822.table, code := 30856461566279794679952501398330150977,
        encodes := Ra2822.tableCode_eq ▸ encodesTable_tableCode Ra2822.cycles } 651263
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2823.table, code := 30858895455350028229647752409674682433,
        encodes := Ra2823.tableCode_eq ▸ encodesTable_tableCode Ra2823.cycles } 655263
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2824.table, code := 30858895455432235257006800202740535361,
        encodes := Ra2824.tableCode_eq ▸ encodesTable_tableCode Ra2824.cycles } 655279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2825.table, code := 30858895455432235259456758537469038657,
        encodes := Ra2825.tableCode_eq ▸ encodesTable_tableCode Ra2825.cycles } 655295
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2826.table, code := 30861653863138334245944300503285633089,
        encodes := Ra2826.tableCode_eq ▸ encodesTable_tableCode Ra2826.cycles } 655343
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2827.table, code := 30861653863138334248394258838014136385,
        encodes := Ra2827.tableCode_eq ▸ encodesTable_tableCode Ra2827.cycles } 655359
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2828.table, code := 22934476984214970424219777675523526721,
        encodes := Ra2828.tableCode_eq ▸ encodesTable_tableCode Ra2828.cycles } 728079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2829.table, code := 22934476984214970426669736010252030017,
        encodes := Ra2829.tableCode_eq ▸ encodesTable_tableCode Ra2829.cycles } 728095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2830.table, code := 22934476984297177454028783803317882945,
        encodes := Ra2830.tableCode_eq ▸ encodesTable_tableCode Ra2830.cycles } 728111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2831.table, code := 22934476984297177456478742138046386241,
        encodes := Ra2831.tableCode_eq ▸ encodesTable_tableCode Ra2831.cycles } 728127
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2832.table, code := 22937235392003276442966284103862980673,
        encodes := Ra2832.tableCode_eq ▸ encodesTable_tableCode Ra2832.cycles } 728175
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2833.table, code := 22937235392003276445416242438591483969,
        encodes := Ra2833.tableCode_eq ▸ encodesTable_tableCode Ra2833.cycles } 728191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2834.table, code := 22934476986700521911725364722488578113,
        encodes := Ra2834.tableCode_eq ▸ encodesTable_tableCode Ra2834.cycles } 728221
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2835.table, code := 22934476986780311087517238716644200513,
        encodes := Ra2835.tableCode_eq ▸ encodesTable_tableCode Ra2835.cycles } 728235
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2836.table, code := 22934476986782728939156470182606803009,
        encodes := Ra2836.tableCode_eq ▸ encodesTable_tableCode Ra2836.cycles } 728239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2837.table, code := 22934476986782728941534370850282934337,
        encodes := Ra2837.tableCode_eq ▸ encodesTable_tableCode Ra2837.cycles } 728253
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2838.table, code := 22934476986782728941606428517335306305,
        encodes := Ra2838.tableCode_eq ▸ encodesTable_tableCode Ra2838.cycles } 728255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2839.table, code := 23017878331752691422759420167989760065,
        encodes := Ra2839.tableCode_eq ▸ encodesTable_tableCode Ra2839.cycles } 728349
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2840.table, code := 23017878334238242907887106547278680129,
        encodes := Ra2840.tableCode_eq ▸ encodesTable_tableCode Ra2840.cycles } 728477
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2841.table, code := 25593582015375252659347876639081238593,
        encodes := Ra2841.tableCode_eq ▸ encodesTable_tableCode Ra2841.cycles } 728729
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2842.table, code := 25676902230791425415339397375615832129,
        encodes := Ra2842.tableCode_eq ▸ encodesTable_tableCode Ra2842.cycles } 728853
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2843.table, code := 25676983360429840022021163550545023041,
        encodes := Ra2843.tableCode_eq ▸ encodesTable_tableCode Ra2843.cycles } 728861
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2844.table, code := 25676983362912973655509618463871340609,
        encodes := Ra2844.tableCode_eq ▸ encodesTable_tableCode Ra2844.cycles } 728985
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2845.table, code := 25676983362915391507148849929833943105,
        encodes := Ra2845.tableCode_eq ▸ encodesTable_tableCode Ra2845.cycles } 728989
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2846.table, code := 25679660641062865065196458049605472321,
        encodes := Ra2846.tableCode_eq ▸ encodesTable_tableCode Ra2846.cycles } 729059
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2847.table, code := 25679660641065282916835689515568074817,
        encodes := Ra2847.tableCode_eq ▸ encodesTable_tableCode Ra2847.cycles } 729063
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2848.table, code := 25679741770701279671878224224534663233,
        encodes := Ra2848.tableCode_eq ▸ encodesTable_tableCode Ra2848.cycles } 729067
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2849.table, code := 25679741770703697523517455690497265729,
        encodes := Ra2849.tableCode_eq ▸ encodesTable_tableCode Ra2849.cycles } 729071
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2850.table, code := 25679660641062865067574358717281603649,
        encodes := Ra2850.tableCode_eq ▸ encodesTable_tableCode Ra2850.cycles } 729073
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2851.table, code := 25679660641062865067646416384333975617,
        encodes := Ra2851.tableCode_eq ▸ encodesTable_tableCode Ra2851.cycles } 729075
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2852.table, code := 25679660641065282919213590183244206145,
        encodes := Ra2852.tableCode_eq ▸ encodesTable_tableCode Ra2852.cycles } 729077
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2853.table, code := 25679660641065282919285647850296578113,
        encodes := Ra2853.tableCode_eq ▸ encodesTable_tableCode Ra2853.cycles } 729079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2854.table, code := 25679741770701279674256124892210794561,
        encodes := Ra2854.tableCode_eq ▸ encodesTable_tableCode Ra2854.cycles } 729081
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2855.table, code := 25679741770701279674328182559263166529,
        encodes := Ra2855.tableCode_eq ▸ encodesTable_tableCode Ra2855.cycles } 729083
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2856.table, code := 25679741770703697525895356358173397057,
        encodes := Ra2856.tableCode_eq ▸ encodesTable_tableCode Ra2856.cycles } 729085
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2857.table, code := 25679741770703697525967414025225769025,
        encodes := Ra2857.tableCode_eq ▸ encodesTable_tableCode Ra2857.cycles } 729087
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2858.table, code := 22934476991961767373908193737215053889,
        encodes := Ra2858.tableCode_eq ▸ encodesTable_tableCode Ra2858.cycles } 736415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2859.table, code := 22934476992043974403717199865009410113,
        encodes := Ra2859.tableCode_eq ▸ encodesTable_tableCode Ra2859.cycles } 736447
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2860.table, code := 22937235399750073390204741830826004545,
        encodes := Ra2860.tableCode_eq ▸ encodesTable_tableCode Ra2860.cycles } 736495
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2861.table, code := 22937235399750073392654700165554507841,
        encodes := Ra2861.tableCode_eq ▸ encodesTable_tableCode Ra2861.cycles } 736511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2862.table, code := 25593582020636498121458647986755342401,
        encodes := Ra2862.tableCode_eq ▸ encodesTable_tableCode Ra2862.cycles } 736921
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2863.table, code := 25679660643840976893818774483953258561,
        encodes := Ra2863.tableCode_eq ▸ encodesTable_tableCode Ra2863.cycles } 737127
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2864.table, code := 25679741773479391500500540658882449473,
        encodes := Ra2864.tableCode_eq ▸ encodesTable_tableCode Ra2864.cycles } 737135
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2865.table, code := 25679660643840976896196675151629389889,
        encodes := Ra2865.tableCode_eq ▸ encodesTable_tableCode Ra2865.cycles } 737141
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2866.table, code := 25679660643840976896268732818681761857,
        encodes := Ra2866.tableCode_eq ▸ encodesTable_tableCode Ra2866.cycles } 737143
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2867.table, code := 25679741773479391502878441326558580801,
        encodes := Ra2867.tableCode_eq ▸ encodesTable_tableCode Ra2867.cycles } 737149
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2868.table, code := 25679741773479391502950498993610952769,
        encodes := Ra2868.tableCode_eq ▸ encodesTable_tableCode Ra2868.cycles } 737151
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2869.table, code := 25679660646324110529685130064955707457,
        encodes := Ra2869.tableCode_eq ▸ encodesTable_tableCode Ra2869.cycles } 737265
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2870.table, code := 25679660646324110529757187732008079425,
        encodes := Ra2870.tableCode_eq ▸ encodesTable_tableCode Ra2870.cycles } 737267
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2871.table, code := 25679660646326528381396419197970681921,
        encodes := Ra2871.tableCode_eq ▸ encodesTable_tableCode Ra2871.cycles } 737271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2872.table, code := 25679741775962525136366896239884898369,
        encodes := Ra2872.tableCode_eq ▸ encodesTable_tableCode Ra2872.cycles } 737273
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2873.table, code := 25679741775962525136438953906937270337,
        encodes := Ra2873.tableCode_eq ▸ encodesTable_tableCode Ra2873.cycles } 737275
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2874.table, code := 25679741775964942988078185372899872833,
        encodes := Ra2874.tableCode_eq ▸ encodesTable_tableCode Ra2874.cycles } 737279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2875.table, code := 23197174991806486661698204226380107841,
        encodes := Ra2875.tableCode_eq ▸ encodesTable_tableCode Ra2875.cycles } 744815
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2876.table, code := 23197174991806486664148162561108611137,
        encodes := Ra2876.tableCode_eq ▸ encodesTable_tableCode Ra2876.cycles } 744831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2877.table, code := 23197174994207413265377653011912069185,
        encodes := Ra2877.tableCode_eq ▸ encodesTable_tableCode Ra2877.cycles } 744907
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2878.table, code := 23197174994209831117016884477874671681,
        encodes := Ra2878.tableCode_eq ▸ encodesTable_tableCode Ra2878.cycles } 744911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2879.table, code := 23197174994209831119394785145550803009,
        encodes := Ra2879.tableCode_eq ▸ encodesTable_tableCode Ra2879.cycles } 744925
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2880.table, code := 23197174994209831119466842812603174977,
        encodes := Ra2880.tableCode_eq ▸ encodesTable_tableCode Ra2880.cycles } 744927
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2816 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2816 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2816 + i.val) 0 ≤ Data.profiles (2816 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2816 + i.val) 0 = Data.canonicalMask (2816 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2816 + i.val) < Data.canonicalMask (2816 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2816 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models044
