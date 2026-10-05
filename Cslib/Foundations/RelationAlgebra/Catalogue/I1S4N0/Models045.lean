/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2881
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2882
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2883
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2884
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2885
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2886
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2887
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2888
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2889
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2890
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2891
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2892
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2893
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2894
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2895
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2896
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2897
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2898
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2899
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2900
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2901
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2902
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2903
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2904
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2905
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2906
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2907
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2908
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2909
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2910
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2911
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2912
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2913
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2914
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2915
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2916
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2917
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2918
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2919
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2920
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2921
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2922
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2923
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2924
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2925
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2926
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2927
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2928
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2929
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2930
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2931
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2932
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2933
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2934
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2935
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2936
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2937
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2938
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2939
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2940
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2941
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2942
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2943
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2944

/-!
# Certified models 2881–2944 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models045

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2881.table, code := 23197174994289620295186659139706425409,
        encodes := Ra2881.tableCode_eq ▸ encodesTable_tableCode Ra2881.cycles } 744939
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2882.table, code := 23197174994292038146825890605669027905,
        encodes := Ra2882.tableCode_eq ▸ encodesTable_tableCode Ra2882.cycles } 744943
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2883.table, code := 23197174994292038149203791273345159233,
        encodes := Ra2883.tableCode_eq ▸ encodesTable_tableCode Ra2883.cycles } 744957
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2884.table, code := 23197174994292038149275848940397531201,
        encodes := Ra2884.tableCode_eq ▸ encodesTable_tableCode Ra2884.cycles } 744959
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2885.table, code := 25772797543307499658116439609216077889,
        encodes := Ra2885.tableCode_eq ▸ encodesTable_tableCode Ra2885.cycles } 745063
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2886.table, code := 25772878672945914264798205784145268801,
        encodes := Ra2886.tableCode_eq ▸ encodesTable_tableCode Ra2886.cycles } 745071
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2887.table, code := 25772797543307499660494340276892209217,
        encodes := Ra2887.tableCode_eq ▸ encodesTable_tableCode Ra2887.cycles } 745077
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2888.table, code := 25772797543307499660566397943944581185,
        encodes := Ra2888.tableCode_eq ▸ encodesTable_tableCode Ra2888.cycles } 745079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2889.table, code := 25772878672945914267176106451821400129,
        encodes := Ra2889.tableCode_eq ▸ encodesTable_tableCode Ra2889.cycles } 745085
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2890.table, code := 25772878672945914267248164118873772097,
        encodes := Ra2890.tableCode_eq ▸ encodesTable_tableCode Ra2890.cycles } 745087
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2891.table, code := 25770120267722948911727061064602619969,
        encodes := Ra2891.tableCode_eq ▸ encodesTable_tableCode Ra2891.cycles } 745145
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2892.table, code := 25772797545793051143244125988504997953,
        encodes := Ra2892.tableCode_eq ▸ encodesTable_tableCode Ra2892.cycles } 745191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2893.table, code := 25772878675431465749925892163434188865,
        encodes := Ra2893.tableCode_eq ▸ encodesTable_tableCode Ra2893.cycles } 745199
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2894.table, code := 25772797545793051145694084323233501249,
        encodes := Ra2894.tableCode_eq ▸ encodesTable_tableCode Ra2894.cycles } 745207
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2895.table, code := 25772878675431465752303792831110320193,
        encodes := Ra2895.tableCode_eq ▸ encodesTable_tableCode Ra2895.cycles } 745213
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2896.table, code := 25772878675431465752375850498162692161,
        encodes := Ra2896.tableCode_eq ▸ encodesTable_tableCode Ra2896.cycles } 745215
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2897.table, code := 25853440483139121665340681133461082177,
        encodes := Ra2897.tableCode_eq ▸ encodesTable_tableCode Ra2897.cycles } 745255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2898.table, code := 25853521612777536272022447308390273089,
        encodes := Ra2898.tableCode_eq ▸ encodesTable_tableCode Ra2898.cycles } 745263
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2899.table, code := 25853440483139121667790639468189585473,
        encodes := Ra2899.tableCode_eq ▸ encodesTable_tableCode Ra2899.cycles } 745271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2900.table, code := 25853521612777536274472405643118776385,
        encodes := Ra2900.tableCode_eq ▸ encodesTable_tableCode Ra2900.cycles } 745279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2901.table, code := 25856198890845220654278181434006179905,
        encodes := Ra2901.tableCode_eq ▸ encodesTable_tableCode Ra2901.cycles } 745319
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2902.table, code := 25856280020483635260959947608935370817,
        encodes := Ra2902.tableCode_eq ▸ encodesTable_tableCode Ra2902.cycles } 745327
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2903.table, code := 25856198890845220656656082101682311233,
        encodes := Ra2903.tableCode_eq ▸ encodesTable_tableCode Ra2903.cycles } 745333
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2904.table, code := 25856198890845220656728139768734683201,
        encodes := Ra2904.tableCode_eq ▸ encodesTable_tableCode Ra2904.cycles } 745335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2905.table, code := 25856280020483635263337848276611502145,
        encodes := Ra2905.tableCode_eq ▸ encodesTable_tableCode Ra2905.cycles } 745341
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2906.table, code := 25856280020483635263409905943663874113,
        encodes := Ra2906.tableCode_eq ▸ encodesTable_tableCode Ra2906.cycles } 745343
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2907.table, code := 25853521615180880729791085894613340225,
        encodes := Ra2907.tableCode_eq ▸ encodesTable_tableCode Ra2907.cycles } 745375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2908.table, code := 25853440485624673150468367512750002241,
        encodes := Ra2908.tableCode_eq ▸ encodesTable_tableCode Ra2908.cycles } 745383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2909.table, code := 25853521615260669905510902221716590657,
        encodes := Ra2909.tableCode_eq ▸ encodesTable_tableCode Ra2909.cycles } 745387
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2910.table, code := 25853521615263087757150133687679193153,
        encodes := Ra2910.tableCode_eq ▸ encodesTable_tableCode Ra2910.cycles } 745391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2911.table, code := 25853440485624673152918325847478505537,
        encodes := Ra2911.tableCode_eq ▸ encodesTable_tableCode Ra2911.cycles } 745399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2912.table, code := 25853521615260669907960860556445093953,
        encodes := Ra2912.tableCode_eq ▸ encodesTable_tableCode Ra2912.cycles } 745403
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2913.table, code := 25853521615263087759600092022407696449,
        encodes := Ra2913.tableCode_eq ▸ encodesTable_tableCode Ra2913.cycles } 745407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2914.table, code := 25856198893248565109596861685500743745,
        encodes := Ra2914.tableCode_eq ▸ encodesTable_tableCode Ra2914.cycles } 745415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2915.table, code := 25856280022884561864639396394467332161,
        encodes := Ra2915.tableCode_eq ▸ encodesTable_tableCode Ra2915.cycles } 745419
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2916.table, code := 25856280022886979716278627860429934657,
        encodes := Ra2916.tableCode_eq ▸ encodesTable_tableCode Ra2916.cycles } 745423
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2917.table, code := 25856198893248565112046820020229247041,
        encodes := Ra2917.tableCode_eq ▸ encodesTable_tableCode Ra2917.cycles } 745431
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2918.table, code := 25856280022884561867089354729195835457,
        encodes := Ra2918.tableCode_eq ▸ encodesTable_tableCode Ra2918.cycles } 745435
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2919.table, code := 25856280022886979718656528528106065985,
        encodes := Ra2919.tableCode_eq ▸ encodesTable_tableCode Ra2919.cycles } 745437
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2920.table, code := 25856280022886979718728586195158437953,
        encodes := Ra2920.tableCode_eq ▸ encodesTable_tableCode Ra2920.cycles } 745439
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2921.table, code := 25856198893330772139405867813295099969,
        encodes := Ra2921.tableCode_eq ▸ encodesTable_tableCode Ra2921.cycles } 745447
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2922.table, code := 25856280022966768894448402522261688385,
        encodes := Ra2922.tableCode_eq ▸ encodesTable_tableCode Ra2922.cycles } 745451
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2923.table, code := 25856280022969186746087633988224290881,
        encodes := Ra2923.tableCode_eq ▸ encodesTable_tableCode Ra2923.cycles } 745455
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2924.table, code := 25856198893330772141855826148023603265,
        encodes := Ra2924.tableCode_eq ▸ encodesTable_tableCode Ra2924.cycles } 745463
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2925.table, code := 25856280022966768896826303189937819713,
        encodes := Ra2925.tableCode_eq ▸ encodesTable_tableCode Ra2925.cycles } 745465
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2926.table, code := 25856280022966768896898360856990191681,
        encodes := Ra2926.tableCode_eq ▸ encodesTable_tableCode Ra2926.cycles } 745467
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2927.table, code := 25856280022969186748465534655900422209,
        encodes := Ra2927.tableCode_eq ▸ encodesTable_tableCode Ra2927.cycles } 745469
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2928.table, code := 25856280022969186748537592322952794177,
        encodes := Ra2928.tableCode_eq ▸ encodesTable_tableCode Ra2928.cycles } 745471
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2929.table, code := 23197174999471076581577614160277278785,
        encodes := Ra2929.tableCode_eq ▸ encodesTable_tableCode Ra2929.cycles } 753119
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2930.table, code := 23197174999553283611386620288071635009,
        encodes := Ra2930.tableCode_eq ▸ encodesTable_tableCode Ra2930.cycles } 753151
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2931.table, code := 25772797548568745120227210956890181697,
        encodes := Ra2931.tableCode_eq ▸ encodesTable_tableCode Ra2931.cycles } 753255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2932.table, code := 25772878678207159726908977131819372609,
        encodes := Ra2932.tableCode_eq ▸ encodesTable_tableCode Ra2932.cycles } 753263
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2933.table, code := 25772797548568745122677169291618684993,
        encodes := Ra2933.tableCode_eq ▸ encodesTable_tableCode Ra2933.cycles } 753271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2934.table, code := 25772878678207159729286877799495503937,
        encodes := Ra2934.tableCode_eq ▸ encodesTable_tableCode Ra2934.cycles } 753277
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2935.table, code := 25772878678207159729358935466547875905,
        encodes := Ra2935.tableCode_eq ▸ encodesTable_tableCode Ra2935.cycles } 753279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2936.table, code := 25770120272984194373837832412276723777,
        encodes := Ra2936.tableCode_eq ▸ encodesTable_tableCode Ra2936.cycles } 753337
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2937.table, code := 25772878680610504184677615718042439745,
        encodes := Ra2937.tableCode_eq ▸ encodesTable_tableCode Ra2937.cycles } 753375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2938.table, code := 25772797551054296605354897336179101761,
        encodes := Ra2938.tableCode_eq ▸ encodesTable_tableCode Ra2938.cycles } 753383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2939.table, code := 25772878680692711212036663511108292673,
        encodes := Ra2939.tableCode_eq ▸ encodesTable_tableCode Ra2939.cycles } 753391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2940.table, code := 25772797551054296607804855670907605057,
        encodes := Ra2940.tableCode_eq ▸ encodesTable_tableCode Ra2940.cycles } 753399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2941.table, code := 25772878680692711214414564178784424001,
        encodes := Ra2941.tableCode_eq ▸ encodesTable_tableCode Ra2941.cycles } 753405
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2942.table, code := 25772878680692711214486621845836795969,
        encodes := Ra2942.tableCode_eq ▸ encodesTable_tableCode Ra2942.cycles } 753407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2943.table, code := 25856198896024259086579946653885927489,
        encodes := Ra2943.tableCode_eq ▸ encodesTable_tableCode Ra2943.cycles } 753479
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2944.table, code := 25856280025662673693261712828815118401,
        encodes := Ra2944.tableCode_eq ▸ encodesTable_tableCode Ra2944.cycles } 753487
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2880 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2880 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2880 + i.val) 0 ≤ Data.profiles (2880 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2880 + i.val) 0 = Data.canonicalMask (2880 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2880 + i.val) < Data.canonicalMask (2880 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2880 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models045
