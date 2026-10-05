/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2945
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2946
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2947
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2948
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2949
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2950
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2951
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2952
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2953
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2954
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2955
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2956
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2957
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2958
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2959
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2960
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2961
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2962
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2963
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2964
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2965
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2966
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2967
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2968
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2969
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2970
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2971
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2972
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2973
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2974
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2975
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2976
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2977
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2978
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2979
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2980
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2981
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2982
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2983
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2984
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2985
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2986
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2987
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2988
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2989
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2990
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2991
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2992
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2993
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2994
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2995
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2996
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2997
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2998
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra2999
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3000
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3001
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3002
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3003
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3004
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3005
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3006
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3007
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra3008

/-!
# Certified models 2945–3008 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models046

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2945.table, code := 25856198896024259089029904988614430785,
        encodes := Ra2945.tableCode_eq ▸ encodesTable_tableCode Ra2945.cycles } 753495
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2946.table, code := 25856280025662673695639613496491249729,
        encodes := Ra2946.tableCode_eq ▸ encodesTable_tableCode Ra2946.cycles } 753501
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2947.table, code := 25856280025662673695711671163543621697,
        encodes := Ra2947.tableCode_eq ▸ encodesTable_tableCode Ra2947.cycles } 753503
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2948.table, code := 25856198896106466116388952781680283713,
        encodes := Ra2948.tableCode_eq ▸ encodesTable_tableCode Ra2948.cycles } 753511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2949.table, code := 25856280025744880723070718956609474625,
        encodes := Ra2949.tableCode_eq ▸ encodesTable_tableCode Ra2949.cycles } 753519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2950.table, code := 25856198896106466118838911116408787009,
        encodes := Ra2950.tableCode_eq ▸ encodesTable_tableCode Ra2950.cycles } 753527
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2951.table, code := 25856280025744880725448619624285605953,
        encodes := Ra2951.tableCode_eq ▸ encodesTable_tableCode Ra2951.cycles } 753533
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2952.table, code := 25856280025744880725520677291337977921,
        encodes := Ra2952.tableCode_eq ▸ encodesTable_tableCode Ra2952.cycles } 753535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2953.table, code := 25856198898509810574157591367903350849,
        encodes := Ra2953.tableCode_eq ▸ encodesTable_tableCode Ra2953.cycles } 753623
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2954.table, code := 25856280028145807329200126076869939265,
        encodes := Ra2954.tableCode_eq ▸ encodesTable_tableCode Ra2954.cycles } 753627
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2955.table, code := 25856280028148225180839357542832541761,
        encodes := Ra2955.tableCode_eq ▸ encodesTable_tableCode Ra2955.cycles } 753631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2956.table, code := 25856198898592017603966597495697707073,
        encodes := Ra2956.tableCode_eq ▸ encodesTable_tableCode Ra2956.cycles } 753655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2957.table, code := 25856280028228014358937074537611923521,
        encodes := Ra2957.tableCode_eq ▸ encodesTable_tableCode Ra2957.cycles } 753657
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2958.table, code := 25856280028228014359009132204664295489,
        encodes := Ra2958.tableCode_eq ▸ encodesTable_tableCode Ra2958.cycles } 753659
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2959.table, code := 25856280028230432210648363670626897985,
        encodes := Ra2959.tableCode_eq ▸ encodesTable_tableCode Ra2959.cycles } 753663
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2960.table, code := 31012149514780565042439172115631706177,
        encodes := Ra2960.tableCode_eq ▸ encodesTable_tableCode Ra2960.cycles } 757751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2961.table, code := 31012230644418979649120938290560897089,
        encodes := Ra2961.tableCode_eq ▸ encodesTable_tableCode Ra2961.cycles } 757759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2962.table, code := 31017341811639104608430971220587188289,
        encodes := Ra2962.tableCode_eq ▸ encodesTable_tableCode Ra2962.cycles } 761831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2963.table, code := 31017422941275101363473505929553776705,
        encodes := Ra2963.tableCode_eq ▸ encodesTable_tableCode Ra2963.cycles } 761835
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2964.table, code := 31017422941277519215112737395516379201,
        encodes := Ra2964.tableCode_eq ▸ encodesTable_tableCode Ra2964.cycles } 761839
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2965.table, code := 31017341811639104610880929555315691585,
        encodes := Ra2965.tableCode_eq ▸ encodesTable_tableCode Ra2965.cycles } 761847
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2966.table, code := 31017422941275101365923464264282280001,
        encodes := Ra2966.tableCode_eq ▸ encodesTable_tableCode Ra2966.cycles } 761851
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2967.table, code := 31017422941277519217490638063192510529,
        encodes := Ra2967.tableCode_eq ▸ encodesTable_tableCode Ra2967.cycles } 761853
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2968.table, code := 31017422941277519217562695730244882497,
        encodes := Ra2968.tableCode_eq ▸ encodesTable_tableCode Ra2968.cycles } 761855
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2969.table, code := 30931263191055577151417990197933248577,
        encodes := Ra2969.tableCode_eq ▸ encodesTable_tableCode Ra2969.cycles } 767643
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2970.table, code := 30934021598761676140355490498478346305,
        encodes := Ra2970.tableCode_eq ▸ encodesTable_tableCode Ra2970.cycles } 767707
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2971.table, code := 31017341814260055926156017362807296065,
        encodes := Ra2971.tableCode_eq ▸ encodesTable_tableCode Ra2971.cycles } 767863
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2972.table, code := 31017422943898470532837783537736486977,
        encodes := Ra2972.tableCode_eq ▸ encodesTable_tableCode Ra2972.cycles } 767871
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2973.table, code := 31017341816745607411283703742096216129,
        encodes := Ra2973.tableCode_eq ▸ encodesTable_tableCode Ra2973.cycles } 767991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2974.table, code := 31017422946381604166326238451062804545,
        encodes := Ra2974.tableCode_eq ▸ encodesTable_tableCode Ra2974.cycles } 767995
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2975.table, code := 31017422946384022017965469917025407041,
        encodes := Ra2975.tableCode_eq ▸ encodesTable_tableCode Ra2975.cycles } 767999
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2976.table, code := 31017341814414798585414056188972372033,
        encodes := Ra2976.tableCode_eq ▸ encodesTable_tableCode Ra2976.cycles } 769895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2977.table, code := 31017422944053213192095822363901562945,
        encodes := Ra2977.tableCode_eq ▸ encodesTable_tableCode Ra2977.cycles } 769903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2978.table, code := 31017341814414798587864014523700875329,
        encodes := Ra2978.tableCode_eq ▸ encodesTable_tableCode Ra2978.cycles } 769911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2979.table, code := 31017422944053213194473723031577694273,
        encodes := Ra2979.tableCode_eq ▸ encodesTable_tableCode Ra2979.cycles } 769917
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2980.table, code := 31017422944053213194545780698630066241,
        encodes := Ra2980.tableCode_eq ▸ encodesTable_tableCode Ra2980.cycles } 769919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2981.table, code := 31017341816818143043182694775195439169,
        encodes := Ra2981.tableCode_eq ▸ encodesTable_tableCode Ra2981.cycles } 770007
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2982.table, code := 31017422946454139798225229484162027585,
        encodes := Ra2982.tableCode_eq ▸ encodesTable_tableCode Ra2982.cycles } 770011
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2983.table, code := 31017422946456557649864460950124630081,
        encodes := Ra2983.tableCode_eq ▸ encodesTable_tableCode Ra2983.cycles } 770015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2984.table, code := 31017341816900350070541742568261292097,
        encodes := Ra2984.tableCode_eq ▸ encodesTable_tableCode Ra2984.cycles } 770023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2985.table, code := 31017422946536346825584277277227880513,
        encodes := Ra2985.tableCode_eq ▸ encodesTable_tableCode Ra2985.cycles } 770027
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2986.table, code := 31017422946538764677223508743190483009,
        encodes := Ra2986.tableCode_eq ▸ encodesTable_tableCode Ra2986.cycles } 770031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2987.table, code := 31017341816900350072991700902989795393,
        encodes := Ra2987.tableCode_eq ▸ encodesTable_tableCode Ra2987.cycles } 770039
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2988.table, code := 31017422946536346828034235611956383809,
        encodes := Ra2988.tableCode_eq ▸ encodesTable_tableCode Ra2988.cycles } 770043
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2989.table, code := 31017422946538764679601409410866614337,
        encodes := Ra2989.tableCode_eq ▸ encodesTable_tableCode Ra2989.cycles } 770045
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2990.table, code := 31017422946538764679673467077918986305,
        encodes := Ra2990.tableCode_eq ▸ encodesTable_tableCode Ra2990.cycles } 770047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2991.table, code := 31188687767046054265009350413358731329,
        encodes := Ra2991.tableCode_eq ▸ encodesTable_tableCode Ra2991.cycles } 774135
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2992.table, code := 31188768896684468871691116588287922241,
        encodes := Ra2992.tableCode_eq ▸ encodesTable_tableCode Ra2992.cycles } 774143
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2993.table, code := 31191202785834491599556142261464207425,
        encodes := Ra2993.tableCode_eq ▸ encodesTable_tableCode Ra2993.cycles } 778171
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2994.table, code := 31191202785836909451195373727426809921,
        encodes := Ra2994.tableCode_eq ▸ encodesTable_tableCode Ra2994.cycles } 778175
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2995.table, code := 31193880063904593831001149518314213441,
        encodes := Ra2995.tableCode_eq ▸ encodesTable_tableCode Ra2995.cycles } 778215
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2996.table, code := 31193961193543008437682915693243404353,
        encodes := Ra2996.tableCode_eq ▸ encodesTable_tableCode Ra2996.cycles } 778223
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2997.table, code := 31193961193540590588493642562009305153,
        encodes := Ra2997.tableCode_eq ▸ encodesTable_tableCode Ra2997.cycles } 778235
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2998.table, code := 31193961193543008440060816360919535681,
        encodes := Ra2998.tableCode_eq ▸ encodesTable_tableCode Ra2998.cycles } 778237
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra2999.table, code := 31193961193543008440132874027971907649,
        encodes := Ra2999.tableCode_eq ▸ encodesTable_tableCode Ra2999.cycles } 778239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3000.table, code := 31191202790940994399958916448244731969,
        encodes := Ra3000.tableCode_eq ▸ encodesTable_tableCode Ra3000.cycles } 784315
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3001.table, code := 31191202790943412251598147914207334465,
        encodes := Ra3001.tableCode_eq ▸ encodesTable_tableCode Ra3001.cycles } 784319
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3002.table, code := 31193961198647093388896416748789829697,
        encodes := Ra3002.tableCode_eq ▸ encodesTable_tableCode Ra3002.cycles } 784379
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3003.table, code := 31193961198649511240535648214752432193,
        encodes := Ra3003.tableCode_eq ▸ encodesTable_tableCode Ra3003.cycles } 784383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3004.table, code := 31191202791015947883497138947306557505,
        encodes := Ra3004.tableCode_eq ▸ encodesTable_tableCode Ra3004.cycles } 786335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3005.table, code := 31191202791098154913306145075100913729,
        encodes := Ra3005.tableCode_eq ▸ encodesTable_tableCode Ra3005.cycles } 786367
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3006.table, code := 31193961198722046872434639247851655233,
        encodes := Ra3006.tableCode_eq ▸ encodesTable_tableCode Ra3006.cycles } 786399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3007.table, code := 31193961198804253899793687040917508161,
        encodes := Ra3007.tableCode_eq ▸ encodesTable_tableCode Ra3007.cycles } 786415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra3008.table, code := 31193961198804253902243645375646011457,
        encodes := Ra3008.tableCode_eq ▸ encodesTable_tableCode Ra3008.cycles } 786431
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2944 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (2944 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (2944 + i.val) 0 ≤ Data.profiles (2944 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (2944 + i.val) 0 = Data.canonicalMask (2944 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (2944 + i.val) < Data.canonicalMask (2944 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (2944 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models046
