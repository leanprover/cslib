/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0897
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0898
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0899
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0900
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0901
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0902
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0903
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0904
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0905
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0906
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0907
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0908
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0909
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0910
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0911
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0912
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0913
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0914
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0915
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0916
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0917
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0918
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0919
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0920
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0921
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0922
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0923
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0924
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0925
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0926
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0927
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0928
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0929
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0930
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0931
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0932
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0933
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0934
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0935
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0936
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0937
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0938
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0939
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0940
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0941
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0942
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0943
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0944
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0945
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0946
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0947
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0948
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0949
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0950
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0951
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0952
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0953
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0954
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0955
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0956
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0957
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0958
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0959
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0960

/-!
# Certified models 897–960 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models014

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0897.table, code := 4412012701378802610913091636575866945,
        encodes := Ra0897.tableCode_eq ▸ encodesTable_tableCode Ra0897.cycles } 146295
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0898.table, code := 4412093831017217217594857809357574209,
        encodes := Ra0898.tableCode_eq ▸ encodesTable_tableCode Ra0898.cycles } 146302
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0899.table, code := 4412093831017217217594857811505057857,
        encodes := Ra0899.tableCode_eq ▸ encodesTable_tableCode Ra0899.cycles } 146303
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0900.table, code := 4412012703864354096040778013717303361,
        encodes := Ra0900.tableCode_eq ▸ encodesTable_tableCode Ra0900.cycles } 146422
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0901.table, code := 4412012703864354096040778015864787009,
        encodes := Ra0901.tableCode_eq ▸ encodesTable_tableCode Ra0901.cycles } 146423
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0902.table, code := 4412093833502768702722544188646494273,
        encodes := Ra0902.tableCode_eq ▸ encodesTable_tableCode Ra0902.cycles } 146430
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0903.table, code := 4412093833502768702722544190793977921,
        encodes := Ra0903.tableCode_eq ▸ encodesTable_tableCode Ra0903.cycles } 146431
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0904.table, code := 1666829049499593093164238573536546881,
        encodes := Ra0904.tableCode_eq ▸ encodesTable_tableCode Ra0904.cycles } 146591
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0905.table, code := 1666829049581800120523286366602399809,
        encodes := Ra0905.tableCode_eq ▸ encodesTable_tableCode Ra0905.cycles } 146607
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0906.table, code := 1666829049581800122973244701330903105,
        encodes := Ra0906.tableCode_eq ▸ encodesTable_tableCode Ra0906.cycles } 146623
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0907.table, code := 4325852948535909234032926648147644481,
        encodes := Ra0907.tableCode_eq ▸ encodesTable_tableCode Ra0907.cycles } 147089
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0908.table, code := 4325934078174323840714692820929351745,
        encodes := Ra0908.tableCode_eq ▸ encodesTable_tableCode Ra0908.cycles } 147096
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0909.table, code := 4325934078174323840714692823076835393,
        encodes := Ra0909.tableCode_eq ▸ encodesTable_tableCode Ra0909.cycles } 147097
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0910.table, code := 4412012701378802613074819318127267905,
        encodes := Ra0910.tableCode_eq ▸ encodesTable_tableCode Ra0910.cycles } 147302
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0911.table, code := 4412012701378802613074819320274751553,
        encodes := Ra0911.tableCode_eq ▸ encodesTable_tableCode Ra0911.cycles } 147303
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0912.table, code := 4412093831017217219756585493056458817,
        encodes := Ra0912.tableCode_eq ▸ encodesTable_tableCode Ra0912.cycles } 147310
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0913.table, code := 4412093831017217219756585495203942465,
        encodes := Ra0913.tableCode_eq ▸ encodesTable_tableCode Ra0913.cycles } 147311
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0914.table, code := 4412012701378802615524777652855771201,
        encodes := Ra0914.tableCode_eq ▸ encodesTable_tableCode Ra0914.cycles } 147318
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0915.table, code := 4412012701378802615524777655003254849,
        encodes := Ra0915.tableCode_eq ▸ encodesTable_tableCode Ra0915.cycles } 147319
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0916.table, code := 4412093831017217222206543827784962113,
        encodes := Ra0916.tableCode_eq ▸ encodesTable_tableCode Ra0916.cycles } 147326
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0917.table, code := 4412093831017217222206543829932445761,
        encodes := Ra0917.tableCode_eq ▸ encodesTable_tableCode Ra0917.cycles } 147327
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0918.table, code := 4412012703864354098202505697416187969,
        encodes := Ra0918.tableCode_eq ▸ encodesTable_tableCode Ra0918.cycles } 147430
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0919.table, code := 4412012703864354098202505699563671617,
        encodes := Ra0919.tableCode_eq ▸ encodesTable_tableCode Ra0919.cycles } 147431
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0920.table, code := 4412093833502768704884271872345378881,
        encodes := Ra0920.tableCode_eq ▸ encodesTable_tableCode Ra0920.cycles } 147438
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0921.table, code := 4412093833502768704884271874492862529,
        encodes := Ra0921.tableCode_eq ▸ encodesTable_tableCode Ra0921.cycles } 147439
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0922.table, code := 4412012703864354100652464032144691265,
        encodes := Ra0922.tableCode_eq ▸ encodesTable_tableCode Ra0922.cycles } 147446
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0923.table, code := 4412012703864354100652464034292174913,
        encodes := Ra0923.tableCode_eq ▸ encodesTable_tableCode Ra0923.cycles } 147447
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0924.table, code := 4412093833502768707334230207073882177,
        encodes := Ra0924.tableCode_eq ▸ encodesTable_tableCode Ra0924.cycles } 147454
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0925.table, code := 4412093833502768707334230209221365825,
        encodes := Ra0925.tableCode_eq ▸ encodesTable_tableCode Ra0925.cycles } 147455
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0926.table, code := 4505149603330876857888484804251619393,
        encodes := Ra0926.tableCode_eq ▸ encodesTable_tableCode Ra0926.cycles } 154342
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0927.table, code := 4505149603330876857888484806399103041,
        encodes := Ra0927.tableCode_eq ▸ encodesTable_tableCode Ra0927.cycles } 154343
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0928.table, code := 4505230732969291464570250979180810305,
        encodes := Ra0928.tableCode_eq ▸ encodesTable_tableCode Ra0928.cycles } 154350
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0929.table, code := 4505230732969291464570250981328293953,
        encodes := Ra0929.tableCode_eq ▸ encodesTable_tableCode Ra0929.cycles } 154351
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0930.table, code := 4505149603330876860338443138980122689,
        encodes := Ra0930.tableCode_eq ▸ encodesTable_tableCode Ra0930.cycles } 154358
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0931.table, code := 4505149603330876860338443141127606337,
        encodes := Ra0931.tableCode_eq ▸ encodesTable_tableCode Ra0931.cycles } 154359
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0932.table, code := 4505230732969291467020209313909313601,
        encodes := Ra0932.tableCode_eq ▸ encodesTable_tableCode Ra0932.cycles } 154366
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0933.table, code := 4505230732969291467020209316056797249,
        encodes := Ra0933.tableCode_eq ▸ encodesTable_tableCode Ra0933.cycles } 154367
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0934.table, code := 4588550950868597854050226629041721409,
        encodes := Ra0934.tableCode_eq ▸ encodesTable_tableCode Ra0934.cycles } 154598
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0935.table, code := 4588550950868597854050226631189205057,
        encodes := Ra0935.tableCode_eq ▸ encodesTable_tableCode Ra0935.cycles } 154599
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0936.table, code := 4588632080507012460731992803970912321,
        encodes := Ra0936.tableCode_eq ▸ encodesTable_tableCode Ra0936.cycles } 154606
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0937.table, code := 4588632080507012460731992806118395969,
        encodes := Ra0937.tableCode_eq ▸ encodesTable_tableCode Ra0937.cycles } 154607
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0938.table, code := 4588550950868597856500184963770224705,
        encodes := Ra0938.tableCode_eq ▸ encodesTable_tableCode Ra0938.cycles } 154614
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0939.table, code := 4588550950868597856500184965917708353,
        encodes := Ra0939.tableCode_eq ▸ encodesTable_tableCode Ra0939.cycles } 154615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0940.table, code := 4588632080507012463181951138699415617,
        encodes := Ra0940.tableCode_eq ▸ encodesTable_tableCode Ra0940.cycles } 154622
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0941.table, code := 4588632080507012463181951140846899265,
        encodes := Ra0941.tableCode_eq ▸ encodesTable_tableCode Ra0941.cycles } 154623
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0942.table, code := 4505149603330876862500170822679007297,
        encodes := Ra0942.tableCode_eq ▸ encodesTable_tableCode Ra0942.cycles } 155366
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0943.table, code := 4505149603330876862500170824826490945,
        encodes := Ra0943.tableCode_eq ▸ encodesTable_tableCode Ra0943.cycles } 155367
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0944.table, code := 4505230732969291469181936997608198209,
        encodes := Ra0944.tableCode_eq ▸ encodesTable_tableCode Ra0944.cycles } 155374
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0945.table, code := 4505230732969291469181936999755681857,
        encodes := Ra0945.tableCode_eq ▸ encodesTable_tableCode Ra0945.cycles } 155375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0946.table, code := 4505149603330876864950129157407510593,
        encodes := Ra0946.tableCode_eq ▸ encodesTable_tableCode Ra0946.cycles } 155382
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0947.table, code := 4505149603330876864950129159554994241,
        encodes := Ra0947.tableCode_eq ▸ encodesTable_tableCode Ra0947.cycles } 155383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0948.table, code := 4505230732969291471631895332336701505,
        encodes := Ra0948.tableCode_eq ▸ encodesTable_tableCode Ra0948.cycles } 155390
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0949.table, code := 4505230732969291471631895334484185153,
        encodes := Ra0949.tableCode_eq ▸ encodesTable_tableCode Ra0949.cycles } 155391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0950.table, code := 4588550950868597858661912647469109313,
        encodes := Ra0950.tableCode_eq ▸ encodesTable_tableCode Ra0950.cycles } 155622
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0951.table, code := 4588550950868597858661912649616592961,
        encodes := Ra0951.tableCode_eq ▸ encodesTable_tableCode Ra0951.cycles } 155623
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0952.table, code := 4588632080507012465343678822398300225,
        encodes := Ra0952.tableCode_eq ▸ encodesTable_tableCode Ra0952.cycles } 155630
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0953.table, code := 4588632080507012465343678824545783873,
        encodes := Ra0953.tableCode_eq ▸ encodesTable_tableCode Ra0953.cycles } 155631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0954.table, code := 4588550950868597861111870982197612609,
        encodes := Ra0954.tableCode_eq ▸ encodesTable_tableCode Ra0954.cycles } 155638
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0955.table, code := 4588550950868597861111870984345096257,
        encodes := Ra0955.tableCode_eq ▸ encodesTable_tableCode Ra0955.cycles } 155639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0956.table, code := 4588632080507012467793637157126803521,
        encodes := Ra0956.tableCode_eq ▸ encodesTable_tableCode Ra0956.cycles } 155646
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0957.table, code := 4588632080507012467793637159274287169,
        encodes := Ra0957.tableCode_eq ▸ encodesTable_tableCode Ra0957.cycles } 155647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0958.table, code := 4505149605951828177775258630170611777,
        encodes := Ra0958.tableCode_eq ▸ encodesTable_tableCode Ra0958.cycles } 161382
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0959.table, code := 4505149605951828177775258632318095425,
        encodes := Ra0959.tableCode_eq ▸ encodesTable_tableCode Ra0959.cycles } 161383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0960.table, code := 4505230735590242784457024805099802689,
        encodes := Ra0960.tableCode_eq ▸ encodesTable_tableCode Ra0960.cycles } 161390
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (896 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (896 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (896 + i.val) 0 ≤ Data.profiles (896 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (896 + i.val) 0 = Data.canonicalMask (896 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (896 + i.val) < Data.canonicalMask (896 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (896 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models014
