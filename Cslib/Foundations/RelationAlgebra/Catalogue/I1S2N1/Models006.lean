/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0385
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0386
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0387
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0388
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0389
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0390
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0391
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0392
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0393
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0394
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0395
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0396
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0397
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0398
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0399
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0400
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0401
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0402
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0403
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0404
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0405
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0406
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0407
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0408
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0409
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0410
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0411
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0412
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0413
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0414
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0415
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0416
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0417
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0418
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0419
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0420
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0421
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0422
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0423
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0424
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0425
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0426
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0427
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0428
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0429
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0430
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0431
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0432
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0433
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0434
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0435
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0436
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0437
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0438
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0439
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0440
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0441
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0442
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0443
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0444
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0445
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0446
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0447
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0448

/-!
# Certified models 385–448 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models006

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0385.table, code := 30319059830211525062421412591993884737,
        encodes := Ra0385.tableCode_eq ▸ encodesTable_tableCode Ra0385.cycles } 23775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0386.table, code := 30321493719291425425938991942797103169,
        encodes := Ra0386.tableCode_eq ▸ encodesTable_tableCode Ra0386.cycles } 23789
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0387.table, code := 30321493719291425426011049609849475137,
        encodes := Ra0387.tableCode_eq ▸ encodesTable_tableCode Ra0387.cycles } 23791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0388.table, code := 30321655978645628251067468311163048001,
        encodes := Ra0388.tableCode_eq ▸ encodesTable_tableCode Ra0388.cycles } 23796
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0389.table, code := 30321655978645628251067468313310531649,
        encodes := Ra0389.tableCode_eq ▸ encodesTable_tableCode Ra0389.cycles } 23797
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0390.table, code := 30321655978645628251139525978215419969,
        encodes := Ra0390.tableCode_eq ▸ encodesTable_tableCode Ra0390.cycles } 23798
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0391.table, code := 30321655978645628251139525980362903617,
        encodes := Ra0391.tableCode_eq ▸ encodesTable_tableCode Ra0391.cycles } 23799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0392.table, code := 30321655978645628253517426648039034945,
        encodes := Ra0392.tableCode_eq ▸ encodesTable_tableCode Ra0392.cycles } 23805
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0393.table, code := 30321655978645628253589484312943923265,
        encodes := Ra0393.tableCode_eq ▸ encodesTable_tableCode Ra0393.cycles } 23806
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0394.table, code := 30321655978645628253589484315091406913,
        encodes := Ra0394.tableCode_eq ▸ encodesTable_tableCode Ra0394.cycles } 23807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0395.table, code := 27743112678344005360844599540941328449,
        encodes := Ra0395.tableCode_eq ▸ encodesTable_tableCode Ra0395.cycles } 23880
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0396.table, code := 27743112678344005360844599543088812097,
        encodes := Ra0396.tableCode_eq ▸ encodesTable_tableCode Ra0396.cycles } 23881
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0397.table, code := 27745871086132311377213205301604651073,
        encodes := Ra0397.tableCode_eq ▸ encodesTable_tableCode Ra0397.cycles } 23922
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0398.table, code := 27745871086132311377213205303752134721,
        encodes := Ra0398.tableCode_eq ▸ encodesTable_tableCode Ra0398.cycles } 23923
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0399.table, code := 27745952215773143835462145275444072513,
        encodes := Ra0399.tableCode_eq ▸ encodesTable_tableCode Ra0399.cycles } 23924
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0400.table, code := 27745952215773143835462145277591556161,
        encodes := Ra0400.tableCode_eq ▸ encodesTable_tableCode Ra0400.cycles } 23925
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0401.table, code := 27745952215773143835534202942496444481,
        encodes := Ra0401.tableCode_eq ▸ encodesTable_tableCode Ra0401.cycles } 23926
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0402.table, code := 27745952215773143835534202944643928129,
        encodes := Ra0402.tableCode_eq ▸ encodesTable_tableCode Ra0402.cycles } 23927
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0403.table, code := 27745871086132311379663163636333154369,
        encodes := Ra0403.tableCode_eq ▸ encodesTable_tableCode Ra0403.cycles } 23930
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0404.table, code := 27745871086132311379663163638480638017,
        encodes := Ra0404.tableCode_eq ▸ encodesTable_tableCode Ra0404.cycles } 23931
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0405.table, code := 27745952215773143837912103610172575809,
        encodes := Ra0405.tableCode_eq ▸ encodesTable_tableCode Ra0405.cycles } 23932
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0406.table, code := 27745952215773143837912103612320059457,
        encodes := Ra0406.tableCode_eq ▸ encodesTable_tableCode Ra0406.cycles } 23933
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0407.table, code := 27745952215773143837984161277224947777,
        encodes := Ra0407.tableCode_eq ▸ encodesTable_tableCode Ra0407.cycles } 23934
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0408.table, code := 27745952215773143837984161279372431425,
        encodes := Ra0408.tableCode_eq ▸ encodesTable_tableCode Ra0408.cycles } 23935
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0409.table, code := 30401487463622274340867509478058364993,
        encodes := Ra0409.tableCode_eq ▸ encodesTable_tableCode Ra0409.cycles } 23958
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0410.table, code := 30401487463622274340867509480205848641,
        encodes := Ra0410.tableCode_eq ▸ encodesTable_tableCode Ra0410.cycles } 23959
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0411.table, code := 30401487463622274343245410147881979969,
        encodes := Ra0411.tableCode_eq ▸ encodesTable_tableCode Ra0411.cycles } 23965
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0412.table, code := 30401487463622274343317467812786868289,
        encodes := Ra0412.tableCode_eq ▸ encodesTable_tableCode Ra0412.cycles } 23966
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0413.table, code := 30401487463622274343317467814934351937,
        encodes := Ra0413.tableCode_eq ▸ encodesTable_tableCode Ra0413.cycles } 23967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0414.table, code := 30404083612056377531963523534103515201,
        encodes := Ra0414.tableCode_eq ▸ encodesTable_tableCode Ra0414.cycles } 23988
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0415.table, code := 30404083612056377531963523536250998849,
        encodes := Ra0415.tableCode_eq ▸ encodesTable_tableCode Ra0415.cycles } 23989
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0416.table, code := 30404083612056377532035581201155887169,
        encodes := Ra0416.tableCode_eq ▸ encodesTable_tableCode Ra0416.cycles } 23990
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0417.table, code := 30404083612056377532035581203303370817,
        encodes := Ra0417.tableCode_eq ▸ encodesTable_tableCode Ra0417.cycles } 23991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0418.table, code := 30404083612056377534413481870979502145,
        encodes := Ra0418.tableCode_eq ▸ encodesTable_tableCode Ra0418.cycles } 23997
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0419.table, code := 30404083612056377534485539535884390465,
        encodes := Ra0419.tableCode_eq ▸ encodesTable_tableCode Ra0419.cycles } 23998
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0420.table, code := 30404083612056377534485539538031874113,
        encodes := Ra0420.tableCode_eq ▸ encodesTable_tableCode Ra0420.cycles } 23999
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0421.table, code := 30401974320603550883456945809223061569,
        encodes := Ra0421.tableCode_eq ▸ encodesTable_tableCode Ra0421.cycles } 24014
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0422.table, code := 30401974320603550883456945811370545217,
        encodes := Ra0422.tableCode_eq ▸ encodesTable_tableCode Ra0422.cycles } 24015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0423.table, code := 30402136579957753708585422179736490049,
        encodes := Ra0423.tableCode_eq ▸ encodesTable_tableCode Ra0423.cycles } 24022
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0424.table, code := 30402136579957753708585422181883973697,
        encodes := Ra0424.tableCode_eq ▸ encodesTable_tableCode Ra0424.cycles } 24023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0425.table, code := 30402136579957753710963322847412621377,
        encodes := Ra0425.tableCode_eq ▸ encodesTable_tableCode Ra0425.cycles } 24028
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0426.table, code := 30402136579957753710963322849560105025,
        encodes := Ra0426.tableCode_eq ▸ encodesTable_tableCode Ra0426.cycles } 24029
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0427.table, code := 30402136579957753711035380514464993345,
        encodes := Ra0427.tableCode_eq ▸ encodesTable_tableCode Ra0427.cycles } 24030
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0428.table, code := 30402136579957753711035380516612476993,
        encodes := Ra0428.tableCode_eq ▸ encodesTable_tableCode Ra0428.cycles } 24031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0429.table, code := 30404570469037654074552959865268211777,
        encodes := Ra0429.tableCode_eq ▸ encodesTable_tableCode Ra0429.cycles } 24044
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0430.table, code := 30404570469037654074552959867415695425,
        encodes := Ra0430.tableCode_eq ▸ encodesTable_tableCode Ra0430.cycles } 24045
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0431.table, code := 30404570469037654074625017532320583745,
        encodes := Ra0431.tableCode_eq ▸ encodesTable_tableCode Ra0431.cycles } 24046
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0432.table, code := 30404570469037654074625017534468067393,
        encodes := Ra0432.tableCode_eq ▸ encodesTable_tableCode Ra0432.cycles } 24047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0433.table, code := 30404651598751024441360438597037330497,
        encodes := Ra0433.tableCode_eq ▸ encodesTable_tableCode Ra0433.cycles } 24049
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0434.table, code := 30404651598751024441432496261942218817,
        encodes := Ra0434.tableCode_eq ▸ encodesTable_tableCode Ra0434.cycles } 24050
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0435.table, code := 30404651598751024441432496264089702465,
        encodes := Ra0435.tableCode_eq ▸ encodesTable_tableCode Ra0435.cycles } 24051
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0436.table, code := 30404732728391856899681436235781640257,
        encodes := Ra0436.tableCode_eq ▸ encodesTable_tableCode Ra0436.cycles } 24052
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0437.table, code := 30404732728391856899681436237929123905,
        encodes := Ra0437.tableCode_eq ▸ encodesTable_tableCode Ra0437.cycles } 24053
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0438.table, code := 30404732728391856899753493902834012225,
        encodes := Ra0438.tableCode_eq ▸ encodesTable_tableCode Ra0438.cycles } 24054
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0439.table, code := 30404732728391856899753493904981495873,
        encodes := Ra0439.tableCode_eq ▸ encodesTable_tableCode Ra0439.cycles } 24055
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0440.table, code := 30404651598751024443810396931765833793,
        encodes := Ra0440.tableCode_eq ▸ encodesTable_tableCode Ra0440.cycles } 24057
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0441.table, code := 30404651598751024443882454596670722113,
        encodes := Ra0441.tableCode_eq ▸ encodesTable_tableCode Ra0441.cycles } 24058
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0442.table, code := 30404651598751024443882454598818205761,
        encodes := Ra0442.tableCode_eq ▸ encodesTable_tableCode Ra0442.cycles } 24059
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0443.table, code := 30404732728391856902131394570510143553,
        encodes := Ra0443.tableCode_eq ▸ encodesTable_tableCode Ra0443.cycles } 24060
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0444.table, code := 30404732728391856902131394572657627201,
        encodes := Ra0444.tableCode_eq ▸ encodesTable_tableCode Ra0444.cycles } 24061
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0445.table, code := 30404732728391856902203452237562515521,
        encodes := Ra0445.tableCode_eq ▸ encodesTable_tableCode Ra0445.cycles } 24062
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0446.table, code := 30404732728391856902203452239709999169,
        encodes := Ra0446.tableCode_eq ▸ encodesTable_tableCode Ra0446.cycles } 24063
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0447.table, code := 30319059830211525064583140275692769345,
        encodes := Ra0447.tableCode_eq ▸ encodesTable_tableCode Ra0447.cycles } 24279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0448.table, code := 30319059830211525067033098610421272641,
        encodes := Ra0448.tableCode_eq ▸ encodesTable_tableCode Ra0448.cycles } 24287
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (384 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (384 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (384 + i.val) 0 ≤ Data.profiles (384 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (384 + i.val) 0 = Data.canonicalMask (384 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (384 + i.val) < Data.canonicalMask (384 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (384 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models006
