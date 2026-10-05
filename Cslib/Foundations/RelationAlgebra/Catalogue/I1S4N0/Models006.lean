/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0385
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0386
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0387
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0388
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0389
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0390
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0391
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0392
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0393
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0394
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0395
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0396
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0397
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0398
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0399
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0400
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0401
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0402
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0403
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0404
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0405
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0406
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0407
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0408
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0409
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0410
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0411
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0412
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0413
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0414
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0415
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0416
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0417
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0418
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0419
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0420
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0421
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0422
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0423
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0424
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0425
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0426
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0427
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0428
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0429
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0430
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0431
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0432
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0433
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0434
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0435
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0436
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0437
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0438
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0439
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0440
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0441
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0442
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0443
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0444
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0445
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0446
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0447
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0448

/-!
# Certified models 385–448 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models006

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0385.table, code := 4253566352145016939692566707070832705,
        encodes := Ra0385.tableCode_eq ▸ encodesTable_tableCode Ra0385.cycles } 96191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0386.table, code := 4256243630212701319498342495810752577,
        encodes := Ra0386.tableCode_eq ▸ encodesTable_tableCode Ra0386.cycles } 96230
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0387.table, code := 4256243630212701319498342497958236225,
        encodes := Ra0387.tableCode_eq ▸ encodesTable_tableCode Ra0387.cycles } 96231
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0388.table, code := 4256324759851115926180108670739943489,
        encodes := Ra0388.tableCode_eq ▸ encodesTable_tableCode Ra0388.cycles } 96238
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0389.table, code := 4256324759851115926180108672887427137,
        encodes := Ra0389.tableCode_eq ▸ encodesTable_tableCode Ra0389.cycles } 96239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0390.table, code := 4256243630212701321948300830539255873,
        encodes := Ra0390.tableCode_eq ▸ encodesTable_tableCode Ra0390.cycles } 96246
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0391.table, code := 4256243630212701321948300832686739521,
        encodes := Ra0391.tableCode_eq ▸ encodesTable_tableCode Ra0391.cycles } 96247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0392.table, code := 4256324759851115928630067005468446785,
        encodes := Ra0392.tableCode_eq ▸ encodesTable_tableCode Ra0392.cycles } 96254
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0393.table, code := 4256324759851115928630067007615930433,
        encodes := Ra0393.tableCode_eq ▸ encodesTable_tableCode Ra0393.cycles } 96255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0394.table, code := 4253485220173375653340193829356310593,
        encodes := Ra0394.tableCode_eq ▸ encodesTable_tableCode Ra0394.cycles } 97075
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0395.table, code := 4253566349814208111661191468100620353,
        encodes := Ra0395.tableCode_eq ▸ encodesTable_tableCode Ra0395.cycles } 97086
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0396.table, code := 4253566349814208111661191470248104001,
        encodes := Ra0396.tableCode_eq ▸ encodesTable_tableCode Ra0396.cycles } 97087
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0397.table, code := 4256243627881892493916925593716527169,
        encodes := Ra0397.tableCode_eq ▸ encodesTable_tableCode Ra0397.cycles } 97142
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0398.table, code := 4256243627881892493916925595864010817,
        encodes := Ra0398.tableCode_eq ▸ encodesTable_tableCode Ra0398.cycles } 97143
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0399.table, code := 4256324757520307100598691768645718081,
        encodes := Ra0399.tableCode_eq ▸ encodesTable_tableCode Ra0399.cycles } 97150
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0400.table, code := 4256324757520307100598691770793201729,
        encodes := Ra0400.tableCode_eq ▸ encodesTable_tableCode Ra0400.cycles } 97151
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0401.table, code := 4253485222658927138467880206497747009,
        encodes := Ra0401.tableCode_eq ▸ encodesTable_tableCode Ra0401.cycles } 97202
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0402.table, code := 4253485222658927138467880208645230657,
        encodes := Ra0402.tableCode_eq ▸ encodesTable_tableCode Ra0402.cycles } 97203
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0403.table, code := 4253566352299759596788877847389540417,
        encodes := Ra0403.tableCode_eq ▸ encodesTable_tableCode Ra0403.cycles } 97214
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0404.table, code := 4253566352299759596788877849537024065,
        encodes := Ra0404.tableCode_eq ▸ encodesTable_tableCode Ra0404.cycles } 97215
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0405.table, code := 4256243630367443979044611973005447233,
        encodes := Ra0405.tableCode_eq ▸ encodesTable_tableCode Ra0405.cycles } 97270
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0406.table, code := 4256243630367443979044611975152930881,
        encodes := Ra0406.tableCode_eq ▸ encodesTable_tableCode Ra0406.cycles } 97271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0407.table, code := 4256324760005858585726378147934638145,
        encodes := Ra0407.tableCode_eq ▸ encodesTable_tableCode Ra0407.cycles } 97278
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0408.table, code := 4256324760005858585726378150082121793,
        encodes := Ra0408.tableCode_eq ▸ encodesTable_tableCode Ra0408.cycles } 97279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0409.table, code := 4172842280344171502366869787353813057,
        encodes := Ra0409.tableCode_eq ▸ encodesTable_tableCode Ra0409.cycles } 97910
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0410.table, code := 4172842280344171502366869789501296705,
        encodes := Ra0410.tableCode_eq ▸ encodesTable_tableCode Ra0410.cycles } 97911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0411.table, code := 4172923409982586109048635962283003969,
        encodes := Ra0411.tableCode_eq ▸ encodesTable_tableCode Ra0411.cycles } 97918
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0412.table, code := 4172923409982586109048635964430487617,
        encodes := Ra0412.tableCode_eq ▸ encodesTable_tableCode Ra0412.cycles } 97919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0413.table, code := 4170165004759620753527532908011851841,
        encodes := Ra0413.tableCode_eq ▸ encodesTable_tableCode Ra0413.cycles } 97976
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0414.table, code := 4170165004759620753527532910159335489,
        encodes := Ra0414.tableCode_eq ▸ encodesTable_tableCode Ra0414.cycles } 97977
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0415.table, code := 4172842282829722987494556166642733121,
        encodes := Ra0415.tableCode_eq ▸ encodesTable_tableCode Ra0415.cycles } 98038
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0416.table, code := 4172842282829722987494556168790216769,
        encodes := Ra0416.tableCode_eq ▸ encodesTable_tableCode Ra0416.cycles } 98039
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0417.table, code := 4172923412468137594176322341571924033,
        encodes := Ra0417.tableCode_eq ▸ encodesTable_tableCode Ra0417.cycles } 98046
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0418.table, code := 4172923412468137594176322343719407681,
        encodes := Ra0418.tableCode_eq ▸ encodesTable_tableCode Ra0418.cycles } 98047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0419.table, code := 4253566349814208113822919151799504961,
        encodes := Ra0419.tableCode_eq ▸ encodesTable_tableCode Ra0419.cycles } 98094
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0420.table, code := 4253566349814208113822919153946988609,
        encodes := Ra0420.tableCode_eq ▸ encodesTable_tableCode Ra0420.cycles } 98095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0421.table, code := 4253485220173375657951879847783698497,
        encodes := Ra0421.tableCode_eq ▸ encodesTable_tableCode Ra0421.cycles } 98099
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0422.table, code := 4253566349814208116272877486528008257,
        encodes := Ra0422.tableCode_eq ▸ encodesTable_tableCode Ra0422.cycles } 98110
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0423.table, code := 4253566349814208116272877488675491905,
        encodes := Ra0423.tableCode_eq ▸ encodesTable_tableCode Ra0423.cycles } 98111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0424.table, code := 4256243627881892496078653277415411777,
        encodes := Ra0424.tableCode_eq ▸ encodesTable_tableCode Ra0424.cycles } 98150
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0425.table, code := 4256243627881892496078653279562895425,
        encodes := Ra0425.tableCode_eq ▸ encodesTable_tableCode Ra0425.cycles } 98151
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0426.table, code := 4256324757520307102760419452344602689,
        encodes := Ra0426.tableCode_eq ▸ encodesTable_tableCode Ra0426.cycles } 98158
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0427.table, code := 4256324757520307102760419454492086337,
        encodes := Ra0427.tableCode_eq ▸ encodesTable_tableCode Ra0427.cycles } 98159
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0428.table, code := 4256243627881892498528611612143915073,
        encodes := Ra0428.tableCode_eq ▸ encodesTable_tableCode Ra0428.cycles } 98166
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0429.table, code := 4256243627881892498528611614291398721,
        encodes := Ra0429.tableCode_eq ▸ encodesTable_tableCode Ra0429.cycles } 98167
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0430.table, code := 4256324757520307105210377787073105985,
        encodes := Ra0430.tableCode_eq ▸ encodesTable_tableCode Ra0430.cycles } 98174
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0431.table, code := 4256324757520307105210377789220589633,
        encodes := Ra0431.tableCode_eq ▸ encodesTable_tableCode Ra0431.cycles } 98175
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0432.table, code := 4253485222658927140629607890196631617,
        encodes := Ra0432.tableCode_eq ▸ encodesTable_tableCode Ra0432.cycles } 98210
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0433.table, code := 4253485222658927140629607892344115265,
        encodes := Ra0433.tableCode_eq ▸ encodesTable_tableCode Ra0433.cycles } 98211
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0434.table, code := 4253566352299759598950605531088425025,
        encodes := Ra0434.tableCode_eq ▸ encodesTable_tableCode Ra0434.cycles } 98222
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0435.table, code := 4253566352299759598950605533235908673,
        encodes := Ra0435.tableCode_eq ▸ encodesTable_tableCode Ra0435.cycles } 98223
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0436.table, code := 4253485222658927143079566224925134913,
        encodes := Ra0436.tableCode_eq ▸ encodesTable_tableCode Ra0436.cycles } 98226
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0437.table, code := 4253485222658927143079566227072618561,
        encodes := Ra0437.tableCode_eq ▸ encodesTable_tableCode Ra0437.cycles } 98227
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0438.table, code := 4253566352299759601400563865816928321,
        encodes := Ra0438.tableCode_eq ▸ encodesTable_tableCode Ra0438.cycles } 98238
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0439.table, code := 4253566352299759601400563867964411969,
        encodes := Ra0439.tableCode_eq ▸ encodesTable_tableCode Ra0439.cycles } 98239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0440.table, code := 4256243630367443981206339656704331841,
        encodes := Ra0440.tableCode_eq ▸ encodesTable_tableCode Ra0440.cycles } 98278
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0441.table, code := 4256243630367443981206339658851815489,
        encodes := Ra0441.tableCode_eq ▸ encodesTable_tableCode Ra0441.cycles } 98279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0442.table, code := 4256324760005858587888105831633522753,
        encodes := Ra0442.tableCode_eq ▸ encodesTable_tableCode Ra0442.cycles } 98286
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0443.table, code := 4256324760005858587888105833781006401,
        encodes := Ra0443.tableCode_eq ▸ encodesTable_tableCode Ra0443.cycles } 98287
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0444.table, code := 4256243630367443983656297991432835137,
        encodes := Ra0444.tableCode_eq ▸ encodesTable_tableCode Ra0444.cycles } 98294
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0445.table, code := 4256243630367443983656297993580318785,
        encodes := Ra0445.tableCode_eq ▸ encodesTable_tableCode Ra0445.cycles } 98295
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0446.table, code := 4256324760005858590338064166362026049,
        encodes := Ra0446.tableCode_eq ▸ encodesTable_tableCode Ra0446.cycles } 98302
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0447.table, code := 4256324760005858590338064168509509697,
        encodes := Ra0447.tableCode_eq ▸ encodesTable_tableCode Ra0447.cycles } 98303
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0448.table, code := 9412275376039663367102641627549929537,
        encodes := Ra0448.tableCode_eq ▸ encodesTable_tableCode Ra0448.cycles } 100351
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (384 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (384 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
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

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models006
