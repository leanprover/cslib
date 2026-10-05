/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0321
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0322
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0323
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0324
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0325
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0326
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0327
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0328
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0329
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0330
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0331
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0332
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0333
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0334
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0335
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0336
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0337
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0338
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0339
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0340
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0341
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0342
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0343
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0344
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0345
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0346
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0347
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0348
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0349
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0350
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0351
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0352
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0353
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0354
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0355
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0356
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0357
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0358
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0359
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0360
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0361
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0362
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0363
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0364
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0365
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0366
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0367
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0368
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0369
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0370
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0371
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0372
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0373
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0374
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0375
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0376
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0377
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0378
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0379
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0380
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0381
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0382
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0383
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0384

/-!
# Certified models 321–384 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models005

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0321.table, code := 4256324752259061643099606439399002177,
        encodes := Ra0321.tableCode_eq ▸ encodesTable_tableCode Ra0321.cycles } 89982
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0322.table, code := 4256324752259061643099606441546485825,
        encodes := Ra0322.tableCode_eq ▸ encodesTable_tableCode Ra0322.cycles } 89983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0323.table, code := 4253485217397681678518836542522527809,
        encodes := Ra0323.tableCode_eq ▸ encodesTable_tableCode Ra0323.cycles } 90018
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0324.table, code := 4253485217397681678518836544670011457,
        encodes := Ra0324.tableCode_eq ▸ encodesTable_tableCode Ra0324.cycles } 90019
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0325.table, code := 4253566347038514136839834183414321217,
        encodes := Ra0325.tableCode_eq ▸ encodesTable_tableCode Ra0325.cycles } 90030
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0326.table, code := 4253566347038514136839834185561804865,
        encodes := Ra0326.tableCode_eq ▸ encodesTable_tableCode Ra0326.cycles } 90031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0327.table, code := 4253485217397681680968794877251031105,
        encodes := Ra0327.tableCode_eq ▸ encodesTable_tableCode Ra0327.cycles } 90034
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0328.table, code := 4253485217397681680968794879398514753,
        encodes := Ra0328.tableCode_eq ▸ encodesTable_tableCode Ra0328.cycles } 90035
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0329.table, code := 4253566347038514139289792518142824513,
        encodes := Ra0329.tableCode_eq ▸ encodesTable_tableCode Ra0329.cycles } 90046
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0330.table, code := 4253566347038514139289792520290308161,
        encodes := Ra0330.tableCode_eq ▸ encodesTable_tableCode Ra0330.cycles } 90047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0331.table, code := 4256243625106198519095568309030228033,
        encodes := Ra0331.tableCode_eq ▸ encodesTable_tableCode Ra0331.cycles } 90086
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0332.table, code := 4256243625106198519095568311177711681,
        encodes := Ra0332.tableCode_eq ▸ encodesTable_tableCode Ra0332.cycles } 90087
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0333.table, code := 4256324754744613125777334483959418945,
        encodes := Ra0333.tableCode_eq ▸ encodesTable_tableCode Ra0333.cycles } 90094
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0334.table, code := 4256324754744613125777334486106902593,
        encodes := Ra0334.tableCode_eq ▸ encodesTable_tableCode Ra0334.cycles } 90095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0335.table, code := 4256243625106198521545526643758731329,
        encodes := Ra0335.tableCode_eq ▸ encodesTable_tableCode Ra0335.cycles } 90102
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0336.table, code := 4256243625106198521545526645906214977,
        encodes := Ra0336.tableCode_eq ▸ encodesTable_tableCode Ra0336.cycles } 90103
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0337.table, code := 4256324754744613128227292818687922241,
        encodes := Ra0337.tableCode_eq ▸ encodesTable_tableCode Ra0337.cycles } 90110
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0338.table, code := 4256324754744613128227292820835405889,
        encodes := Ra0338.tableCode_eq ▸ encodesTable_tableCode Ra0338.cycles } 90111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0339.table, code := 4164891578180459548595003165604319297,
        encodes := Ra0339.tableCode_eq ▸ encodesTable_tableCode Ra0339.cycles } 93840
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0340.table, code := 4164891578180459548595003167751802945,
        encodes := Ra0340.tableCode_eq ▸ encodesTable_tableCode Ra0340.cycles } 93841
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0341.table, code := 4251051331023352927636895837731426369,
        encodes := Ra0341.tableCode_eq ▸ encodesTable_tableCode Ra0341.cycles } 94054
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0342.table, code := 4251051331023352927636895839878910017,
        encodes := Ra0342.tableCode_eq ▸ encodesTable_tableCode Ra0342.cycles } 94055
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0343.table, code := 4251132460661767534318662012660617281,
        encodes := Ra0343.tableCode_eq ▸ encodesTable_tableCode Ra0343.cycles } 94062
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0344.table, code := 4251132460661767534318662014808100929,
        encodes := Ra0344.tableCode_eq ▸ encodesTable_tableCode Ra0344.cycles } 94063
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0345.table, code := 4251051331023352930086854172459929665,
        encodes := Ra0345.tableCode_eq ▸ encodesTable_tableCode Ra0345.cycles } 94070
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0346.table, code := 4251051331023352930086854174607413313,
        encodes := Ra0346.tableCode_eq ▸ encodesTable_tableCode Ra0346.cycles } 94071
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0347.table, code := 4251132460661767536768620347389120577,
        encodes := Ra0347.tableCode_eq ▸ encodesTable_tableCode Ra0347.cycles } 94078
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0348.table, code := 4251132460661767536768620349536604225,
        encodes := Ra0348.tableCode_eq ▸ encodesTable_tableCode Ra0348.cycles } 94079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0349.table, code := 4251051333508904415214540551748849729,
        encodes := Ra0349.tableCode_eq ▸ encodesTable_tableCode Ra0349.cycles } 94198
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0350.table, code := 4251051333508904415214540553896333377,
        encodes := Ra0350.tableCode_eq ▸ encodesTable_tableCode Ra0350.cycles } 94199
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0351.table, code := 4251132463147319021896306726678040641,
        encodes := Ra0351.tableCode_eq ▸ encodesTable_tableCode Ra0351.cycles } 94206
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0352.table, code := 4251132463147319021896306728825524289,
        encodes := Ra0352.tableCode_eq ▸ encodesTable_tableCode Ra0352.cycles } 94207
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0353.table, code := 4253485220018632991632196668462731329,
        encodes := Ra0353.tableCode_eq ▸ encodesTable_tableCode Ra0353.cycles } 95027
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0354.table, code := 4253566349659465449953194307207041089,
        encodes := Ra0354.tableCode_eq ▸ encodesTable_tableCode Ra0354.cycles } 95038
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0355.table, code := 4253566349659465449953194309354524737,
        encodes := Ra0355.tableCode_eq ▸ encodesTable_tableCode Ra0355.cycles } 95039
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0356.table, code := 4256243627727149832208928432822947905,
        encodes := Ra0356.tableCode_eq ▸ encodesTable_tableCode Ra0356.cycles } 95094
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0357.table, code := 4256243627727149832208928434970431553,
        encodes := Ra0357.tableCode_eq ▸ encodesTable_tableCode Ra0357.cycles } 95095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0358.table, code := 4256324757365564438890694607752138817,
        encodes := Ra0358.tableCode_eq ▸ encodesTable_tableCode Ra0358.cycles } 95102
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0359.table, code := 4256324757365564438890694609899622465,
        encodes := Ra0359.tableCode_eq ▸ encodesTable_tableCode Ra0359.cycles } 95103
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0360.table, code := 4253485222504184476759883047751651393,
        encodes := Ra0360.tableCode_eq ▸ encodesTable_tableCode Ra0360.cycles } 95155
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0361.table, code := 4253566352145016935080880686495961153,
        encodes := Ra0361.tableCode_eq ▸ encodesTable_tableCode Ra0361.cycles } 95166
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0362.table, code := 4253566352145016935080880688643444801,
        encodes := Ra0362.tableCode_eq ▸ encodesTable_tableCode Ra0362.cycles } 95167
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0363.table, code := 4256243630212701317336614812111867969,
        encodes := Ra0363.tableCode_eq ▸ encodesTable_tableCode Ra0363.cycles } 95222
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0364.table, code := 4256243630212701317336614814259351617,
        encodes := Ra0364.tableCode_eq ▸ encodesTable_tableCode Ra0364.cycles } 95223
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0365.table, code := 4256324759851115924018380987041058881,
        encodes := Ra0365.tableCode_eq ▸ encodesTable_tableCode Ra0365.cycles } 95230
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0366.table, code := 4256324759851115924018380989188542529,
        encodes := Ra0366.tableCode_eq ▸ encodesTable_tableCode Ra0366.cycles } 95231
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0367.table, code := 4253566349659465452114921990905925697,
        encodes := Ra0367.tableCode_eq ▸ encodesTable_tableCode Ra0367.cycles } 96046
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0368.table, code := 4253566349659465452114921993053409345,
        encodes := Ra0368.tableCode_eq ▸ encodesTable_tableCode Ra0368.cycles } 96047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0369.table, code := 4253485220018632996243882686890119233,
        encodes := Ra0369.tableCode_eq ▸ encodesTable_tableCode Ra0369.cycles } 96051
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0370.table, code := 4253566349659465454564880325634428993,
        encodes := Ra0370.tableCode_eq ▸ encodesTable_tableCode Ra0370.cycles } 96062
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0371.table, code := 4253566349659465454564880327781912641,
        encodes := Ra0371.tableCode_eq ▸ encodesTable_tableCode Ra0371.cycles } 96063
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0372.table, code := 4256243627727149834370656116521832513,
        encodes := Ra0372.tableCode_eq ▸ encodesTable_tableCode Ra0372.cycles } 96102
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0373.table, code := 4256243627727149834370656118669316161,
        encodes := Ra0373.tableCode_eq ▸ encodesTable_tableCode Ra0373.cycles } 96103
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0374.table, code := 4256324757365564441052422291451023425,
        encodes := Ra0374.tableCode_eq ▸ encodesTable_tableCode Ra0374.cycles } 96110
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0375.table, code := 4256324757365564441052422293598507073,
        encodes := Ra0375.tableCode_eq ▸ encodesTable_tableCode Ra0375.cycles } 96111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0376.table, code := 4256243627727149836820614451250335809,
        encodes := Ra0376.tableCode_eq ▸ encodesTable_tableCode Ra0376.cycles } 96118
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0377.table, code := 4256243627727149836820614453397819457,
        encodes := Ra0377.tableCode_eq ▸ encodesTable_tableCode Ra0377.cycles } 96119
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0378.table, code := 4256324757365564443502380626179526721,
        encodes := Ra0378.tableCode_eq ▸ encodesTable_tableCode Ra0378.cycles } 96126
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0379.table, code := 4256324757365564443502380628327010369,
        encodes := Ra0379.tableCode_eq ▸ encodesTable_tableCode Ra0379.cycles } 96127
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0380.table, code := 4253485222504184478921610731450536001,
        encodes := Ra0380.tableCode_eq ▸ encodesTable_tableCode Ra0380.cycles } 96163
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0381.table, code := 4253566352145016937242608370194845761,
        encodes := Ra0381.tableCode_eq ▸ encodesTable_tableCode Ra0381.cycles } 96174
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0382.table, code := 4253566352145016937242608372342329409,
        encodes := Ra0382.tableCode_eq ▸ encodesTable_tableCode Ra0382.cycles } 96175
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0383.table, code := 4253485222504184481371569066179039297,
        encodes := Ra0383.tableCode_eq ▸ encodesTable_tableCode Ra0383.cycles } 96179
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0384.table, code := 4253566352145016939692566704923349057,
        encodes := Ra0384.tableCode_eq ▸ encodesTable_tableCode Ra0384.cycles } 96190
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (320 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (320 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (320 + i.val) 0 ≤ Data.profiles (320 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (320 + i.val) 0 = Data.canonicalMask (320 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (320 + i.val) < Data.canonicalMask (320 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (320 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models005
