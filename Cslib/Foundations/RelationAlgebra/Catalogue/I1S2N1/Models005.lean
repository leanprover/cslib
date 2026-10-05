/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0321
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0322
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0323
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0324
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0325
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0326
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0327
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0328
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0329
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0330
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0331
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0332
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0333
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0334
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0335
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0336
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0337
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0338
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0339
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0340
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0341
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0342
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0343
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0344
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0345
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0346
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0347
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0348
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0349
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0350
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0351
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0352
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0353
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0354
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0355
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0356
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0357
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0358
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0359
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0360
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0361
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0362
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0363
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0364
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0365
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0366
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0367
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0368
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0369
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0370
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0371
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0372
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0373
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0374
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0375
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0376
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0377
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0378
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0379
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0380
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0381
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0382
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0383
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0384

/-!
# Certified models 321–384 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models005

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0321.table, code := 27725182869882679208405144946042212417,
        encodes := Ra0321.tableCode_eq ▸ encodesTable_tableCode Ra0321.cycles } 22399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0322.table, code := 30381204974713086253877929475892842561,
        encodes := Ra0322.tableCode_eq ▸ encodesTable_tableCode Ra0322.cycles } 22478
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0323.table, code := 30381204974713086253877929478040326209,
        encodes := Ra0323.tableCode_eq ▸ encodesTable_tableCode Ra0323.cycles } 22479
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0324.table, code := 30381367234067289081384306514082402369,
        encodes := Ra0324.tableCode_eq ▸ encodesTable_tableCode Ra0324.cycles } 22492
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0325.table, code := 30381367234067289081384306516229886017,
        encodes := Ra0325.tableCode_eq ▸ encodesTable_tableCode Ra0325.cycles } 22493
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0326.table, code := 30381367234067289081456364181134774337,
        encodes := Ra0326.tableCode_eq ▸ encodesTable_tableCode Ra0326.cycles } 22494
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0327.table, code := 30381367234067289081456364183282257985,
        encodes := Ra0327.tableCode_eq ▸ encodesTable_tableCode Ra0327.cycles } 22495
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0328.table, code := 30383882252860559811781422263707111489,
        encodes := Ra0328.tableCode_eq ▸ encodesTable_tableCode Ra0328.cycles } 22513
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0329.table, code := 30383882252860559811853479928611999809,
        encodes := Ra0329.tableCode_eq ▸ encodesTable_tableCode Ra0329.cycles } 22514
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0330.table, code := 30383882252860559811853479930759483457,
        encodes := Ra0330.tableCode_eq ▸ encodesTable_tableCode Ra0330.cycles } 22515
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0331.table, code := 30383963382501392270102419902451421249,
        encodes := Ra0331.tableCode_eq ▸ encodesTable_tableCode Ra0331.cycles } 22516
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0332.table, code := 30383963382501392270102419904598904897,
        encodes := Ra0332.tableCode_eq ▸ encodesTable_tableCode Ra0332.cycles } 22517
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0333.table, code := 30383963382501392270174477569503793217,
        encodes := Ra0333.tableCode_eq ▸ encodesTable_tableCode Ra0333.cycles } 22518
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0334.table, code := 30383963382501392270174477571651276865,
        encodes := Ra0334.tableCode_eq ▸ encodesTable_tableCode Ra0334.cycles } 22519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0335.table, code := 30383882252860559814231380598435614785,
        encodes := Ra0335.tableCode_eq ▸ encodesTable_tableCode Ra0335.cycles } 22521
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0336.table, code := 30383882252860559814303438263340503105,
        encodes := Ra0336.tableCode_eq ▸ encodesTable_tableCode Ra0336.cycles } 22522
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0337.table, code := 30383882252860559814303438265487986753,
        encodes := Ra0337.tableCode_eq ▸ encodesTable_tableCode Ra0337.cycles } 22523
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0338.table, code := 30383963382501392272552378237179924545,
        encodes := Ra0338.tableCode_eq ▸ encodesTable_tableCode Ra0338.cycles } 22524
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0339.table, code := 30383963382501392272552378239327408193,
        encodes := Ra0339.tableCode_eq ▸ encodesTable_tableCode Ra0339.cycles } 22525
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0340.table, code := 30383963382501392272624435904232296513,
        encodes := Ra0340.tableCode_eq ▸ encodesTable_tableCode Ra0340.cycles } 22526
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0341.table, code := 30383963382501392272624435906379780161,
        encodes := Ra0341.tableCode_eq ▸ encodesTable_tableCode Ra0341.cycles } 22527
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0342.table, code := 30316463681632346023367672045313986625,
        encodes := Ra0342.tableCode_eq ▸ encodesTable_tableCode Ra0342.cycles } 22780
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0343.table, code := 30316463681632346023367672047461470273,
        encodes := Ra0343.tableCode_eq ▸ encodesTable_tableCode Ra0343.cycles } 22781
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0344.table, code := 30316463681632346023439729712366358593,
        encodes := Ra0344.tableCode_eq ▸ encodesTable_tableCode Ra0344.cycles } 22782
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0345.table, code := 30316463681632346023439729714513842241,
        encodes := Ra0345.tableCode_eq ▸ encodesTable_tableCode Ra0345.cycles } 22783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0346.table, code := 30398891315043095304263727268254453825,
        encodes := Ra0346.tableCode_eq ▸ encodesTable_tableCode Ra0346.cycles } 22972
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0347.table, code := 30398891315043095304263727270401937473,
        encodes := Ra0347.tableCode_eq ▸ encodesTable_tableCode Ra0347.cycles } 22973
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0348.table, code := 30398891315043095304335784935306825793,
        encodes := Ra0348.tableCode_eq ▸ encodesTable_tableCode Ra0348.cycles } 22974
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0349.table, code := 30398891315043095304335784937454309441,
        encodes := Ra0349.tableCode_eq ▸ encodesTable_tableCode Ra0349.cycles } 22975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0350.table, code := 30399540431378574671981639969932578881,
        encodes := Ra0350.tableCode_eq ▸ encodesTable_tableCode Ra0350.cycles } 23036
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0351.table, code := 30399540431378574671981639972080062529,
        encodes := Ra0351.tableCode_eq ▸ encodesTable_tableCode Ra0351.cycles } 23037
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0352.table, code := 30399540431378574672053697636984950849,
        encodes := Ra0352.tableCode_eq ▸ encodesTable_tableCode Ra0352.cycles } 23038
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0353.table, code := 30399540431378574672053697639132434497,
        encodes := Ra0353.tableCode_eq ▸ encodesTable_tableCode Ra0353.cycles } 23039
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0354.table, code := 30316463681632346025529399729012871233,
        encodes := Ra0354.tableCode_eq ▸ encodesTable_tableCode Ra0354.cycles } 23284
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0355.table, code := 30316463681632346025529399731160354881,
        encodes := Ra0355.tableCode_eq ▸ encodesTable_tableCode Ra0355.cycles } 23285
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0356.table, code := 30316463681632346025601457396065243201,
        encodes := Ra0356.tableCode_eq ▸ encodesTable_tableCode Ra0356.cycles } 23286
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0357.table, code := 30316463681632346025601457398212726849,
        encodes := Ra0357.tableCode_eq ▸ encodesTable_tableCode Ra0357.cycles } 23287
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0358.table, code := 30316463681632346027979358063741374529,
        encodes := Ra0358.tableCode_eq ▸ encodesTable_tableCode Ra0358.cycles } 23292
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0359.table, code := 30316463681632346027979358065888858177,
        encodes := Ra0359.tableCode_eq ▸ encodesTable_tableCode Ra0359.cycles } 23293
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0360.table, code := 30316463681632346028051415730793746497,
        encodes := Ra0360.tableCode_eq ▸ encodesTable_tableCode Ra0360.cycles } 23294
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0361.table, code := 30316463681632346028051415732941230145,
        encodes := Ra0361.tableCode_eq ▸ encodesTable_tableCode Ra0361.cycles } 23295
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0362.table, code := 30398891315043095306425454951953338433,
        encodes := Ra0362.tableCode_eq ▸ encodesTable_tableCode Ra0362.cycles } 23476
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0363.table, code := 30398891315043095306425454954100822081,
        encodes := Ra0363.tableCode_eq ▸ encodesTable_tableCode Ra0363.cycles } 23477
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0364.table, code := 30398891315043095306497512619005710401,
        encodes := Ra0364.tableCode_eq ▸ encodesTable_tableCode Ra0364.cycles } 23478
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0365.table, code := 30398891315043095306497512621153194049,
        encodes := Ra0365.tableCode_eq ▸ encodesTable_tableCode Ra0365.cycles } 23479
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0366.table, code := 30398891315043095308875413286681841729,
        encodes := Ra0366.tableCode_eq ▸ encodesTable_tableCode Ra0366.cycles } 23484
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0367.table, code := 30398891315043095308875413288829325377,
        encodes := Ra0367.tableCode_eq ▸ encodesTable_tableCode Ra0367.cycles } 23485
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0368.table, code := 30398891315043095308947470953734213697,
        encodes := Ra0368.tableCode_eq ▸ encodesTable_tableCode Ra0368.cycles } 23486
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0369.table, code := 30398891315043095308947470955881697345,
        encodes := Ra0369.tableCode_eq ▸ encodesTable_tableCode Ra0369.cycles } 23487
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0370.table, code := 30399459301737742215822370014887153729,
        encodes := Ra0370.tableCode_eq ▸ encodesTable_tableCode Ra0370.cycles } 23537
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0371.table, code := 30399459301737742215894427681939525697,
        encodes := Ra0371.tableCode_eq ▸ encodesTable_tableCode Ra0371.cycles } 23539
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0372.table, code := 30399540431378574674143367653631463489,
        encodes := Ra0372.tableCode_eq ▸ encodesTable_tableCode Ra0372.cycles } 23540
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0373.table, code := 30399540431378574674143367655778947137,
        encodes := Ra0373.tableCode_eq ▸ encodesTable_tableCode Ra0373.cycles } 23541
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0374.table, code := 30399540431378574674215425320683835457,
        encodes := Ra0374.tableCode_eq ▸ encodesTable_tableCode Ra0374.cycles } 23542
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0375.table, code := 30399540431378574674215425322831319105,
        encodes := Ra0375.tableCode_eq ▸ encodesTable_tableCode Ra0375.cycles } 23543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0376.table, code := 30399459301737742218272328349615657025,
        encodes := Ra0376.tableCode_eq ▸ encodesTable_tableCode Ra0376.cycles } 23545
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0377.table, code := 30399459301737742218344386016668028993,
        encodes := Ra0377.tableCode_eq ▸ encodesTable_tableCode Ra0377.cycles } 23547
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0378.table, code := 30399540431378574676593325988359966785,
        encodes := Ra0378.tableCode_eq ▸ encodesTable_tableCode Ra0378.cycles } 23548
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0379.table, code := 30399540431378574676593325990507450433,
        encodes := Ra0379.tableCode_eq ▸ encodesTable_tableCode Ra0379.cycles } 23549
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0380.table, code := 30399540431378574676665383655412338753,
        encodes := Ra0380.tableCode_eq ▸ encodesTable_tableCode Ra0380.cycles } 23550
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0381.table, code := 30399540431378574676665383657559822401,
        encodes := Ra0381.tableCode_eq ▸ encodesTable_tableCode Ra0381.cycles } 23551
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0382.table, code := 30319059830211525059971454255117897793,
        encodes := Ra0382.tableCode_eq ▸ encodesTable_tableCode Ra0382.cycles } 23766
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0383.table, code := 30319059830211525059971454257265381441,
        encodes := Ra0383.tableCode_eq ▸ encodesTable_tableCode Ra0383.cycles } 23767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0384.table, code := 30319059830211525062421412589846401089,
        encodes := Ra0384.tableCode_eq ▸ encodesTable_tableCode Ra0384.cycles } 23774
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (320 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (320 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
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

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models005
