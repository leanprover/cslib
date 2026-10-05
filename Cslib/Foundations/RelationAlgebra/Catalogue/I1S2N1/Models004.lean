/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0257
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0258
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0259
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0260
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0261
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0262
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0263
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0264
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0265
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0266
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0267
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0268
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0269
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0270
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0271
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0272
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0273
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0274
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0275
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0276
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0277
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0278
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0279
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0280
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0281
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0282
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0283
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0284
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0285
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0286
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0287
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0288
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0289
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0290
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0291
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0292
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0293
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0294
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0295
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0296
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0297
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0298
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0299
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0300
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0301
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0302
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0303
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0304
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0305
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0306
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0307
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0308
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0309
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0310
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0311
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0312
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0313
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0314
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0315
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0316
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0317
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0318
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0319
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0320

/-!
# Certified models 257–320 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models004

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0257.table, code := 27725182869882679201271442923686465601,
        encodes := Ra0257.tableCode_eq ▸ encodesTable_tableCode Ra0257.cycles } 21876
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0258.table, code := 27725182869882679201271442925833949249,
        encodes := Ra0258.tableCode_eq ▸ encodesTable_tableCode Ra0258.cycles } 21877
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0259.table, code := 27725182869882679201343500590738837569,
        encodes := Ra0259.tableCode_eq ▸ encodesTable_tableCode Ra0259.cycles } 21878
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0260.table, code := 27725182869882679201343500592886321217,
        encodes := Ra0260.tableCode_eq ▸ encodesTable_tableCode Ra0260.cycles } 21879
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0261.table, code := 27725101740241846745472461284575547457,
        encodes := Ra0261.tableCode_eq ▸ encodesTable_tableCode Ra0261.cycles } 21882
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0262.table, code := 27725101740241846745472461286723031105,
        encodes := Ra0262.tableCode_eq ▸ encodesTable_tableCode Ra0262.cycles } 21883
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0263.table, code := 27725182869882679203721401258414968897,
        encodes := Ra0263.tableCode_eq ▸ encodesTable_tableCode Ra0263.cycles } 21884
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0264.table, code := 27725182869882679203721401260562452545,
        encodes := Ra0264.tableCode_eq ▸ encodesTable_tableCode Ra0264.cycles } 21885
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0265.table, code := 27725182869882679203793458925467340865,
        encodes := Ra0265.tableCode_eq ▸ encodesTable_tableCode Ra0265.cycles } 21886
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0266.table, code := 27725182869882679203793458927614824513,
        encodes := Ra0266.tableCode_eq ▸ encodesTable_tableCode Ra0266.cycles } 21887
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0267.table, code := 30381204974713086249266243457465454657,
        encodes := Ra0267.tableCode_eq ▸ encodesTable_tableCode Ra0267.cycles } 21966
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0268.table, code := 30381204974713086249266243459612938305,
        encodes := Ra0268.tableCode_eq ▸ encodesTable_tableCode Ra0268.cycles } 21967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0269.table, code := 30381367234067289076772620495655014465,
        encodes := Ra0269.tableCode_eq ▸ encodesTable_tableCode Ra0269.cycles } 21980
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0270.table, code := 30381367234067289076772620497802498113,
        encodes := Ra0270.tableCode_eq ▸ encodesTable_tableCode Ra0270.cycles } 21981
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0271.table, code := 30381367234067289076844678162707386433,
        encodes := Ra0271.tableCode_eq ▸ encodesTable_tableCode Ra0271.cycles } 21982
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0272.table, code := 30381367234067289076844678164854870081,
        encodes := Ra0272.tableCode_eq ▸ encodesTable_tableCode Ra0272.cycles } 21983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0273.table, code := 30383882252860559807169736245279723585,
        encodes := Ra0273.tableCode_eq ▸ encodesTable_tableCode Ra0273.cycles } 22001
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0274.table, code := 30383882252860559807241793910184611905,
        encodes := Ra0274.tableCode_eq ▸ encodesTable_tableCode Ra0274.cycles } 22002
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0275.table, code := 30383882252860559807241793912332095553,
        encodes := Ra0275.tableCode_eq ▸ encodesTable_tableCode Ra0275.cycles } 22003
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0276.table, code := 30383963382501392265490733884024033345,
        encodes := Ra0276.tableCode_eq ▸ encodesTable_tableCode Ra0276.cycles } 22004
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0277.table, code := 30383963382501392265490733886171516993,
        encodes := Ra0277.tableCode_eq ▸ encodesTable_tableCode Ra0277.cycles } 22005
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0278.table, code := 30383963382501392265562791551076405313,
        encodes := Ra0278.tableCode_eq ▸ encodesTable_tableCode Ra0278.cycles } 22006
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0279.table, code := 30383963382501392265562791553223888961,
        encodes := Ra0279.tableCode_eq ▸ encodesTable_tableCode Ra0279.cycles } 22007
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0280.table, code := 30383882252860559809619694580008226881,
        encodes := Ra0280.tableCode_eq ▸ encodesTable_tableCode Ra0280.cycles } 22009
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0281.table, code := 30383882252860559809691752244913115201,
        encodes := Ra0281.tableCode_eq ▸ encodesTable_tableCode Ra0281.cycles } 22010
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0282.table, code := 30383882252860559809691752247060598849,
        encodes := Ra0282.tableCode_eq ▸ encodesTable_tableCode Ra0282.cycles } 22011
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0283.table, code := 30383963382501392267940692218752536641,
        encodes := Ra0283.tableCode_eq ▸ encodesTable_tableCode Ra0283.cycles } 22012
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0284.table, code := 30383963382501392267940692220900020289,
        encodes := Ra0284.tableCode_eq ▸ encodesTable_tableCode Ra0284.cycles } 22013
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0285.table, code := 30383963382501392268012749885804908609,
        encodes := Ra0285.tableCode_eq ▸ encodesTable_tableCode Ra0285.cycles } 22014
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0286.table, code := 30383963382501392268012749887952392257,
        encodes := Ra0286.tableCode_eq ▸ encodesTable_tableCode Ra0286.cycles } 22015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0287.table, code := 30300237516419684253770539278302187585,
        encodes := Ra0287.tableCode_eq ▸ encodesTable_tableCode Ra0287.cycles } 22197
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0288.table, code := 30300237516419684253842596945354559553,
        encodes := Ra0288.tableCode_eq ▸ encodesTable_tableCode Ra0288.cycles } 22199
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0289.table, code := 30300237516419684256292555280083062849,
        encodes := Ra0289.tableCode_eq ▸ encodesTable_tableCode Ra0289.cycles } 22207
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0290.table, code := 30300724373400960796359975607319400513,
        encodes := Ra0290.tableCode_eq ▸ encodesTable_tableCode Ra0290.cycles } 22252
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0291.table, code := 30300724373400960796359975609466884161,
        encodes := Ra0291.tableCode_eq ▸ encodesTable_tableCode Ra0291.cycles } 22253
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0292.table, code := 30300724373400960796432033274371772481,
        encodes := Ra0292.tableCode_eq ▸ encodesTable_tableCode Ra0292.cycles } 22254
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0293.table, code := 30300724373400960796432033276519256129,
        encodes := Ra0293.tableCode_eq ▸ encodesTable_tableCode Ra0293.cycles } 22255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0294.table, code := 30300805503114331163167454339088519233,
        encodes := Ra0294.tableCode_eq ▸ encodesTable_tableCode Ra0294.cycles } 22257
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0295.table, code := 30300805503114331163239512003993407553,
        encodes := Ra0295.tableCode_eq ▸ encodesTable_tableCode Ra0295.cycles } 22258
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0296.table, code := 30300805503114331163239512006140891201,
        encodes := Ra0296.tableCode_eq ▸ encodesTable_tableCode Ra0296.cycles } 22259
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0297.table, code := 30300886632755163621488451977832828993,
        encodes := Ra0297.tableCode_eq ▸ encodesTable_tableCode Ra0297.cycles } 22260
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0298.table, code := 30300886632755163621488451979980312641,
        encodes := Ra0298.tableCode_eq ▸ encodesTable_tableCode Ra0298.cycles } 22261
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0299.table, code := 30300886632755163621560509644885200961,
        encodes := Ra0299.tableCode_eq ▸ encodesTable_tableCode Ra0299.cycles } 22262
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0300.table, code := 30300886632755163621560509647032684609,
        encodes := Ra0300.tableCode_eq ▸ encodesTable_tableCode Ra0300.cycles } 22263
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0301.table, code := 30300805503114331165617412673817022529,
        encodes := Ra0301.tableCode_eq ▸ encodesTable_tableCode Ra0301.cycles } 22265
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0302.table, code := 30300805503114331165689470338721910849,
        encodes := Ra0302.tableCode_eq ▸ encodesTable_tableCode Ra0302.cycles } 22266
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0303.table, code := 30300805503114331165689470340869394497,
        encodes := Ra0303.tableCode_eq ▸ encodesTable_tableCode Ra0303.cycles } 22267
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0304.table, code := 30300886632755163623938410312561332289,
        encodes := Ra0304.tableCode_eq ▸ encodesTable_tableCode Ra0304.cycles } 22268
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0305.table, code := 30300886632755163623938410314708815937,
        encodes := Ra0305.tableCode_eq ▸ encodesTable_tableCode Ra0305.cycles } 22269
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0306.table, code := 30300886632755163624010467979613704257,
        encodes := Ra0306.tableCode_eq ▸ encodesTable_tableCode Ra0306.cycles } 22270
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0307.table, code := 30300886632755163624010467981761187905,
        encodes := Ra0307.tableCode_eq ▸ encodesTable_tableCode Ra0307.cycles } 22271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0308.table, code := 27722343332453540731265583207611109441,
        encodes := Ra0308.tableCode_eq ▸ encodesTable_tableCode Ra0308.cycles } 22344
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0309.table, code := 27722343332453540731265583209758593089,
        encodes := Ra0309.tableCode_eq ▸ encodesTable_tableCode Ra0309.cycles } 22345
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0310.table, code := 27725101740241846747634188968274432065,
        encodes := Ra0310.tableCode_eq ▸ encodesTable_tableCode Ra0310.cycles } 22386
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0311.table, code := 27725101740241846747634188970421915713,
        encodes := Ra0311.tableCode_eq ▸ encodesTable_tableCode Ra0311.cycles } 22387
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0312.table, code := 27725182869882679205883128942113853505,
        encodes := Ra0312.tableCode_eq ▸ encodesTable_tableCode Ra0312.cycles } 22388
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0313.table, code := 27725182869882679205883128944261337153,
        encodes := Ra0313.tableCode_eq ▸ encodesTable_tableCode Ra0313.cycles } 22389
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0314.table, code := 27725182869882679205955186609166225473,
        encodes := Ra0314.tableCode_eq ▸ encodesTable_tableCode Ra0314.cycles } 22390
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0315.table, code := 27725182869882679205955186611313709121,
        encodes := Ra0315.tableCode_eq ▸ encodesTable_tableCode Ra0315.cycles } 22391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0316.table, code := 27725101740241846750084147303002935361,
        encodes := Ra0316.tableCode_eq ▸ encodesTable_tableCode Ra0316.cycles } 22394
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0317.table, code := 27725101740241846750084147305150419009,
        encodes := Ra0317.tableCode_eq ▸ encodesTable_tableCode Ra0317.cycles } 22395
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0318.table, code := 27725182869882679208333087276842356801,
        encodes := Ra0318.tableCode_eq ▸ encodesTable_tableCode Ra0318.cycles } 22396
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0319.table, code := 27725182869882679208333087278989840449,
        encodes := Ra0319.tableCode_eq ▸ encodesTable_tableCode Ra0319.cycles } 22397
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0320.table, code := 27725182869882679208405144943894728769,
        encodes := Ra0320.tableCode_eq ▸ encodesTable_tableCode Ra0320.cycles } 22398
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (256 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (256 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (256 + i.val) 0 ≤ Data.profiles (256 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (256 + i.val) 0 = Data.canonicalMask (256 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (256 + i.val) < Data.canonicalMask (256 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (256 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models004
