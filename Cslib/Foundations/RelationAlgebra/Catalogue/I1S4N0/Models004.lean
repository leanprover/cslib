/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0257
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0258
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0259
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0260
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0261
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0262
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0263
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0264
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0265
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0266
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0267
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0268
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0269
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0270
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0271
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0272
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0273
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0274
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0275
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0276
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0277
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0278
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0279
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0280
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0281
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0282
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0283
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0284
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0285
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0286
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0287
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0288
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0289
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0290
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0291
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0292
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0293
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0294
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0295
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0296
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0297
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0298
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0299
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0300
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0301
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0302
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0303
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0304
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0305
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0306
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0307
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0308
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0309
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0310
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0311
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0312
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0313
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0314
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0315
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0316
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0317
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0318
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0319
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0320

/-!
# Certified models 257–320 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models004

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0257.table, code := 4251132455400522074657848999715016769,
        encodes := Ra0257.tableCode_eq ▸ encodesTable_tableCode Ra0257.cycles } 85886
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0258.table, code := 4251132455400522074657849001862500417,
        encodes := Ra0258.tableCode_eq ▸ encodesTable_tableCode Ra0258.cycles } 85887
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0259.table, code := 4251051328247658950653810869346242625,
        encodes := Ra0259.tableCode_eq ▸ encodesTable_tableCode Ra0259.cycles } 85990
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0260.table, code := 4251051328247658950653810871493726273,
        encodes := Ra0260.tableCode_eq ▸ encodesTable_tableCode Ra0260.cycles } 85991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0261.table, code := 4251132457886073557335577044275433537,
        encodes := Ra0261.tableCode_eq ▸ encodesTable_tableCode Ra0261.cycles } 85998
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0262.table, code := 4251132457886073557335577046422917185,
        encodes := Ra0262.tableCode_eq ▸ encodesTable_tableCode Ra0262.cycles } 85999
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0263.table, code := 4251051328247658953103769204074745921,
        encodes := Ra0263.tableCode_eq ▸ encodesTable_tableCode Ra0263.cycles } 86006
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0264.table, code := 4251051328247658953103769206222229569,
        encodes := Ra0264.tableCode_eq ▸ encodesTable_tableCode Ra0264.cycles } 86007
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0265.table, code := 4251132457886073559785535379003936833,
        encodes := Ra0265.tableCode_eq ▸ encodesTable_tableCode Ra0265.cycles } 86014
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0266.table, code := 4251132457886073559785535381151420481,
        encodes := Ra0266.tableCode_eq ▸ encodesTable_tableCode Ra0266.cycles } 86015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0267.table, code := 4253485214757387527071466983912640577,
        encodes := Ra0267.tableCode_eq ▸ encodesTable_tableCode Ra0267.cycles } 86818
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0268.table, code := 4253566344398219985392464624804433985,
        encodes := Ra0268.tableCode_eq ▸ encodesTable_tableCode Ra0268.cycles } 86830
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0269.table, code := 4253566344398219985392464626951917633,
        encodes := Ra0269.tableCode_eq ▸ encodesTable_tableCode Ra0269.cycles } 86831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0270.table, code := 4256243622465904370098157087296327745,
        encodes := Ra0270.tableCode_eq ▸ encodesTable_tableCode Ra0270.cycles } 86903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0271.table, code := 4256324752104318976779923260078035009,
        encodes := Ra0271.tableCode_eq ▸ encodesTable_tableCode Ra0271.cycles } 86910
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0272.table, code := 4256324752104318976779923262225518657,
        encodes := Ra0272.tableCode_eq ▸ encodesTable_tableCode Ra0272.cycles } 86911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0273.table, code := 4253485217242939012199153365349044289,
        encodes := Ra0273.tableCode_eq ▸ encodesTable_tableCode Ra0273.cycles } 86947
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0274.table, code := 4253566346883771470520151004093354049,
        encodes := Ra0274.tableCode_eq ▸ encodesTable_tableCode Ra0274.cycles } 86958
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0275.table, code := 4253566346883771470520151006240837697,
        encodes := Ra0275.tableCode_eq ▸ encodesTable_tableCode Ra0275.cycles } 86959
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0276.table, code := 4256243624951455855225843466585247809,
        encodes := Ra0276.tableCode_eq ▸ encodesTable_tableCode Ra0276.cycles } 87031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0277.table, code := 4256324754589870461907609639366955073,
        encodes := Ra0277.tableCode_eq ▸ encodesTable_tableCode Ra0277.cycles } 87038
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0278.table, code := 4256324754589870461907609641514438721,
        encodes := Ra0278.tableCode_eq ▸ encodesTable_tableCode Ra0278.cycles } 87039
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0279.table, code := 4256243622465904372259884770995212353,
        encodes := Ra0279.tableCode_eq ▸ encodesTable_tableCode Ra0279.cycles } 87911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0280.table, code := 4256324752104318978941650943776919617,
        encodes := Ra0280.tableCode_eq ▸ encodesTable_tableCode Ra0280.cycles } 87918
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0281.table, code := 4256324752104318978941650945924403265,
        encodes := Ra0281.tableCode_eq ▸ encodesTable_tableCode Ra0281.cycles } 87919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0282.table, code := 4256243622465904374709843105723715649,
        encodes := Ra0282.tableCode_eq ▸ encodesTable_tableCode Ra0282.cycles } 87927
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0283.table, code := 4256324752104318981391609278505422913,
        encodes := Ra0283.tableCode_eq ▸ encodesTable_tableCode Ra0283.cycles } 87934
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0284.table, code := 4256324752104318981391609280652906561,
        encodes := Ra0284.tableCode_eq ▸ encodesTable_tableCode Ra0284.cycles } 87935
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0285.table, code := 4256243624951455857387571150284132417,
        encodes := Ra0285.tableCode_eq ▸ encodesTable_tableCode Ra0285.cycles } 88039
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0286.table, code := 4256324754589870464069337323065839681,
        encodes := Ra0286.tableCode_eq ▸ encodesTable_tableCode Ra0286.cycles } 88046
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0287.table, code := 4256324754589870464069337325213323329,
        encodes := Ra0287.tableCode_eq ▸ encodesTable_tableCode Ra0287.cycles } 88047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0288.table, code := 4256243624951455859837529485012635713,
        encodes := Ra0288.tableCode_eq ▸ encodesTable_tableCode Ra0288.cycles } 88055
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0289.table, code := 4256324754589870466519295657794342977,
        encodes := Ra0289.tableCode_eq ▸ encodesTable_tableCode Ra0289.cycles } 88062
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0290.table, code := 4256324754589870466519295659941826625,
        encodes := Ra0290.tableCode_eq ▸ encodesTable_tableCode Ra0290.cycles } 88063
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0291.table, code := 4253485214912130191229422481682206785,
        encodes := Ra0291.tableCode_eq ▸ encodesTable_tableCode Ra0291.cycles } 88883
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0292.table, code := 4253566344552962649550420120426516545,
        encodes := Ra0292.tableCode_eq ▸ encodesTable_tableCode Ra0292.cycles } 88894
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0293.table, code := 4253566344552962649550420122574000193,
        encodes := Ra0293.tableCode_eq ▸ encodesTable_tableCode Ra0293.cycles } 88895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0294.table, code := 4256243622620647031806154246042423361,
        encodes := Ra0294.tableCode_eq ▸ encodesTable_tableCode Ra0294.cycles } 88950
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0295.table, code := 4256243622620647031806154248189907009,
        encodes := Ra0295.tableCode_eq ▸ encodesTable_tableCode Ra0295.cycles } 88951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0296.table, code := 4256324752259061638487920420971614273,
        encodes := Ra0296.tableCode_eq ▸ encodesTable_tableCode Ra0296.cycles } 88958
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0297.table, code := 4256324752259061638487920423119097921,
        encodes := Ra0297.tableCode_eq ▸ encodesTable_tableCode Ra0297.cycles } 88959
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0298.table, code := 4253485217397681676357108858823643201,
        encodes := Ra0298.tableCode_eq ▸ encodesTable_tableCode Ra0298.cycles } 89010
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0299.table, code := 4253485217397681676357108860971126849,
        encodes := Ra0299.tableCode_eq ▸ encodesTable_tableCode Ra0299.cycles } 89011
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0300.table, code := 4253566347038514134678106499715436609,
        encodes := Ra0300.tableCode_eq ▸ encodesTable_tableCode Ra0300.cycles } 89022
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0301.table, code := 4253566347038514134678106501862920257,
        encodes := Ra0301.tableCode_eq ▸ encodesTable_tableCode Ra0301.cycles } 89023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0302.table, code := 4256243625106198516933840625331343425,
        encodes := Ra0302.tableCode_eq ▸ encodesTable_tableCode Ra0302.cycles } 89078
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0303.table, code := 4256243625106198516933840627478827073,
        encodes := Ra0303.tableCode_eq ▸ encodesTable_tableCode Ra0303.cycles } 89079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0304.table, code := 4256324754744613123615606800260534337,
        encodes := Ra0304.tableCode_eq ▸ encodesTable_tableCode Ra0304.cycles } 89086
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0305.table, code := 4256324754744613123615606802408017985,
        encodes := Ra0305.tableCode_eq ▸ encodesTable_tableCode Ra0305.cycles } 89087
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0306.table, code := 4170164999498375291416761560337748033,
        encodes := Ra0306.tableCode_eq ▸ encodesTable_tableCode Ra0306.cycles } 89784
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0307.table, code := 4170164999498375291416761562485231681,
        encodes := Ra0307.tableCode_eq ▸ encodesTable_tableCode Ra0307.cycles } 89785
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0308.table, code := 4172923407206892132065550993897820225,
        encodes := Ra0308.tableCode_eq ▸ encodesTable_tableCode Ra0308.cycles } 89854
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0309.table, code := 4172923407206892132065550996045303873,
        encodes := Ra0309.tableCode_eq ▸ encodesTable_tableCode Ra0309.cycles } 89855
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0310.table, code := 4253566344552962651712147804125401153,
        encodes := Ra0310.tableCode_eq ▸ encodesTable_tableCode Ra0310.cycles } 89902
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0311.table, code := 4253566344552962651712147806272884801,
        encodes := Ra0311.tableCode_eq ▸ encodesTable_tableCode Ra0311.cycles } 89903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0312.table, code := 4253485214912130195841108500109594689,
        encodes := Ra0312.tableCode_eq ▸ encodesTable_tableCode Ra0312.cycles } 89907
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0313.table, code := 4253566344552962654162106138853904449,
        encodes := Ra0313.tableCode_eq ▸ encodesTable_tableCode Ra0313.cycles } 89918
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0314.table, code := 4253566344552962654162106141001388097,
        encodes := Ra0314.tableCode_eq ▸ encodesTable_tableCode Ra0314.cycles } 89919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0315.table, code := 4256243622620647033967881929741307969,
        encodes := Ra0315.tableCode_eq ▸ encodesTable_tableCode Ra0315.cycles } 89958
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0316.table, code := 4256243622620647033967881931888791617,
        encodes := Ra0316.tableCode_eq ▸ encodesTable_tableCode Ra0316.cycles } 89959
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0317.table, code := 4256324752259061640649648104670498881,
        encodes := Ra0317.tableCode_eq ▸ encodesTable_tableCode Ra0317.cycles } 89966
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0318.table, code := 4256324752259061640649648106817982529,
        encodes := Ra0318.tableCode_eq ▸ encodesTable_tableCode Ra0318.cycles } 89967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0319.table, code := 4256243622620647036417840264469811265,
        encodes := Ra0319.tableCode_eq ▸ encodesTable_tableCode Ra0319.cycles } 89974
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0320.table, code := 4256243622620647036417840266617294913,
        encodes := Ra0320.tableCode_eq ▸ encodesTable_tableCode Ra0320.cycles } 89975
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (256 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (256 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
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

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models004
