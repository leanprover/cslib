/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0129
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0130
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0131
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0132
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0133
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0134
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0135
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0136
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0137
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0138
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0139
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0140
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0141
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0142
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0143
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0144
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0145
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0146
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0147
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0148
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0149
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0150
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0151
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0152
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0153
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0154
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0155
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0156
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0157
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0158
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0159
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0160
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0161
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0162
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0163
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0164
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0165
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0166
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0167
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0168
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0169
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0170
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0171
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0172
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0173
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0174
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0175
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0176
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0177
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0178
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0179
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0180
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0181
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0182
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0183
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0184
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0185
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0186
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0187
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0188
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0189
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0190
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0191
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0192

/-!
# Certified models 129–192 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models002

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0129.table, code := 4253566342396239284667563331895431233,
        encodes := Ra0129.tableCode_eq ▸ encodesTable_tableCode Ra0129.cycles } 32686
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0130.table, code := 4253566342396239284667563334042914881,
        encodes := Ra0130.tableCode_eq ▸ encodesTable_tableCode Ra0130.cycles } 32687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0131.table, code := 4253566342396239287117521666623934529,
        encodes := Ra0131.tableCode_eq ▸ encodesTable_tableCode Ra0131.cycles } 32702
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0132.table, code := 4253566342396239287117521668771418177,
        encodes := Ra0132.tableCode_eq ▸ encodesTable_tableCode Ra0132.cycles } 32703
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0133.table, code := 4256243620463923666923297457511338049,
        encodes := Ra0133.tableCode_eq ▸ encodesTable_tableCode Ra0133.cycles } 32742
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0134.table, code := 4256243620463923666923297459658821697,
        encodes := Ra0134.tableCode_eq ▸ encodesTable_tableCode Ra0134.cycles } 32743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0135.table, code := 4256324750102338273605063632440528961,
        encodes := Ra0135.tableCode_eq ▸ encodesTable_tableCode Ra0135.cycles } 32750
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0136.table, code := 4256324750102338273605063634588012609,
        encodes := Ra0136.tableCode_eq ▸ encodesTable_tableCode Ra0136.cycles } 32751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0137.table, code := 4256243620463923669373255792239841345,
        encodes := Ra0137.tableCode_eq ▸ encodesTable_tableCode Ra0137.cycles } 32758
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0138.table, code := 4256243620463923669373255794387324993,
        encodes := Ra0138.tableCode_eq ▸ encodesTable_tableCode Ra0138.cycles } 32759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0139.table, code := 4256324750102338276055021967169032257,
        encodes := Ra0139.tableCode_eq ▸ encodesTable_tableCode Ra0139.cycles } 32766
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0140.table, code := 4256324750102338276055021969316515905,
        encodes := Ra0140.tableCode_eq ▸ encodesTable_tableCode Ra0140.cycles } 32767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0141.table, code := 9409435833968250030801222353643900993,
        encodes := Ra0141.tableCode_eq ▸ encodesTable_tableCode Ra0141.cycles } 41859
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0142.table, code := 9409516963609082489122219994535694401,
        encodes := Ra0142.tableCode_eq ▸ encodesTable_tableCode Ra0142.cycles } 41871
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0143.table, code := 9412275371397388510318684757603651649,
        encodes := Ra0143.tableCode_eq ▸ encodesTable_tableCode Ra0143.cycles } 41983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0144.table, code := 9409435833968250035412908372071288897,
        encodes := Ra0144.tableCode_eq ▸ encodesTable_tableCode Ra0144.cycles } 42883
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0145.table, code := 9409516963609082493733906012963082305,
        encodes := Ra0145.tableCode_eq ▸ encodesTable_tableCode Ra0145.cycles } 42895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0146.table, code := 9412275371397388514930370776031039553,
        encodes := Ra0146.tableCode_eq ▸ encodesTable_tableCode Ra0146.cycles } 43007
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0147.table, code := 9412275371552131172026681918497230913,
        encodes := Ra0147.tableCode_eq ▸ encodesTable_tableCode Ra0147.cycles } 44031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0148.table, code := 9412275371552131176638367936924618817,
        encodes := Ra0148.tableCode_eq ▸ encodesTable_tableCode Ra0148.cycles } 45055
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0149.table, code := 9417467668410670740468439358181216321,
        encodes := Ra0149.tableCode_eq ▸ encodesTable_tableCode Ra0149.cycles } 48127
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0150.table, code := 9417467668410670745080125376608604225,
        encodes := Ra0150.tableCode_eq ▸ encodesTable_tableCode Ra0150.cycles } 49151
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0151.table, code := 9585974086233739255749301319047057473,
        encodes := Ra0151.tableCode_eq ▸ encodesTable_tableCode Ra0151.cycles } 58257
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0152.table, code := 9585974086233739255821358983951945793,
        encodes := Ra0152.tableCode_eq ▸ encodesTable_tableCode Ra0152.cycles } 58258
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0153.table, code := 9585974086233739255821358986099429441,
        encodes := Ra0153.tableCode_eq ▸ encodesTable_tableCode Ra0153.cycles } 58259
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0154.table, code := 9588813623662877732816805388278304833,
        encodes := Ra0154.tableCode_eq ▸ encodesTable_tableCode Ra0154.cycles } 58365
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0155.table, code := 9588813623662877732888863053183193153,
        encodes := Ra0155.tableCode_eq ▸ encodesTable_tableCode Ra0155.cycles } 58366
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0156.table, code := 9588813623662877732888863055330676801,
        encodes := Ra0156.tableCode_eq ▸ encodesTable_tableCode Ra0156.cycles } 58367
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0157.table, code := 9585974086233739257983086669798314049,
        encodes := Ra0157.tableCode_eq ▸ encodesTable_tableCode Ra0157.cycles } 59267
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0158.table, code := 9586055215874571716304084308542623809,
        encodes := Ra0158.tableCode_eq ▸ encodesTable_tableCode Ra0158.cycles } 59278
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0159.table, code := 9586055215874571716304084310690107457,
        encodes := Ra0159.tableCode_eq ▸ encodesTable_tableCode Ra0159.cycles } 59279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0160.table, code := 9585974086233739260433045004526817345,
        encodes := Ra0160.tableCode_eq ▸ encodesTable_tableCode Ra0160.cycles } 59283
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0161.table, code := 9588732494022045276729593098137768001,
        encodes := Ra0161.tableCode_eq ▸ encodesTable_tableCode Ra0161.cycles } 59363
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0162.table, code := 9588732494024463128368824561952886849,
        encodes := Ra0162.tableCode_eq ▸ encodesTable_tableCode Ra0162.cycles } 59366
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0163.table, code := 9588732494024463128368824564100370497,
        encodes := Ra0163.tableCode_eq ▸ encodesTable_tableCode Ra0163.cycles } 59367
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0164.table, code := 9588813623662877735050590736882077761,
        encodes := Ra0164.tableCode_eq ▸ encodesTable_tableCode Ra0164.cycles } 59374
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0165.table, code := 9588813623662877735050590739029561409,
        encodes := Ra0165.tableCode_eq ▸ encodesTable_tableCode Ra0165.cycles } 59375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0166.table, code := 9588732494022045279179551432866271297,
        encodes := Ra0166.tableCode_eq ▸ encodesTable_tableCode Ra0166.cycles } 59379
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0167.table, code := 9588732494024463130746725231776501825,
        encodes := Ra0167.tableCode_eq ▸ encodesTable_tableCode Ra0167.cycles } 59381
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0168.table, code := 9588732494024463130818782896681390145,
        encodes := Ra0168.tableCode_eq ▸ encodesTable_tableCode Ra0168.cycles } 59382
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0169.table, code := 9588732494024463130818782898828873793,
        encodes := Ra0169.tableCode_eq ▸ encodesTable_tableCode Ra0169.cycles } 59383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0170.table, code := 9588813623662877737428491406705692737,
        encodes := Ra0170.tableCode_eq ▸ encodesTable_tableCode Ra0170.cycles } 59389
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0171.table, code := 9588813623662877737500549071610581057,
        encodes := Ra0171.tableCode_eq ▸ encodesTable_tableCode Ra0171.cycles } 59390
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0172.table, code := 9588813623662877737500549073758064705,
        encodes := Ra0172.tableCode_eq ▸ encodesTable_tableCode Ra0172.cycles } 59391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0173.table, code := 9588732494096998758034030246448336961,
        encodes := Ra0173.tableCode_eq ▸ encodesTable_tableCode Ra0173.cycles } 60373
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0174.table, code := 9588732494096998758106087911353225281,
        encodes := Ra0174.tableCode_eq ▸ encodesTable_tableCode Ra0174.cycles } 60374
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0175.table, code := 9588732494096998758106087913500708929,
        encodes := Ra0175.tableCode_eq ▸ encodesTable_tableCode Ra0175.cycles } 60375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0176.table, code := 9588813623735413364715796421377527873,
        encodes := Ra0176.tableCode_eq ▸ encodesTable_tableCode Ra0176.cycles } 60381
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0177.table, code := 9588813623735413364787854086282416193,
        encodes := Ra0177.tableCode_eq ▸ encodesTable_tableCode Ra0177.cycles } 60382
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0178.table, code := 9588813623735413364787854088429899841,
        encodes := Ra0178.tableCode_eq ▸ encodesTable_tableCode Ra0178.cycles } 60383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0179.table, code := 9588732494179205787843036374242693185,
        encodes := Ra0179.tableCode_eq ▸ encodesTable_tableCode Ra0179.cycles } 60405
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0180.table, code := 9588732494179205787915094039147581505,
        encodes := Ra0180.tableCode_eq ▸ encodesTable_tableCode Ra0180.cycles } 60406
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0181.table, code := 9588732494179205787915094041295065153,
        encodes := Ra0181.tableCode_eq ▸ encodesTable_tableCode Ra0181.cycles } 60407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0182.table, code := 9588813623815202542885571083209281601,
        encodes := Ra0182.tableCode_eq ▸ encodesTable_tableCode Ra0182.cycles } 60409
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0183.table, code := 9588813623815202542957628748114169921,
        encodes := Ra0183.tableCode_eq ▸ encodesTable_tableCode Ra0183.cycles } 60410
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0184.table, code := 9588813623815202542957628750261653569,
        encodes := Ra0184.tableCode_eq ▸ encodesTable_tableCode Ra0184.cycles } 60411
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0185.table, code := 9588813623817620394524802549171884097,
        encodes := Ra0185.tableCode_eq ▸ encodesTable_tableCode Ra0185.cycles } 60413
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0186.table, code := 9588813623817620394596860214076772417,
        encodes := Ra0186.tableCode_eq ▸ encodesTable_tableCode Ra0186.cycles } 60414
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0187.table, code := 9588813623817620394596860216224256065,
        encodes := Ra0187.tableCode_eq ▸ encodesTable_tableCode Ra0187.cycles } 60415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0188.table, code := 9588732494096998760267815597199593537,
        encodes := Ra0188.tableCode_eq ▸ encodesTable_tableCode Ra0188.cycles } 61383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0189.table, code := 9588813623735413366949581769981300801,
        encodes := Ra0189.tableCode_eq ▸ encodesTable_tableCode Ra0189.cycles } 61390
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0190.table, code := 9588813623735413366949581772128784449,
        encodes := Ra0190.tableCode_eq ▸ encodesTable_tableCode Ra0190.cycles } 61391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0191.table, code := 9588732494096998762717773931928096833,
        encodes := Ra0191.tableCode_eq ▸ encodesTable_tableCode Ra0191.cycles } 61399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0192.table, code := 9588813623735413369327482439804915777,
        encodes := Ra0192.tableCode_eq ▸ encodesTable_tableCode Ra0192.cycles } 61405
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (128 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (128 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (128 + i.val) 0 ≤ Data.profiles (128 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (128 + i.val) 0 = Data.canonicalMask (128 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (128 + i.val) < Data.canonicalMask (128 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (128 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models002
