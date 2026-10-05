/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0129
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0130
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0131
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0132
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0133
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0134
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0135
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0136
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0137
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0138
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0139
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0140
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0141
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0142
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0143
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0144
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0145
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0146
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0147
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0148
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0149
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0150
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0151
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0152
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0153
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0154
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0155
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0156
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0157
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0158
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0159
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0160
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0161
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0162
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0163
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0164
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0165
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0166
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0167
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0168
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0169
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0170
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0171
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0172
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0173
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0174
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0175
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0176
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0177
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0178
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0179
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0180
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0181
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0182
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0183
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0184
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0185
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0186
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0187
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0188
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0189
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0190
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0191
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0192

/-!
# Certified models 129–192 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models002

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0129.table, code := 24970182526203904878788714613721796673,
        encodes := Ra0129.tableCode_eq ▸ encodesTable_tableCode Ra0129.cycles } 18060
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0130.table, code := 24970182526203904878788714615869280321,
        encodes := Ra0130.tableCode_eq ▸ encodesTable_tableCode Ra0130.cycles } 18061
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0131.table, code := 24970831642539384246506627315399921729,
        encodes := Ra0131.tableCode_eq ▸ encodesTable_tableCode Ra0131.cycles } 18124
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0132.table, code := 24970831642539384246506627317547405377,
        encodes := Ra0132.tableCode_eq ▸ encodesTable_tableCode Ra0132.cycles } 18125
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0133.table, code := 22395046750026067372580306638789152833,
        encodes := Ra0133.tableCode_eq ▸ encodesTable_tableCode Ra0133.cycles } 18248
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0134.table, code := 22395046750026067372580306640936636481,
        encodes := Ra0134.tableCode_eq ▸ encodesTable_tableCode Ra0134.cycles } 18249
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0135.table, code := 22395127879666899830901304279680946241,
        encodes := Ra0135.tableCode_eq ▸ encodesTable_tableCode Ra0135.cycles } 18252
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0136.table, code := 22395127879666899830901304281828429889,
        encodes := Ra0136.tableCode_eq ▸ encodesTable_tableCode Ra0136.cycles } 18253
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0137.table, code := 25053827262644780436799597601274204225,
        encodes := Ra0137.tableCode_eq ▸ encodesTable_tableCode Ra0137.cycles } 18377
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0138.table, code := 25053908392285612895120595240018513985,
        encodes := Ra0138.tableCode_eq ▸ encodesTable_tableCode Ra0138.cycles } 18380
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0139.table, code := 25053908392285612895120595242165997633,
        encodes := Ra0139.tableCode_eq ▸ encodesTable_tableCode Ra0139.cycles } 18381
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0140.table, code := 25056585670433086453168203361937526849,
        encodes := Ra0140.tableCode_eq ▸ encodesTable_tableCode Ra0140.cycles } 18419
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0141.table, code := 25056666800073918911489201000681836609,
        encodes := Ra0141.tableCode_eq ▸ encodesTable_tableCode Ra0141.cycles } 18422
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0142.table, code := 25056666800073918911489201002829320257,
        encodes := Ra0142.tableCode_eq ▸ encodesTable_tableCode Ra0142.cycles } 18423
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0143.table, code := 25056585670433086455546104029613658177,
        encodes := Ra0143.tableCode_eq ▸ encodesTable_tableCode Ra0143.cycles } 18425
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0144.table, code := 25056585670433086455618161696666030145,
        encodes := Ra0144.tableCode_eq ▸ encodesTable_tableCode Ra0144.cycles } 18427
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0145.table, code := 25056666800073918913867101670505451585,
        encodes := Ra0145.tableCode_eq ▸ encodesTable_tableCode Ra0145.cycles } 18429
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0146.table, code := 25056666800073918913939159335410339905,
        encodes := Ra0146.tableCode_eq ▸ encodesTable_tableCode Ra0146.cycles } 18430
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0147.table, code := 25056666800073918913939159337557823553,
        encodes := Ra0147.tableCode_eq ▸ encodesTable_tableCode Ra0147.cycles } 18431
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0148.table, code := 25072243848951101313368421070310477889,
        encodes := Ra0148.tableCode_eq ▸ encodesTable_tableCode Ra0148.cycles } 18943
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0149.table, code := 25072243848951101317980107088737865793,
        encodes := Ra0149.tableCode_eq ▸ encodesTable_tableCode Ra0149.cycles } 19455
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0150.table, code := 22332982735165338639516845062834360385,
        encodes := Ra0150.tableCode_eq ▸ encodesTable_tableCode Ra0150.cycles } 19551
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0151.table, code := 22335578883599441830612859118879510593,
        encodes := Ra0151.tableCode_eq ▸ encodesTable_tableCode Ra0151.cycles } 19581
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0152.table, code := 22335578883599441830684916783784398913,
        encodes := Ra0152.tableCode_eq ▸ encodesTable_tableCode Ra0152.cycles } 19582
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0153.table, code := 22335578883599441830684916785931882561,
        encodes := Ra0153.tableCode_eq ▸ encodesTable_tableCode Ra0153.cycles } 19583
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0154.table, code := 25076787029628904175728205302157545537,
        encodes := Ra0154.tableCode_eq ▸ encodesTable_tableCode Ra0154.cycles } 19901
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0155.table, code := 25076787029628904175800262967062433857,
        encodes := Ra0155.tableCode_eq ▸ encodesTable_tableCode Ra0155.cycles } 19902
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0156.table, code := 25076787029628904175800262969209917505,
        encodes := Ra0156.tableCode_eq ▸ encodesTable_tableCode Ra0156.cycles } 19903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0157.table, code := 25077355016323551085125120362943877185,
        encodes := Ra0157.tableCode_eq ▸ encodesTable_tableCode Ra0157.cycles } 19961
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0158.table, code := 25077355016323551085197178029996249153,
        encodes := Ra0158.tableCode_eq ▸ encodesTable_tableCode Ra0158.cycles } 19963
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0159.table, code := 25077436145964383543446118003835670593,
        encodes := Ra0159.tableCode_eq ▸ encodesTable_tableCode Ra0159.cycles } 19965
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0160.table, code := 25077436145964383543518175668740558913,
        encodes := Ra0160.tableCode_eq ▸ encodesTable_tableCode Ra0160.cycles } 19966
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0161.table, code := 25077436145964383543518175670888042561,
        encodes := Ra0161.tableCode_eq ▸ encodesTable_tableCode Ra0161.cycles } 19967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0162.table, code := 22332820475811135816550096376019816513,
        encodes := Ra0162.tableCode_eq ▸ encodesTable_tableCode Ra0162.cycles } 20047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0163.table, code := 22332982735165338641678572746533244993,
        encodes := Ra0163.tableCode_eq ▸ encodesTable_tableCode Ra0163.cycles } 20055
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0164.table, code := 22332982735165338644128531081261748289,
        encodes := Ra0164.tableCode_eq ▸ encodesTable_tableCode Ra0164.cycles } 20063
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0165.table, code := 22335578883599441832846644469630767169,
        encodes := Ra0165.tableCode_eq ▸ encodesTable_tableCode Ra0165.cycles } 20087
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0166.table, code := 22335578883599441835296602804359270465,
        encodes := Ra0166.tableCode_eq ▸ encodesTable_tableCode Ra0166.cycles } 20095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0167.table, code := 22417844257655988286092207320276930625,
        encodes := Ra0167.tableCode_eq ▸ encodesTable_tableCode Ra0167.cycles } 20261
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0168.table, code := 22417844257655988288614223322057805889,
        encodes := Ra0168.tableCode_eq ▸ encodesTable_tableCode Ra0168.cycles } 20271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0169.table, code := 22415816095916532006771008990546759745,
        encodes := Ra0169.tableCode_eq ▸ encodesTable_tableCode Ra0169.cycles } 20296
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0170.table, code := 22415816095916532006771008992694243393,
        encodes := Ra0170.tableCode_eq ▸ encodesTable_tableCode Ra0170.cycles } 20297
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0171.table, code := 22418493373991467656260078354536075329,
        encodes := Ra0171.tableCode_eq ▸ encodesTable_tableCode Ra0171.cycles } 20332
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0172.table, code := 22418493373991467656260078356683558977,
        encodes := Ra0172.tableCode_eq ▸ encodesTable_tableCode Ra0172.cycles } 20333
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0173.table, code := 22418493373991467656332136021588447297,
        encodes := Ra0173.tableCode_eq ▸ encodesTable_tableCode Ra0173.cycles } 20334
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0174.table, code := 22418493373991467656332136023735930945,
        encodes := Ra0174.tableCode_eq ▸ encodesTable_tableCode Ra0174.cycles } 20335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0175.table, code := 25076787029628904177961990650761318465,
        encodes := Ra0175.tableCode_eq ▸ encodesTable_tableCode Ra0175.cycles } 20406
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0176.table, code := 25076787029628904177961990652908802113,
        encodes := Ra0176.tableCode_eq ▸ encodesTable_tableCode Ra0176.cycles } 20407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0177.table, code := 25076787029628904180339891320584933441,
        encodes := Ra0177.tableCode_eq ▸ encodesTable_tableCode Ra0177.cycles } 20413
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0178.table, code := 25076787029628904180411948985489821761,
        encodes := Ra0178.tableCode_eq ▸ encodesTable_tableCode Ra0178.cycles } 20414
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0179.table, code := 25076787029628904180411948987637305409,
        encodes := Ra0179.tableCode_eq ▸ encodesTable_tableCode Ra0179.cycles } 20415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0180.table, code := 25077355016323551087358905713695133761,
        encodes := Ra0180.tableCode_eq ▸ encodesTable_tableCode Ra0180.cycles } 20467
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0181.table, code := 25077436145964383545679903352439443521,
        encodes := Ra0181.tableCode_eq ▸ encodesTable_tableCode Ra0181.cycles } 20470
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0182.table, code := 25077436145964383545679903354586927169,
        encodes := Ra0182.tableCode_eq ▸ encodesTable_tableCode Ra0182.cycles } 20471
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0183.table, code := 25077355016323551089736806381371265089,
        encodes := Ra0183.tableCode_eq ▸ encodesTable_tableCode Ra0183.cycles } 20473
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0184.table, code := 25077355016323551089808864048423637057,
        encodes := Ra0184.tableCode_eq ▸ encodesTable_tableCode Ra0184.cycles } 20475
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0185.table, code := 25077436145964383548057804022263058497,
        encodes := Ra0185.tableCode_eq ▸ encodesTable_tableCode Ra0185.cycles } 20477
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0186.table, code := 25077436145964383548129861687167946817,
        encodes := Ra0186.tableCode_eq ▸ encodesTable_tableCode Ra0186.cycles } 20478
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0187.table, code := 25077436145964383548129861689315430465,
        encodes := Ra0187.tableCode_eq ▸ encodesTable_tableCode Ra0187.cycles } 20479
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0188.table, code := 30295045219406402021459056991878254657,
        encodes := Ra0188.tableCode_eq ▸ encodesTable_tableCode Ra0188.cycles } 20668
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0189.table, code := 30295045219406402021459056994025738305,
        encodes := Ra0189.tableCode_eq ▸ encodesTable_tableCode Ra0189.cycles } 20669
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0190.table, code := 30295045219406402021531114658930626625,
        encodes := Ra0190.tableCode_eq ▸ encodesTable_tableCode Ra0190.cycles } 20670
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0191.table, code := 30295045219406402021531114661078110273,
        encodes := Ra0191.tableCode_eq ▸ encodesTable_tableCode Ra0191.cycles } 20671
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0192.table, code := 30295694335741881389176969693556379713,
        encodes := Ra0192.tableCode_eq ▸ encodesTable_tableCode Ra0192.cycles } 20732
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (128 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (128 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
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

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models002
