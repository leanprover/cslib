/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0193
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0194
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0195
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0196
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0197
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0198
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0199
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0200
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0201
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0202
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0203
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0204
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0205
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0206
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0207
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0208
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0209
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0210
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0211
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0212
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0213
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0214
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0215
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0216
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0217
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0218
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0219
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0220
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0221
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0222
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0223
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0224
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0225
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0226
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0227
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0228
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0229
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0230
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0231
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0232
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0233
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0234
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0235
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0236
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0237
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0238
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0239
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0240
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0241
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0242
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0243
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0244
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0245
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0246
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0247
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0248
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0249
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0250
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0251
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0252
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0253
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0254
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0255
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0256

/-!
# Certified models 193–256 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models003

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0193.table, code := 30295694335741881389176969695703863361,
        encodes := Ra0193.tableCode_eq ▸ encodesTable_tableCode Ra0193.cycles } 20733
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0194.table, code := 30295694335741881389249027360608751681,
        encodes := Ra0194.tableCode_eq ▸ encodesTable_tableCode Ra0194.cycles } 20734
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0195.table, code := 30295694335741881389249027362756235329,
        encodes := Ra0195.tableCode_eq ▸ encodesTable_tableCode Ra0195.cycles } 20735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0196.table, code := 30378771085488110037790937618174971969,
        encodes := Ra0196.tableCode_eq ▸ encodesTable_tableCode Ra0196.cycles } 20988
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0197.table, code := 30378771085488110037790937620322455617,
        encodes := Ra0197.tableCode_eq ▸ encodesTable_tableCode Ra0197.cycles } 20989
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0198.table, code := 30378771085488110037862995285227343937,
        encodes := Ra0198.tableCode_eq ▸ encodesTable_tableCode Ra0198.cycles } 20990
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0199.table, code := 30378771085488110037862995287374827585,
        encodes := Ra0199.tableCode_eq ▸ encodesTable_tableCode Ra0199.cycles } 20991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0200.table, code := 30295045219406402023620784675577139265,
        encodes := Ra0200.tableCode_eq ▸ encodesTable_tableCode Ra0200.cycles } 21172
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0201.table, code := 30295045219406402023620784677724622913,
        encodes := Ra0201.tableCode_eq ▸ encodesTable_tableCode Ra0201.cycles } 21173
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0202.table, code := 30295045219406402023692842342629511233,
        encodes := Ra0202.tableCode_eq ▸ encodesTable_tableCode Ra0202.cycles } 21174
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0203.table, code := 30295045219406402023692842344776994881,
        encodes := Ra0203.tableCode_eq ▸ encodesTable_tableCode Ra0203.cycles } 21175
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0204.table, code := 30295045219406402026070743010305642561,
        encodes := Ra0204.tableCode_eq ▸ encodesTable_tableCode Ra0204.cycles } 21180
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0205.table, code := 30295045219406402026070743012453126209,
        encodes := Ra0205.tableCode_eq ▸ encodesTable_tableCode Ra0205.cycles } 21181
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0206.table, code := 30295045219406402026142800677358014529,
        encodes := Ra0206.tableCode_eq ▸ encodesTable_tableCode Ra0206.cycles } 21182
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0207.table, code := 30295045219406402026142800679505498177,
        encodes := Ra0207.tableCode_eq ▸ encodesTable_tableCode Ra0207.cycles } 21183
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0208.table, code := 30295694335741881391338697377255264321,
        encodes := Ra0208.tableCode_eq ▸ encodesTable_tableCode Ra0208.cycles } 21236
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0209.table, code := 30295694335741881391338697379402747969,
        encodes := Ra0209.tableCode_eq ▸ encodesTable_tableCode Ra0209.cycles } 21237
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0210.table, code := 30295694335741881391410755044307636289,
        encodes := Ra0210.tableCode_eq ▸ encodesTable_tableCode Ra0210.cycles } 21238
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0211.table, code := 30295694335741881391410755046455119937,
        encodes := Ra0211.tableCode_eq ▸ encodesTable_tableCode Ra0211.cycles } 21239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0212.table, code := 30295694335741881393788655711983767617,
        encodes := Ra0212.tableCode_eq ▸ encodesTable_tableCode Ra0212.cycles } 21244
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0213.table, code := 30295694335741881393788655714131251265,
        encodes := Ra0213.tableCode_eq ▸ encodesTable_tableCode Ra0213.cycles } 21245
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0214.table, code := 30295694335741881393860713379036139585,
        encodes := Ra0214.tableCode_eq ▸ encodesTable_tableCode Ra0214.cycles } 21246
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0215.table, code := 30295694335741881393860713381183623233,
        encodes := Ra0215.tableCode_eq ▸ encodesTable_tableCode Ra0215.cycles } 21247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0216.table, code := 30378689955847277581631667663129546817,
        encodes := Ra0216.tableCode_eq ▸ encodesTable_tableCode Ra0216.cycles } 21489
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0217.table, code := 30378689955847277581703725330181918785,
        encodes := Ra0217.tableCode_eq ▸ encodesTable_tableCode Ra0217.cycles } 21491
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0218.table, code := 30378771085488110039952665301873856577,
        encodes := Ra0218.tableCode_eq ▸ encodesTable_tableCode Ra0218.cycles } 21492
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0219.table, code := 30378771085488110039952665304021340225,
        encodes := Ra0219.tableCode_eq ▸ encodesTable_tableCode Ra0219.cycles } 21493
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0220.table, code := 30378771085488110040024722968926228545,
        encodes := Ra0220.tableCode_eq ▸ encodesTable_tableCode Ra0220.cycles } 21494
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0221.table, code := 30378771085488110040024722971073712193,
        encodes := Ra0221.tableCode_eq ▸ encodesTable_tableCode Ra0221.cycles } 21495
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0222.table, code := 30378689955847277584081625997858050113,
        encodes := Ra0222.tableCode_eq ▸ encodesTable_tableCode Ra0222.cycles } 21497
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0223.table, code := 30378689955847277584153683664910422081,
        encodes := Ra0223.tableCode_eq ▸ encodesTable_tableCode Ra0223.cycles } 21499
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0224.table, code := 30378771085488110042402623636602359873,
        encodes := Ra0224.tableCode_eq ▸ encodesTable_tableCode Ra0224.cycles } 21500
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0225.table, code := 30378771085488110042402623638749843521,
        encodes := Ra0225.tableCode_eq ▸ encodesTable_tableCode Ra0225.cycles } 21501
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0226.table, code := 30378771085488110042474681303654731841,
        encodes := Ra0226.tableCode_eq ▸ encodesTable_tableCode Ra0226.cycles } 21502
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0227.table, code := 30378771085488110042474681305802215489,
        encodes := Ra0227.tableCode_eq ▸ encodesTable_tableCode Ra0227.cycles } 21503
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0228.table, code := 30300237516419684249158853257727316033,
        encodes := Ra0228.tableCode_eq ▸ encodesTable_tableCode Ra0228.cycles } 21684
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0229.table, code := 30300237516419684249158853259874799681,
        encodes := Ra0229.tableCode_eq ▸ encodesTable_tableCode Ra0229.cycles } 21685
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0230.table, code := 30300237516419684249230910924779688001,
        encodes := Ra0230.tableCode_eq ▸ encodesTable_tableCode Ra0230.cycles } 21686
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0231.table, code := 30300237516419684249230910926927171649,
        encodes := Ra0231.tableCode_eq ▸ encodesTable_tableCode Ra0231.cycles } 21687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0232.table, code := 30300237516419684251608811594603302977,
        encodes := Ra0232.tableCode_eq ▸ encodesTable_tableCode Ra0232.cycles } 21693
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0233.table, code := 30300237516419684251680869259508191297,
        encodes := Ra0233.tableCode_eq ▸ encodesTable_tableCode Ra0233.cycles } 21694
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0234.table, code := 30300237516419684251680869261655674945,
        encodes := Ra0234.tableCode_eq ▸ encodesTable_tableCode Ra0234.cycles } 21695
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0235.table, code := 30300724373400960791748289588892012609,
        encodes := Ra0235.tableCode_eq ▸ encodesTable_tableCode Ra0235.cycles } 21740
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0236.table, code := 30300724373400960791748289591039496257,
        encodes := Ra0236.tableCode_eq ▸ encodesTable_tableCode Ra0236.cycles } 21741
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0237.table, code := 30300724373400960791820347255944384577,
        encodes := Ra0237.tableCode_eq ▸ encodesTable_tableCode Ra0237.cycles } 21742
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0238.table, code := 30300724373400960791820347258091868225,
        encodes := Ra0238.tableCode_eq ▸ encodesTable_tableCode Ra0238.cycles } 21743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0239.table, code := 30300805503114331158555768320661131329,
        encodes := Ra0239.tableCode_eq ▸ encodesTable_tableCode Ra0239.cycles } 21745
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0240.table, code := 30300805503114331158627825985566019649,
        encodes := Ra0240.tableCode_eq ▸ encodesTable_tableCode Ra0240.cycles } 21746
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0241.table, code := 30300805503114331158627825987713503297,
        encodes := Ra0241.tableCode_eq ▸ encodesTable_tableCode Ra0241.cycles } 21747
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0242.table, code := 30300886632755163616876765959405441089,
        encodes := Ra0242.tableCode_eq ▸ encodesTable_tableCode Ra0242.cycles } 21748
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0243.table, code := 30300886632755163616876765961552924737,
        encodes := Ra0243.tableCode_eq ▸ encodesTable_tableCode Ra0243.cycles } 21749
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0244.table, code := 30300886632755163616948823626457813057,
        encodes := Ra0244.tableCode_eq ▸ encodesTable_tableCode Ra0244.cycles } 21750
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0245.table, code := 30300886632755163616948823628605296705,
        encodes := Ra0245.tableCode_eq ▸ encodesTable_tableCode Ra0245.cycles } 21751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0246.table, code := 30300805503114331161005726655389634625,
        encodes := Ra0246.tableCode_eq ▸ encodesTable_tableCode Ra0246.cycles } 21753
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0247.table, code := 30300805503114331161077784320294522945,
        encodes := Ra0247.tableCode_eq ▸ encodesTable_tableCode Ra0247.cycles } 21754
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0248.table, code := 30300805503114331161077784322442006593,
        encodes := Ra0248.tableCode_eq ▸ encodesTable_tableCode Ra0248.cycles } 21755
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0249.table, code := 30300886632755163619326724294133944385,
        encodes := Ra0249.tableCode_eq ▸ encodesTable_tableCode Ra0249.cycles } 21756
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0250.table, code := 30300886632755163619326724296281428033,
        encodes := Ra0250.tableCode_eq ▸ encodesTable_tableCode Ra0250.cycles } 21757
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0251.table, code := 30300886632755163619398781961186316353,
        encodes := Ra0251.tableCode_eq ▸ encodesTable_tableCode Ra0251.cycles } 21758
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0252.table, code := 30300886632755163619398781963333800001,
        encodes := Ra0252.tableCode_eq ▸ encodesTable_tableCode Ra0252.cycles } 21759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0253.table, code := 27722343332453540726653897189183721537,
        encodes := Ra0253.tableCode_eq ▸ encodesTable_tableCode Ra0253.cycles } 21832
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0254.table, code := 27722343332453540726653897191331205185,
        encodes := Ra0254.tableCode_eq ▸ encodesTable_tableCode Ra0254.cycles } 21833
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0255.table, code := 27725101740241846743022502949847044161,
        encodes := Ra0255.tableCode_eq ▸ encodesTable_tableCode Ra0255.cycles } 21874
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0256.table, code := 27725101740241846743022502951994527809,
        encodes := Ra0256.tableCode_eq ▸ encodesTable_tableCode Ra0256.cycles } 21875
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (192 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (192 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (192 + i.val) 0 ≤ Data.profiles (192 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (192 + i.val) 0 = Data.canonicalMask (192 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (192 + i.val) < Data.canonicalMask (192 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (192 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models003
