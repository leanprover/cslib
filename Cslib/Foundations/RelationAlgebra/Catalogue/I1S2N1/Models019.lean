/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1217
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1218
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1219
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1220
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1221
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1222
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1223
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1224
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1225
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1226
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1227
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1228
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1229
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1230
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1231
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1232
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1233
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1234
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1235
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1236
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1237
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1238
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1239
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1240
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1241
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1242
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1243
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1244
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1245
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1246
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1247
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1248
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1249
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1250
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1251
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1252
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1253
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1254
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1255
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1256
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1257
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1258
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1259
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1260
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1261
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1262
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1263
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1264
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1265
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1266
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1267
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1268
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1269
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1270
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1271
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1272
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1273
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1274
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1275
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1276
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1277
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1278
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1279
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1280

/-!
# Certified models 1217–1280 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models019

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1217.table, code := 35872140205179254854783845091263123521,
        encodes := Ra1217.tableCode_eq ▸ encodesTable_tableCode Ra1217.cycles } 60409
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1218.table, code := 35872140205179254854855902758315495489,
        encodes := Ra1218.tableCode_eq ▸ encodesTable_tableCode Ra1218.cycles } 60411
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1219.table, code := 35872221334820087313104842730007433281,
        encodes := Ra1219.tableCode_eq ▸ encodesTable_tableCode Ra1219.cycles } 60412
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1220.table, code := 35872221334820087313104842732154916929,
        encodes := Ra1220.tableCode_eq ▸ encodesTable_tableCode Ra1220.cycles } 60413
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1221.table, code := 35872221334820087313176900397059805249,
        encodes := Ra1221.tableCode_eq ▸ encodesTable_tableCode Ra1221.cycles } 60414
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1222.table, code := 35872221334820087313176900399207288897,
        encodes := Ra1222.tableCode_eq ▸ encodesTable_tableCode Ra1222.cycles } 60415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1223.table, code := 33215874711426350455749171590532960321,
        encodes := Ra1223.tableCode_eq ▸ encodesTable_tableCode Ra1223.cycles } 60750
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1224.table, code := 33215874711426350455749171592680443969,
        encodes := Ra1224.tableCode_eq ▸ encodesTable_tableCode Ra1224.cycles } 60751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1225.table, code := 33218633119214656471973662017091539009,
        encodes := Ra1225.tableCode_eq ▸ encodesTable_tableCode Ra1225.cycles } 60788
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1226.table, code := 33218633119214656471973662019239022657,
        encodes := Ra1226.tableCode_eq ▸ encodesTable_tableCode Ra1226.cycles } 60789
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1227.table, code := 33218633119214656472045719684143910977,
        encodes := Ra1227.tableCode_eq ▸ encodesTable_tableCode Ra1227.cycles } 60790
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1228.table, code := 33218633119214656472045719686291394625,
        encodes := Ra1228.tableCode_eq ▸ encodesTable_tableCode Ra1228.cycles } 60791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1229.table, code := 33218633119214656474423620353967525953,
        encodes := Ra1229.tableCode_eq ▸ encodesTable_tableCode Ra1229.cycles } 60797
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1230.table, code := 33218633119214656474495678018872414273,
        encodes := Ra1230.tableCode_eq ▸ encodesTable_tableCode Ra1230.cycles } 60798
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1231.table, code := 33218633119214656474495678021019897921,
        encodes := Ra1231.tableCode_eq ▸ encodesTable_tableCode Ra1231.cycles } 60799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1232.table, code := 35874655224045063519968462550870528065,
        encodes := Ra1232.tableCode_eq ▸ encodesTable_tableCode Ra1232.cycles } 60878
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1233.table, code := 35874655224045063519968462553018011713,
        encodes := Ra1233.tableCode_eq ▸ encodesTable_tableCode Ra1233.cycles } 60879
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1234.table, code := 35874817483399266347474839589060087873,
        encodes := Ra1234.tableCode_eq ▸ encodesTable_tableCode Ra1234.cycles } 60892
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1235.table, code := 35874817483399266347474839591207571521,
        encodes := Ra1235.tableCode_eq ▸ encodesTable_tableCode Ra1235.cycles } 60893
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1236.table, code := 35874817483399266347546897256112459841,
        encodes := Ra1236.tableCode_eq ▸ encodesTable_tableCode Ra1236.cycles } 60894
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1237.table, code := 35874817483399266347546897258259943489,
        encodes := Ra1237.tableCode_eq ▸ encodesTable_tableCode Ra1237.cycles } 60895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1238.table, code := 35877332502192537077871955338684796993,
        encodes := Ra1238.tableCode_eq ▸ encodesTable_tableCode Ra1238.cycles } 60913
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1239.table, code := 35877332502192537077944013005737168961,
        encodes := Ra1239.tableCode_eq ▸ encodesTable_tableCode Ra1239.cycles } 60915
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1240.table, code := 35877413631833369536192952977429106753,
        encodes := Ra1240.tableCode_eq ▸ encodesTable_tableCode Ra1240.cycles } 60916
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1241.table, code := 35877413631833369536192952979576590401,
        encodes := Ra1241.tableCode_eq ▸ encodesTable_tableCode Ra1241.cycles } 60917
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1242.table, code := 35877413631833369536265010644481478721,
        encodes := Ra1242.tableCode_eq ▸ encodesTable_tableCode Ra1242.cycles } 60918
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1243.table, code := 35877413631833369536265010646628962369,
        encodes := Ra1243.tableCode_eq ▸ encodesTable_tableCode Ra1243.cycles } 60919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1244.table, code := 35877332502192537080321913673413300289,
        encodes := Ra1244.tableCode_eq ▸ encodesTable_tableCode Ra1244.cycles } 60921
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1245.table, code := 35877332502192537080393971340465672257,
        encodes := Ra1245.tableCode_eq ▸ encodesTable_tableCode Ra1245.cycles } 60923
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1246.table, code := 35877413631833369538642911312157610049,
        encodes := Ra1246.tableCode_eq ▸ encodesTable_tableCode Ra1246.cycles } 60924
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1247.table, code := 35877413631833369538642911314305093697,
        encodes := Ra1247.tableCode_eq ▸ encodesTable_tableCode Ra1247.cycles } 60925
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1248.table, code := 35877413631833369538714968979209982017,
        encodes := Ra1248.tableCode_eq ▸ encodesTable_tableCode Ra1248.cycles } 60926
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1249.table, code := 35877413631833369538714968981357465665,
        encodes := Ra1249.tableCode_eq ▸ encodesTable_tableCode Ra1249.cycles } 60927
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1250.table, code := 33215874711426350460360857611107831873,
        encodes := Ra1250.tableCode_eq ▸ encodesTable_tableCode Ra1250.cycles } 61263
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1251.table, code := 33218633119214656476585348037666410561,
        encodes := Ra1251.tableCode_eq ▸ encodesTable_tableCode Ra1251.cycles } 61301
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1252.table, code := 33218633119214656476657405704718782529,
        encodes := Ra1252.tableCode_eq ▸ encodesTable_tableCode Ra1252.cycles } 61303
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1253.table, code := 33218633119214656479107364039447285825,
        encodes := Ra1253.tableCode_eq ▸ encodesTable_tableCode Ra1253.cycles } 61311
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1254.table, code := 35874655224045063524580148569297915969,
        encodes := Ra1254.tableCode_eq ▸ encodesTable_tableCode Ra1254.cycles } 61390
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1255.table, code := 35874655224045063524580148571445399617,
        encodes := Ra1255.tableCode_eq ▸ encodesTable_tableCode Ra1255.cycles } 61391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1256.table, code := 35874817483399266352086525607487475777,
        encodes := Ra1256.tableCode_eq ▸ encodesTable_tableCode Ra1256.cycles } 61404
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1257.table, code := 35874817483399266352086525609634959425,
        encodes := Ra1257.tableCode_eq ▸ encodesTable_tableCode Ra1257.cycles } 61405
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1258.table, code := 35874817483399266352158583274539847745,
        encodes := Ra1258.tableCode_eq ▸ encodesTable_tableCode Ra1258.cycles } 61406
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1259.table, code := 35874817483399266352158583276687331393,
        encodes := Ra1259.tableCode_eq ▸ encodesTable_tableCode Ra1259.cycles } 61407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1260.table, code := 35877332502192537082483641357112184897,
        encodes := Ra1260.tableCode_eq ▸ encodesTable_tableCode Ra1260.cycles } 61425
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1261.table, code := 35877332502192537082555699024164556865,
        encodes := Ra1261.tableCode_eq ▸ encodesTable_tableCode Ra1261.cycles } 61427
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1262.table, code := 35877413631833369540804638995856494657,
        encodes := Ra1262.tableCode_eq ▸ encodesTable_tableCode Ra1262.cycles } 61428
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1263.table, code := 35877413631833369540804638998003978305,
        encodes := Ra1263.tableCode_eq ▸ encodesTable_tableCode Ra1263.cycles } 61429
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1264.table, code := 35877413631833369540876696662908866625,
        encodes := Ra1264.tableCode_eq ▸ encodesTable_tableCode Ra1264.cycles } 61430
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1265.table, code := 35877413631833369540876696665056350273,
        encodes := Ra1265.tableCode_eq ▸ encodesTable_tableCode Ra1265.cycles } 61431
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1266.table, code := 35877332502192537084933599691840688193,
        encodes := Ra1266.tableCode_eq ▸ encodesTable_tableCode Ra1266.cycles } 61433
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1267.table, code := 35877332502192537085005657358893060161,
        encodes := Ra1267.tableCode_eq ▸ encodesTable_tableCode Ra1267.cycles } 61435
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1268.table, code := 35877413631833369543254597330584997953,
        encodes := Ra1268.tableCode_eq ▸ encodesTable_tableCode Ra1268.cycles } 61436
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1269.table, code := 35877413631833369543254597332732481601,
        encodes := Ra1269.tableCode_eq ▸ encodesTable_tableCode Ra1269.cycles } 61437
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1270.table, code := 35877413631833369543326654997637369921,
        encodes := Ra1270.tableCode_eq ▸ encodesTable_tableCode Ra1270.cycles } 61438
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1271.table, code := 35877413631833369543326654999784853569,
        encodes := Ra1271.tableCode_eq ▸ encodesTable_tableCode Ra1271.cycles } 61439
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1272.table, code := 41196678379818422190110929213318238273,
        encodes := Ra1272.tableCode_eq ▸ encodesTable_tableCode Ra1272.cycles } 63945
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1273.table, code := 41196678379818422190182986878223126593,
        encodes := Ra1273.tableCode_eq ▸ encodesTable_tableCode Ra1273.cycles } 63946
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1274.table, code := 41196678379818422190182986880370610241,
        encodes := Ra1274.tableCode_eq ▸ encodesTable_tableCode Ra1274.cycles } 63947
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1275.table, code := 41199517917247560667178433280402001985,
        encodes := Ra1275.tableCode_eq ▸ encodesTable_tableCode Ra1275.cycles } 63996
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1276.table, code := 41199517917247560667178433282549485633,
        encodes := Ra1276.tableCode_eq ▸ encodesTable_tableCode Ra1276.cycles } 63997
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1277.table, code := 41199517917247560667250490947454373953,
        encodes := Ra1277.tableCode_eq ▸ encodesTable_tableCode Ra1277.cycles } 63998
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1278.table, code := 41199517917247560667250490949601857601,
        encodes := Ra1278.tableCode_eq ▸ encodesTable_tableCode Ra1278.cycles } 63999
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1279.table, code := 41196678379818422192344714564069494849,
        encodes := Ra1279.tableCode_eq ▸ encodesTable_tableCode Ra1279.cycles } 64451
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1280.table, code := 41196759509459254650665712202813804609,
        encodes := Ra1280.tableCode_eq ▸ encodesTable_tableCode Ra1280.cycles } 64454
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (1216 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1216 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (1216 + i.val) 0 ≤ Data.profiles (1216 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1216 + i.val) 0 = Data.canonicalMask (1216 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1216 + i.val) < Data.canonicalMask (1216 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1216 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models019
