/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1281
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1282
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1283
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1284
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1285
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1286
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1287
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1288
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1289
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1290
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1291
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1292
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1293
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1294
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1295
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1296
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1297
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1298
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1299
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1300
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1301
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1302
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1303
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1304
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1305
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1306
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1307
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1308
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1309
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1310
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1311
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1312
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1313
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1314
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1315
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1316
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1317
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1318
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1319
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1320
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1321
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1322
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1323
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1324
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1325
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1326
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1327
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1328
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1329
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1330
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1331
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1332
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1333
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1334
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1335
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1336
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1337
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1338
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1339
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1340
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1341
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1342
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1343
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1344

/-!
# Certified models 1281–1344 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models020

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1281.table, code := 9749693874355968762438739609369448513,
        encodes := Ra1281.tableCode_eq ▸ encodesTable_tableCode Ra1281.cycles } 180182
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1282.table, code := 9749693874355968762438739611516932161,
        encodes := Ra1282.tableCode_eq ▸ encodesTable_tableCode Ra1282.cycles } 180183
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1283.table, code := 9749775003994383369120505784298639425,
        encodes := Ra1283.tableCode_eq ▸ encodesTable_tableCode Ra1283.cycles } 180190
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1284.table, code := 9749775003994383369120505786446123073,
        encodes := Ra1284.tableCode_eq ▸ encodesTable_tableCode Ra1284.cycles } 180191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1285.table, code := 9749693874435757938158555938620182593,
        encodes := Ra1285.tableCode_eq ▸ encodesTable_tableCode Ra1285.cycles } 180195
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1286.table, code := 9749693874438175789797787402435301441,
        encodes := Ra1286.tableCode_eq ▸ encodesTable_tableCode Ra1286.cycles } 180198
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1287.table, code := 9749693874438175789797787404582785089,
        encodes := Ra1287.tableCode_eq ▸ encodesTable_tableCode Ra1287.cycles } 180199
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1288.table, code := 9749775004074172544840322113549373505,
        encodes := Ra1288.tableCode_eq ▸ encodesTable_tableCode Ra1288.cycles } 180203
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1289.table, code := 9749775004076590396479553577364492353,
        encodes := Ra1289.tableCode_eq ▸ encodesTable_tableCode Ra1289.cycles } 180206
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1290.table, code := 9749775004076590396479553579511976001,
        encodes := Ra1290.tableCode_eq ▸ encodesTable_tableCode Ra1290.cycles } 180207
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1291.table, code := 9749693874435757940536456606296313921,
        encodes := Ra1291.tableCode_eq ▸ encodesTable_tableCode Ra1291.cycles } 180209
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1292.table, code := 9749693874435757940608514273348685889,
        encodes := Ra1292.tableCode_eq ▸ encodesTable_tableCode Ra1292.cycles } 180211
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1293.table, code := 9749693874438175792175688072258916417,
        encodes := Ra1293.tableCode_eq ▸ encodesTable_tableCode Ra1293.cycles } 180213
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1294.table, code := 9749693874438175792247745737163804737,
        encodes := Ra1294.tableCode_eq ▸ encodesTable_tableCode Ra1294.cycles } 180214
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1295.table, code := 9749693874438175792247745739311288385,
        encodes := Ra1295.tableCode_eq ▸ encodesTable_tableCode Ra1295.cycles } 180215
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1296.table, code := 9749775004074172547218222781225504833,
        encodes := Ra1296.tableCode_eq ▸ encodesTable_tableCode Ra1296.cycles } 180217
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1297.table, code := 9749775004074172547290280448277876801,
        encodes := Ra1297.tableCode_eq ▸ encodesTable_tableCode Ra1297.cycles } 180219
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1298.table, code := 9749775004076590398857454245040623681,
        encodes := Ra1298.tableCode_eq ▸ encodesTable_tableCode Ra1298.cycles } 180220
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1299.table, code := 9749775004076590398857454247188107329,
        encodes := Ra1299.tableCode_eq ▸ encodesTable_tableCode Ra1299.cycles } 180221
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1300.table, code := 9749775004076590398929511912092995649,
        encodes := Ra1300.tableCode_eq ▸ encodesTable_tableCode Ra1300.cycles } 180222
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1301.table, code := 9749775004076590398929511914240479297,
        encodes := Ra1301.tableCode_eq ▸ encodesTable_tableCode Ra1301.cycles } 180223
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1302.table, code := 9921039824581462127942420098237861953,
        encodes := Ra1302.tableCode_eq ▸ encodesTable_tableCode Ra1302.cycles } 183281
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1303.table, code := 9921039824581462128014477765290233921,
        encodes := Ra1303.tableCode_eq ▸ encodesTable_tableCode Ra1303.cycles } 183283
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1304.table, code := 9921039824583879979653709229105352769,
        encodes := Ra1304.tableCode_eq ▸ encodesTable_tableCode Ra1304.cycles } 183286
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1305.table, code := 9921039824583879979653709231252836417,
        encodes := Ra1305.tableCode_eq ▸ encodesTable_tableCode Ra1305.cycles } 183287
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1306.table, code := 9921120954222294586335475404034543681,
        encodes := Ra1306.tableCode_eq ▸ encodesTable_tableCode Ra1306.cycles } 183294
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1307.table, code := 9921120954222294586335475406182027329,
        encodes := Ra1307.tableCode_eq ▸ encodesTable_tableCode Ra1307.cycles } 183295
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1308.table, code := 9921039822016121469328702742596948033,
        encodes := Ra1308.tableCode_eq ▸ encodesTable_tableCode Ra1308.cycles } 184151
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1309.table, code := 9921120951654536075938411250473766977,
        encodes := Ra1309.tableCode_eq ▸ encodesTable_tableCode Ra1309.cycles } 184157
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1310.table, code := 9921120951654536076010468917526138945,
        encodes := Ra1310.tableCode_eq ▸ encodesTable_tableCode Ra1310.cycles } 184159
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1311.table, code := 9921039822098328496687750535662800961,
        encodes := Ra1311.tableCode_eq ▸ encodesTable_tableCode Ra1311.cycles } 184167
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1312.table, code := 9921120951736743103369516710591991873,
        encodes := Ra1312.tableCode_eq ▸ encodesTable_tableCode Ra1312.cycles } 184175
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1313.table, code := 9921039822098328499137708870391304257,
        encodes := Ra1313.tableCode_eq ▸ encodesTable_tableCode Ra1313.cycles } 184183
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1314.table, code := 9921120951736743105747417378268123201,
        encodes := Ra1314.tableCode_eq ▸ encodesTable_tableCode Ra1314.cycles } 184189
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1315.table, code := 9921120951736743105819475045320495169,
        encodes := Ra1315.tableCode_eq ▸ encodesTable_tableCode Ra1315.cycles } 184191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1316.table, code := 9918281416877780992877936614406623297,
        encodes := Ra1316.tableCode_eq ▸ encodesTable_tableCode Ra1316.cycles } 184231
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1317.table, code := 9918362546513777747920471321225728065,
        encodes := Ra1317.tableCode_eq ▸ encodesTable_tableCode Ra1317.cycles } 184234
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1318.table, code := 9918362546513777747920471323373211713,
        encodes := Ra1318.tableCode_eq ▸ encodesTable_tableCode Ra1318.cycles } 184235
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1319.table, code := 9918362546516195599559702787188330561,
        encodes := Ra1319.tableCode_eq ▸ encodesTable_tableCode Ra1319.cycles } 184238
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1320.table, code := 9918362546516195599559702789335814209,
        encodes := Ra1320.tableCode_eq ▸ encodesTable_tableCode Ra1320.cycles } 184239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1321.table, code := 9918281416877780995327894949135126593,
        encodes := Ra1321.tableCode_eq ▸ encodesTable_tableCode Ra1321.cycles } 184247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1322.table, code := 9918362546513777750370429655954231361,
        encodes := Ra1322.tableCode_eq ▸ encodesTable_tableCode Ra1322.cycles } 184250
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1323.table, code := 9918362546513777750370429658101715009,
        encodes := Ra1323.tableCode_eq ▸ encodesTable_tableCode Ra1323.cycles } 184251
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1324.table, code := 9918362546516195602009661121916833857,
        encodes := Ra1324.tableCode_eq ▸ encodesTable_tableCode Ra1324.cycles } 184254
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1325.table, code := 9918362546516195602009661124064317505,
        encodes := Ra1325.tableCode_eq ▸ encodesTable_tableCode Ra1325.cycles } 184255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1326.table, code := 9921039824501672952006430785009881153,
        encodes := Ra1326.tableCode_eq ▸ encodesTable_tableCode Ra1326.cycles } 184262
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1327.table, code := 9921039824501672952006430787157364801,
        encodes := Ra1327.tableCode_eq ▸ encodesTable_tableCode Ra1327.cycles } 184263
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1328.table, code := 9921120954140087558688196959939072065,
        encodes := Ra1328.tableCode_eq ▸ encodesTable_tableCode Ra1328.cycles } 184270
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1329.table, code := 9921120954140087558688196962086555713,
        encodes := Ra1329.tableCode_eq ▸ encodesTable_tableCode Ra1329.cycles } 184271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1330.table, code := 9921039824501672954456389119738384449,
        encodes := Ra1330.tableCode_eq ▸ encodesTable_tableCode Ra1330.cycles } 184278
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1331.table, code := 9921039824501672954456389121885868097,
        encodes := Ra1331.tableCode_eq ▸ encodesTable_tableCode Ra1331.cycles } 184279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1332.table, code := 9921120954140087561066097627615203393,
        encodes := Ra1332.tableCode_eq ▸ encodesTable_tableCode Ra1332.cycles } 184284
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1333.table, code := 9921120954140087561066097629762687041,
        encodes := Ra1333.tableCode_eq ▸ encodesTable_tableCode Ra1333.cycles } 184285
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1334.table, code := 9921120954140087561138155294667575361,
        encodes := Ra1334.tableCode_eq ▸ encodesTable_tableCode Ra1334.cycles } 184286
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1335.table, code := 9921120954140087561138155296815059009,
        encodes := Ra1335.tableCode_eq ▸ encodesTable_tableCode Ra1335.cycles } 184287
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1336.table, code := 9921039824581462130176205448989118529,
        encodes := Ra1336.tableCode_eq ▸ encodesTable_tableCode Ra1336.cycles } 184291
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1337.table, code := 9921039824583879981815436912804237377,
        encodes := Ra1337.tableCode_eq ▸ encodesTable_tableCode Ra1337.cycles } 184294
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1338.table, code := 9921039824583879981815436914951721025,
        encodes := Ra1338.tableCode_eq ▸ encodesTable_tableCode Ra1338.cycles } 184295
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1339.table, code := 9921120954219876736857971621770825793,
        encodes := Ra1339.tableCode_eq ▸ encodesTable_tableCode Ra1339.cycles } 184298
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1340.table, code := 9921120954219876736857971623918309441,
        encodes := Ra1340.tableCode_eq ▸ encodesTable_tableCode Ra1340.cycles } 184299
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1341.table, code := 9921120954222294588497203087733428289,
        encodes := Ra1341.tableCode_eq ▸ encodesTable_tableCode Ra1341.cycles } 184302
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1342.table, code := 9921120954222294588497203089880911937,
        encodes := Ra1342.tableCode_eq ▸ encodesTable_tableCode Ra1342.cycles } 184303
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1343.table, code := 9921039824581462132554106116665249857,
        encodes := Ra1343.tableCode_eq ▸ encodesTable_tableCode Ra1343.cycles } 184305
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1344.table, code := 9921039824581462132626163783717621825,
        encodes := Ra1344.tableCode_eq ▸ encodesTable_tableCode Ra1344.cycles } 184307
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1280 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1280 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1280 + i.val) 0 ≤ Data.profiles (1280 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1280 + i.val) 0 = Data.canonicalMask (1280 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1280 + i.val) < Data.canonicalMask (1280 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1280 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models020
