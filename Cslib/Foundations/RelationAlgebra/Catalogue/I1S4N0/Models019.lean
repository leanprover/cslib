/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1217
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1218
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1219
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1220
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1221
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1222
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1223
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1224
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1225
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1226
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1227
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1228
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1229
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1230
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1231
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1232
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1233
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1234
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1235
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1236
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1237
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1238
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1239
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1240
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1241
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1242
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1243
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1244
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1245
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1246
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1247
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1248
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1249
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1250
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1251
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1252
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1253
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1254
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1255
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1256
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1257
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1258
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1259
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1260
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1261
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1262
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1263
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1264
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1265
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1266
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1267
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1268
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1269
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1270
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1271
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1272
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1273
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1274
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1275
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1276
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1277
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1278
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1279
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1280

/-!
# Certified models 1217–1280 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models019

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1217.table, code := 9663615248593402870674035034254741569,
        encodes := Ra1217.tableCode_eq ▸ encodesTable_tableCode Ra1217.cycles } 177819
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1218.table, code := 9666373656299501857161577000071336001,
        encodes := Ra1218.tableCode_eq ▸ encodesTable_tableCode Ra1218.cycles } 177867
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1219.table, code := 9666373656299501859611535334799839297,
        encodes := Ra1219.tableCode_eq ▸ encodesTable_tableCode Ra1219.cycles } 177883
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1220.table, code := 9749693871797881645340004532076417089,
        encodes := Ra1220.tableCode_eq ▸ encodesTable_tableCode Ra1220.cycles } 178037
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1221.table, code := 9749693871797881645412062196981305409,
        encodes := Ra1221.tableCode_eq ▸ encodesTable_tableCode Ra1221.cycles } 178038
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1222.table, code := 9749693871797881645412062199128789057,
        encodes := Ra1222.tableCode_eq ▸ encodesTable_tableCode Ra1222.cycles } 178039
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1223.table, code := 9749775001436296252021770704858124353,
        encodes := Ra1223.tableCode_eq ▸ encodesTable_tableCode Ra1223.cycles } 178044
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1224.table, code := 9749775001436296252021770707005608001,
        encodes := Ra1224.tableCode_eq ▸ encodesTable_tableCode Ra1224.cycles } 178045
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1225.table, code := 9749775001436296252093828371910496321,
        encodes := Ra1225.tableCode_eq ▸ encodesTable_tableCode Ra1225.cycles } 178046
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1226.table, code := 9749775001436296252093828374057979969,
        encodes := Ra1226.tableCode_eq ▸ encodesTable_tableCode Ra1226.cycles } 178047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1227.table, code := 9749693874281015278828459445402734657,
        encodes := Ra1227.tableCode_eq ▸ encodesTable_tableCode Ra1227.cycles } 178161
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1228.table, code := 9749693874281015278900517112455106625,
        encodes := Ra1228.tableCode_eq ▸ encodesTable_tableCode Ra1228.cycles } 178163
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1229.table, code := 9749693874283433130467690911365337153,
        encodes := Ra1229.tableCode_eq ▸ encodesTable_tableCode Ra1229.cycles } 178165
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1230.table, code := 9749693874283433130539748576270225473,
        encodes := Ra1230.tableCode_eq ▸ encodesTable_tableCode Ra1230.cycles } 178166
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1231.table, code := 9749693874283433130539748578417709121,
        encodes := Ra1231.tableCode_eq ▸ encodesTable_tableCode Ra1231.cycles } 178167
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1232.table, code := 9749775003919429885510225620331925569,
        encodes := Ra1232.tableCode_eq ▸ encodesTable_tableCode Ra1232.cycles } 178169
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1233.table, code := 9749775003919429885582283287384297537,
        encodes := Ra1233.tableCode_eq ▸ encodesTable_tableCode Ra1233.cycles } 178171
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1234.table, code := 9749775003921847737149457084147044417,
        encodes := Ra1234.tableCode_eq ▸ encodesTable_tableCode Ra1234.cycles } 178172
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1235.table, code := 9749775003921847737149457086294528065,
        encodes := Ra1235.tableCode_eq ▸ encodesTable_tableCode Ra1235.cycles } 178173
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1236.table, code := 9749775003921847737221514751199416385,
        encodes := Ra1236.tableCode_eq ▸ encodesTable_tableCode Ra1236.cycles } 178174
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1237.table, code := 9749775003921847737221514753346900033,
        encodes := Ra1237.tableCode_eq ▸ encodesTable_tableCode Ra1237.cycles } 178175
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1238.table, code := 9749693871952624300058415004718993473,
        encodes := Ra1238.tableCode_eq ▸ encodesTable_tableCode Ra1238.cycles } 179046
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1239.table, code := 9749693871952624300058415006866477121,
        encodes := Ra1239.tableCode_eq ▸ encodesTable_tableCode Ra1239.cycles } 179047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1240.table, code := 9749775001591038906740181179648184385,
        encodes := Ra1240.tableCode_eq ▸ encodesTable_tableCode Ra1240.cycles } 179054
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1241.table, code := 9749775001591038906740181181795668033,
        encodes := Ra1241.tableCode_eq ▸ encodesTable_tableCode Ra1241.cycles } 179055
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1242.table, code := 9749693871952624302436315674542608449,
        encodes := Ra1242.tableCode_eq ▸ encodesTable_tableCode Ra1242.cycles } 179061
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1243.table, code := 9749693871952624302508373339447496769,
        encodes := Ra1243.tableCode_eq ▸ encodesTable_tableCode Ra1243.cycles } 179062
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1244.table, code := 9749693871952624302508373341594980417,
        encodes := Ra1244.tableCode_eq ▸ encodesTable_tableCode Ra1244.cycles } 179063
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1245.table, code := 9749775001591038909118081847324315713,
        encodes := Ra1245.tableCode_eq ▸ encodesTable_tableCode Ra1245.cycles } 179068
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1246.table, code := 9749775001591038909118081849471799361,
        encodes := Ra1246.tableCode_eq ▸ encodesTable_tableCode Ra1246.cycles } 179069
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1247.table, code := 9749775001591038909190139514376687681,
        encodes := Ra1247.tableCode_eq ▸ encodesTable_tableCode Ra1247.cycles } 179070
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1248.table, code := 9749775001591038909190139516524171329,
        encodes := Ra1248.tableCode_eq ▸ encodesTable_tableCode Ra1248.cycles } 179071
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1249.table, code := 9749693874355968757827053590942060609,
        encodes := Ra1249.tableCode_eq ▸ encodesTable_tableCode Ra1249.cycles } 179158
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1250.table, code := 9749693874355968757827053593089544257,
        encodes := Ra1250.tableCode_eq ▸ encodesTable_tableCode Ra1250.cycles } 179159
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1251.table, code := 9749775003994383364508819765871251521,
        encodes := Ra1251.tableCode_eq ▸ encodesTable_tableCode Ra1251.cycles } 179166
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1252.table, code := 9749775003994383364508819768018735169,
        encodes := Ra1252.tableCode_eq ▸ encodesTable_tableCode Ra1252.cycles } 179167
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1253.table, code := 9749693874435757933546869920192794689,
        encodes := Ra1253.tableCode_eq ▸ encodesTable_tableCode Ra1253.cycles } 179171
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1254.table, code := 9749693874438175785186101384007913537,
        encodes := Ra1254.tableCode_eq ▸ encodesTable_tableCode Ra1254.cycles } 179174
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1255.table, code := 9749693874438175785186101386155397185,
        encodes := Ra1255.tableCode_eq ▸ encodesTable_tableCode Ra1255.cycles } 179175
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1256.table, code := 9749775004074172540228636095121985601,
        encodes := Ra1256.tableCode_eq ▸ encodesTable_tableCode Ra1256.cycles } 179179
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1257.table, code := 9749775004076590391867867558937104449,
        encodes := Ra1257.tableCode_eq ▸ encodesTable_tableCode Ra1257.cycles } 179182
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1258.table, code := 9749775004076590391867867561084588097,
        encodes := Ra1258.tableCode_eq ▸ encodesTable_tableCode Ra1258.cycles } 179183
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1259.table, code := 9749693874435757935924770587868926017,
        encodes := Ra1259.tableCode_eq ▸ encodesTable_tableCode Ra1259.cycles } 179185
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1260.table, code := 9749693874435757935996828254921297985,
        encodes := Ra1260.tableCode_eq ▸ encodesTable_tableCode Ra1260.cycles } 179187
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1261.table, code := 9749693874438175787564002053831528513,
        encodes := Ra1261.tableCode_eq ▸ encodesTable_tableCode Ra1261.cycles } 179189
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1262.table, code := 9749693874438175787636059718736416833,
        encodes := Ra1262.tableCode_eq ▸ encodesTable_tableCode Ra1262.cycles } 179190
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1263.table, code := 9749693874438175787636059720883900481,
        encodes := Ra1263.tableCode_eq ▸ encodesTable_tableCode Ra1263.cycles } 179191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1264.table, code := 9749775004074172542606536762798116929,
        encodes := Ra1264.tableCode_eq ▸ encodesTable_tableCode Ra1264.cycles } 179193
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1265.table, code := 9749775004074172542678594429850488897,
        encodes := Ra1265.tableCode_eq ▸ encodesTable_tableCode Ra1265.cycles } 179195
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1266.table, code := 9749775004076590394245768226613235777,
        encodes := Ra1266.tableCode_eq ▸ encodesTable_tableCode Ra1266.cycles } 179196
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1267.table, code := 9749775004076590394245768228760719425,
        encodes := Ra1267.tableCode_eq ▸ encodesTable_tableCode Ra1267.cycles } 179197
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1268.table, code := 9749775004076590394317825893665607745,
        encodes := Ra1268.tableCode_eq ▸ encodesTable_tableCode Ra1268.cycles } 179198
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1269.table, code := 9749775004076590394317825895813091393,
        encodes := Ra1269.tableCode_eq ▸ encodesTable_tableCode Ra1269.cycles } 179199
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1270.table, code := 9749693871952624304670101023146381377,
        encodes := Ra1270.tableCode_eq ▸ encodesTable_tableCode Ra1270.cycles } 180070
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1271.table, code := 9749693871952624304670101025293865025,
        encodes := Ra1271.tableCode_eq ▸ encodesTable_tableCode Ra1271.cycles } 180071
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1272.table, code := 9749775001591038911351867198075572289,
        encodes := Ra1272.tableCode_eq ▸ encodesTable_tableCode Ra1272.cycles } 180078
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1273.table, code := 9749775001591038911351867200223055937,
        encodes := Ra1273.tableCode_eq ▸ encodesTable_tableCode Ra1273.cycles } 180079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1274.table, code := 9749693871952624307048001692969996353,
        encodes := Ra1274.tableCode_eq ▸ encodesTable_tableCode Ra1274.cycles } 180085
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1275.table, code := 9749693871952624307120059357874884673,
        encodes := Ra1275.tableCode_eq ▸ encodesTable_tableCode Ra1275.cycles } 180086
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1276.table, code := 9749693871952624307120059360022368321,
        encodes := Ra1276.tableCode_eq ▸ encodesTable_tableCode Ra1276.cycles } 180087
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1277.table, code := 9749775001591038913729767865751703617,
        encodes := Ra1277.tableCode_eq ▸ encodesTable_tableCode Ra1277.cycles } 180092
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1278.table, code := 9749775001591038913729767867899187265,
        encodes := Ra1278.tableCode_eq ▸ encodesTable_tableCode Ra1278.cycles } 180093
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1279.table, code := 9749775001591038913801825532804075585,
        encodes := Ra1279.tableCode_eq ▸ encodesTable_tableCode Ra1279.cycles } 180094
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1280.table, code := 9749775001591038913801825534951559233,
        encodes := Ra1280.tableCode_eq ▸ encodesTable_tableCode Ra1280.cycles } 180095
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1216 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1216 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
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

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models019
