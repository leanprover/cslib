/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1153
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1154
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1155
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1156
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1157
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1158
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1159
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1160
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1161
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1162
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1163
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1164
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1165
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1166
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1167
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1168
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1169
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1170
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1171
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1172
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1173
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1174
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1175
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1176
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1177
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1178
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1179
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1180
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1181
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1182
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1183
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1184
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1185
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1186
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1187
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1188
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1189
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1190
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1191
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1192
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1193
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1194
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1195
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1196
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1197
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1198
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1199
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1200
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1201
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1202
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1203
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1204
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1205
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1206
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1207
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1208
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1209
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1210
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1211
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1212
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1213
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1214
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1215
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1216

/-!
# Certified models 1153–1216 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models018

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1153.table, code := 38379695072218678993621432200660783169,
        encodes := Ra1153.tableCode_eq ▸ encodesTable_tableCode Ra1153.cycles } 57202
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1154.table, code := 38379695072218678993621432202808266817,
        encodes := Ra1154.tableCode_eq ▸ encodesTable_tableCode Ra1154.cycles } 57203
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1155.table, code := 38379776201859511451870372174500204609,
        encodes := Ra1155.tableCode_eq ▸ encodesTable_tableCode Ra1155.cycles } 57204
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1156.table, code := 38379776201859511451870372176647688257,
        encodes := Ra1156.tableCode_eq ▸ encodesTable_tableCode Ra1156.cycles } 57205
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1157.table, code := 38379776201859511451942429841552576577,
        encodes := Ra1157.tableCode_eq ▸ encodesTable_tableCode Ra1157.cycles } 57206
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1158.table, code := 38379776201859511451942429843700060225,
        encodes := Ra1158.tableCode_eq ▸ encodesTable_tableCode Ra1158.cycles } 57207
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1159.table, code := 38379695072218678996071390535389286465,
        encodes := Ra1159.tableCode_eq ▸ encodesTable_tableCode Ra1159.cycles } 57210
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1160.table, code := 38379695072218678996071390537536770113,
        encodes := Ra1160.tableCode_eq ▸ encodesTable_tableCode Ra1160.cycles } 57211
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1161.table, code := 38379776201859511454320330509228707905,
        encodes := Ra1161.tableCode_eq ▸ encodesTable_tableCode Ra1161.cycles } 57212
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1162.table, code := 38379776201859511454320330511376191553,
        encodes := Ra1162.tableCode_eq ▸ encodesTable_tableCode Ra1162.cycles } 57213
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1163.table, code := 38379776201859511454392388176281079873,
        encodes := Ra1163.tableCode_eq ▸ encodesTable_tableCode Ra1163.cycles } 57214
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1164.table, code := 38379776201859511454392388178428563521,
        encodes := Ra1164.tableCode_eq ▸ encodesTable_tableCode Ra1164.cycles } 57215
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1165.table, code := 41035311449708641957275736379261980737,
        encodes := Ra1165.tableCode_eq ▸ encodesTable_tableCode Ra1165.cycles } 57239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1166.table, code := 41035311449708641959725694713990484033,
        encodes := Ra1166.tableCode_eq ▸ encodesTable_tableCode Ra1166.cycles } 57247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1167.table, code := 41037907598142745148371750435307130945,
        encodes := Ra1167.tableCode_eq ▸ encodesTable_tableCode Ra1167.cycles } 57269
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1168.table, code := 41037907598142745148443808102359502913,
        encodes := Ra1168.tableCode_eq ▸ encodesTable_tableCode Ra1168.cycles } 57271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1169.table, code := 41037907598142745150893766437088006209,
        encodes := Ra1169.tableCode_eq ▸ encodesTable_tableCode Ra1169.cycles } 57279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1170.table, code := 41035798306689918499865172708279193665,
        encodes := Ra1170.tableCode_eq ▸ encodesTable_tableCode Ra1170.cycles } 57294
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1171.table, code := 41035798306689918499865172710426677313,
        encodes := Ra1171.tableCode_eq ▸ encodesTable_tableCode Ra1171.cycles } 57295
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1172.table, code := 41035960566044121324993649078792622145,
        encodes := Ra1172.tableCode_eq ▸ encodesTable_tableCode Ra1172.cycles } 57302
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1173.table, code := 41035960566044121324993649080940105793,
        encodes := Ra1173.tableCode_eq ▸ encodesTable_tableCode Ra1173.cycles } 57303
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1174.table, code := 41035960566044121327371549746468753473,
        encodes := Ra1174.tableCode_eq ▸ encodesTable_tableCode Ra1174.cycles } 57308
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1175.table, code := 41035960566044121327371549748616237121,
        encodes := Ra1175.tableCode_eq ▸ encodesTable_tableCode Ra1175.cycles } 57309
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1176.table, code := 41035960566044121327443607413521125441,
        encodes := Ra1176.tableCode_eq ▸ encodesTable_tableCode Ra1176.cycles } 57310
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1177.table, code := 41035960566044121327443607415668609089,
        encodes := Ra1177.tableCode_eq ▸ encodesTable_tableCode Ra1177.cycles } 57311
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1178.table, code := 41038394455124021690961186764324343873,
        encodes := Ra1178.tableCode_eq ▸ encodesTable_tableCode Ra1178.cycles } 57324
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1179.table, code := 41038394455124021690961186766471827521,
        encodes := Ra1179.tableCode_eq ▸ encodesTable_tableCode Ra1179.cycles } 57325
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1180.table, code := 41038394455124021691033244431376715841,
        encodes := Ra1180.tableCode_eq ▸ encodesTable_tableCode Ra1180.cycles } 57326
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1181.table, code := 41038394455124021691033244433524199489,
        encodes := Ra1181.tableCode_eq ▸ encodesTable_tableCode Ra1181.cycles } 57327
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1182.table, code := 41038475584837392057768665496093462593,
        encodes := Ra1182.tableCode_eq ▸ encodesTable_tableCode Ra1182.cycles } 57329
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1183.table, code := 41038475584837392057840723160998350913,
        encodes := Ra1183.tableCode_eq ▸ encodesTable_tableCode Ra1183.cycles } 57330
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1184.table, code := 41038475584837392057840723163145834561,
        encodes := Ra1184.tableCode_eq ▸ encodesTable_tableCode Ra1184.cycles } 57331
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1185.table, code := 41038556714478224516089663134837772353,
        encodes := Ra1185.tableCode_eq ▸ encodesTable_tableCode Ra1185.cycles } 57332
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1186.table, code := 41038556714478224516089663136985256001,
        encodes := Ra1186.tableCode_eq ▸ encodesTable_tableCode Ra1186.cycles } 57333
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1187.table, code := 41038556714478224516161720801890144321,
        encodes := Ra1187.tableCode_eq ▸ encodesTable_tableCode Ra1187.cycles } 57334
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1188.table, code := 41038556714478224516161720804037627969,
        encodes := Ra1188.tableCode_eq ▸ encodesTable_tableCode Ra1188.cycles } 57335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1189.table, code := 41038475584837392060218623830821965889,
        encodes := Ra1189.tableCode_eq ▸ encodesTable_tableCode Ra1189.cycles } 57337
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1190.table, code := 41038475584837392060290681495726854209,
        encodes := Ra1190.tableCode_eq ▸ encodesTable_tableCode Ra1190.cycles } 57338
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1191.table, code := 41038475584837392060290681497874337857,
        encodes := Ra1191.tableCode_eq ▸ encodesTable_tableCode Ra1191.cycles } 57339
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1192.table, code := 41038556714478224518539621469566275649,
        encodes := Ra1192.tableCode_eq ▸ encodesTable_tableCode Ra1192.cycles } 57340
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1193.table, code := 41038556714478224518539621471713759297,
        encodes := Ra1193.tableCode_eq ▸ encodesTable_tableCode Ra1193.cycles } 57341
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1194.table, code := 41038556714478224518611679136618647617,
        encodes := Ra1194.tableCode_eq ▸ encodesTable_tableCode Ra1194.cycles } 57342
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1195.table, code := 41038556714478224518611679138766131265,
        encodes := Ra1195.tableCode_eq ▸ encodesTable_tableCode Ra1195.cycles } 57343
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1196.table, code := 33210601284772235764828461014335098945,
        encodes := Ra1196.tableCode_eq ▸ encodesTable_tableCode Ra1196.cycles } 59714
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1197.table, code := 33210601284772235764828461016482582593,
        encodes := Ra1197.tableCode_eq ▸ encodesTable_tableCode Ra1197.cycles } 59715
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1198.table, code := 33210682414413068223149458655226892353,
        encodes := Ra1198.tableCode_eq ▸ encodesTable_tableCode Ra1198.cycles } 59718
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1199.table, code := 33210682414413068223149458657374376001,
        encodes := Ra1199.tableCode_eq ▸ encodesTable_tableCode Ra1199.cycles } 59719
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1200.table, code := 33210601284772235767206361684158713921,
        encodes := Ra1200.tableCode_eq ▸ encodesTable_tableCode Ra1200.cycles } 59721
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1201.table, code := 33210601284772235767278419349063602241,
        encodes := Ra1201.tableCode_eq ▸ encodesTable_tableCode Ra1201.cycles } 59722
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1202.table, code := 33210601284772235767278419351211085889,
        encodes := Ra1202.tableCode_eq ▸ encodesTable_tableCode Ra1202.cycles } 59723
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1203.table, code := 35869381797390948829047751976820150337,
        encodes := Ra1203.tableCode_eq ▸ encodesTable_tableCode Ra1203.cycles } 59843
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1204.table, code := 35869462927031781287368749615564460097,
        encodes := Ra1204.tableCode_eq ▸ encodesTable_tableCode Ra1204.cycles } 59846
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1205.table, code := 35869462927031781287368749617711943745,
        encodes := Ra1205.tableCode_eq ▸ encodesTable_tableCode Ra1205.cycles } 59847
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1206.table, code := 35872221334820087308493156711580045377,
        encodes := Ra1206.tableCode_eq ▸ encodesTable_tableCode Ra1206.cycles } 59900
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1207.table, code := 35872221334820087308493156713727529025,
        encodes := Ra1207.tableCode_eq ▸ encodesTable_tableCode Ra1207.cycles } 59901
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1208.table, code := 35872221334820087308565214378632417345,
        encodes := Ra1208.tableCode_eq ▸ encodesTable_tableCode Ra1208.cycles } 59902
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1209.table, code := 35872221334820087308565214380779900993,
        encodes := Ra1209.tableCode_eq ▸ encodesTable_tableCode Ra1209.cycles } 59903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1210.table, code := 33210601284772235769440147034909970497,
        encodes := Ra1210.tableCode_eq ▸ encodesTable_tableCode Ra1210.cycles } 60227
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1211.table, code := 33210682414413068227761144673654280257,
        encodes := Ra1211.tableCode_eq ▸ encodesTable_tableCode Ra1211.cycles } 60230
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1212.table, code := 33210682414413068227761144675801763905,
        encodes := Ra1212.tableCode_eq ▸ encodesTable_tableCode Ra1212.cycles } 60231
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1213.table, code := 33210601284772235771890105369638473793,
        encodes := Ra1213.tableCode_eq ▸ encodesTable_tableCode Ra1213.cycles } 60235
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1214.table, code := 35869381797390948833659437995247538241,
        encodes := Ra1214.tableCode_eq ▸ encodesTable_tableCode Ra1214.cycles } 60355
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1215.table, code := 35869462927031781291980435633991848001,
        encodes := Ra1215.tableCode_eq ▸ encodesTable_tableCode Ra1215.cycles } 60358
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1216.table, code := 35869462927031781291980435636139331649,
        encodes := Ra1216.tableCode_eq ▸ encodesTable_tableCode Ra1216.cycles } 60359
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (1152 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1152 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (1152 + i.val) 0 ≤ Data.profiles (1152 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1152 + i.val) 0 = Data.canonicalMask (1152 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1152 + i.val) < Data.canonicalMask (1152 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1152 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models018
