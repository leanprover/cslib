/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1153
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1154
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1155
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1156
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1157
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1158
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1159
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1160
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1161
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1162
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1163
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1164
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1165
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1166
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1167
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1168
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1169
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1170
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1171
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1172
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1173
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1174
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1175
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1176
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1177
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1178
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1179
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1180
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1181
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1182
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1183
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1184
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1185
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1186
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1187
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1188
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1189
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1190
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1191
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1192
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1193
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1194
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1195
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1196
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1197
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1198
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1199
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1200
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1201
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1202
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1203
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1204
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1205
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1206
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1207
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1208
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1209
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1210
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1211
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1212
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1213
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1214
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1215
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1216

/-!
# Certified models 1153–1216 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models018

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1153.table, code := 9741743167151036055773839994229362753,
        encodes := Ra1153.tableCode_eq ▸ encodesTable_tableCode Ra1153.cycles } 173830
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1154.table, code := 9741743167151036055773839996376846401,
        encodes := Ra1154.tableCode_eq ▸ encodesTable_tableCode Ra1154.cycles } 173831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1155.table, code := 9741824296789450662455606169158553665,
        encodes := Ra1155.tableCode_eq ▸ encodesTable_tableCode Ra1155.cycles } 173838
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1156.table, code := 9741824296789450662455606171306037313,
        encodes := Ra1156.tableCode_eq ▸ encodesTable_tableCode Ra1156.cycles } 173839
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1157.table, code := 9744501574939342076898247092392431681,
        encodes := Ra1157.tableCode_eq ▸ encodesTable_tableCode Ra1157.cycles } 173941
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1158.table, code := 9744501574939342076970304759444803649,
        encodes := Ra1158.tableCode_eq ▸ encodesTable_tableCode Ra1158.cycles } 173943
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1159.table, code := 9744582704577756683580013265174138945,
        encodes := Ra1159.tableCode_eq ▸ encodesTable_tableCode Ra1159.cycles } 173948
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1160.table, code := 9744582704577756683580013267321622593,
        encodes := Ra1160.tableCode_eq ▸ encodesTable_tableCode Ra1160.cycles } 173949
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1161.table, code := 9744582704577756683652070932226510913,
        encodes := Ra1161.tableCode_eq ▸ encodesTable_tableCode Ra1161.cycles } 173950
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1162.table, code := 9744582704577756683652070934373994561,
        encodes := Ra1162.tableCode_eq ▸ encodesTable_tableCode Ra1162.cycles } 173951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1163.table, code := 9741743169636587540901526375665766465,
        encodes := Ra1163.tableCode_eq ▸ encodesTable_tableCode Ra1163.cycles } 173959
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1164.table, code := 9741824299275002147583292548447473729,
        encodes := Ra1164.tableCode_eq ▸ encodesTable_tableCode Ra1164.cycles } 173966
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1165.table, code := 9741824299275002147583292550594957377,
        encodes := Ra1165.tableCode_eq ▸ encodesTable_tableCode Ra1165.cycles } 173967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1166.table, code := 9744501577422475710386702005718749249,
        encodes := Ra1166.tableCode_eq ▸ encodesTable_tableCode Ra1166.cycles } 174065
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1167.table, code := 9744501577422475710458759672771121217,
        encodes := Ra1167.tableCode_eq ▸ encodesTable_tableCode Ra1167.cycles } 174067
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1168.table, code := 9744501577424893562025933471681351745,
        encodes := Ra1168.tableCode_eq ▸ encodesTable_tableCode Ra1168.cycles } 174069
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1169.table, code := 9744501577424893562097991138733723713,
        encodes := Ra1169.tableCode_eq ▸ encodesTable_tableCode Ra1169.cycles } 174071
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1170.table, code := 9744582707060890317068468180647940161,
        encodes := Ra1170.tableCode_eq ▸ encodesTable_tableCode Ra1170.cycles } 174073
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1171.table, code := 9744582707060890317140525847700312129,
        encodes := Ra1171.tableCode_eq ▸ encodesTable_tableCode Ra1171.cycles } 174075
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1172.table, code := 9744582707063308168707699644463059009,
        encodes := Ra1172.tableCode_eq ▸ encodesTable_tableCode Ra1172.cycles } 174076
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1173.table, code := 9744582707063308168707699646610542657,
        encodes := Ra1173.tableCode_eq ▸ encodesTable_tableCode Ra1173.cycles } 174077
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1174.table, code := 9744582707063308168779757311515430977,
        encodes := Ra1174.tableCode_eq ▸ encodesTable_tableCode Ra1174.cycles } 174078
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1175.table, code := 9744582707063308168779757313662914625,
        encodes := Ra1175.tableCode_eq ▸ encodesTable_tableCode Ra1175.cycles } 174079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1176.table, code := 9744501575094084736228343585609879617,
        encodes := Ra1176.tableCode_eq ▸ encodesTable_tableCode Ra1176.cycles } 175975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1177.table, code := 9744582704732499342910109758391586881,
        encodes := Ra1177.tableCode_eq ▸ encodesTable_tableCode Ra1177.cycles } 175982
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1178.table, code := 9744582704732499342910109760539070529,
        encodes := Ra1178.tableCode_eq ▸ encodesTable_tableCode Ra1178.cycles } 175983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1179.table, code := 9744501575094084738606244253286010945,
        encodes := Ra1179.tableCode_eq ▸ encodesTable_tableCode Ra1179.cycles } 175989
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1180.table, code := 9744501575094084738678301920338382913,
        encodes := Ra1180.tableCode_eq ▸ encodesTable_tableCode Ra1180.cycles } 175991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1181.table, code := 9744582704732499345288010426067718209,
        encodes := Ra1181.tableCode_eq ▸ encodesTable_tableCode Ra1181.cycles } 175996
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1182.table, code := 9744582704732499345288010428215201857,
        encodes := Ra1182.tableCode_eq ▸ encodesTable_tableCode Ra1182.cycles } 175997
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1183.table, code := 9744582704732499345360068093120090177,
        encodes := Ra1183.tableCode_eq ▸ encodesTable_tableCode Ra1183.cycles } 175998
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1184.table, code := 9744582704732499345360068095267573825,
        encodes := Ra1184.tableCode_eq ▸ encodesTable_tableCode Ra1184.cycles } 175999
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1185.table, code := 9744501577577218369716798498936197185,
        encodes := Ra1185.tableCode_eq ▸ encodesTable_tableCode Ra1185.cycles } 176099
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1186.table, code := 9744501577579636221356029964898799681,
        encodes := Ra1186.tableCode_eq ▸ encodesTable_tableCode Ra1186.cycles } 176103
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1187.table, code := 9744582707215632976398564673865388097,
        encodes := Ra1187.tableCode_eq ▸ encodesTable_tableCode Ra1187.cycles } 176107
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1188.table, code := 9744582707218050828037796137680506945,
        encodes := Ra1188.tableCode_eq ▸ encodesTable_tableCode Ra1188.cycles } 176110
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1189.table, code := 9744582707218050828037796139827990593,
        encodes := Ra1189.tableCode_eq ▸ encodesTable_tableCode Ra1189.cycles } 176111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1190.table, code := 9744501577577218372094699166612328513,
        encodes := Ra1190.tableCode_eq ▸ encodesTable_tableCode Ra1190.cycles } 176113
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1191.table, code := 9744501577577218372166756833664700481,
        encodes := Ra1191.tableCode_eq ▸ encodesTable_tableCode Ra1191.cycles } 176115
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1192.table, code := 9744501577579636223733930632574931009,
        encodes := Ra1192.tableCode_eq ▸ encodesTable_tableCode Ra1192.cycles } 176117
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1193.table, code := 9744501577579636223805988299627302977,
        encodes := Ra1193.tableCode_eq ▸ encodesTable_tableCode Ra1193.cycles } 176119
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1194.table, code := 9744582707215632978776465341541519425,
        encodes := Ra1194.tableCode_eq ▸ encodesTable_tableCode Ra1194.cycles } 176121
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1195.table, code := 9744582707215632978848523008593891393,
        encodes := Ra1195.tableCode_eq ▸ encodesTable_tableCode Ra1195.cycles } 176123
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1196.table, code := 9744582707218050830415696805356638273,
        encodes := Ra1196.tableCode_eq ▸ encodesTable_tableCode Ra1196.cycles } 176124
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1197.table, code := 9744582707218050830415696807504121921,
        encodes := Ra1197.tableCode_eq ▸ encodesTable_tableCode Ra1197.cycles } 176125
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1198.table, code := 9744582707218050830487754472409010241,
        encodes := Ra1198.tableCode_eq ▸ encodesTable_tableCode Ra1198.cycles } 176126
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1199.table, code := 9744582707218050830487754474556493889,
        encodes := Ra1199.tableCode_eq ▸ encodesTable_tableCode Ra1199.cycles } 176127
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1200.table, code := 9663615248593402866062349013679870017,
        encodes := Ra1200.tableCode_eq ▸ encodesTable_tableCode Ra1200.cycles } 176794
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1201.table, code := 9663615248593402866062349015827353665,
        encodes := Ra1201.tableCode_eq ▸ encodesTable_tableCode Ra1201.cycles } 176795
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1202.table, code := 9666373656299501854999849314224967745,
        encodes := Ra1202.tableCode_eq ▸ encodesTable_tableCode Ra1202.cycles } 176858
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1203.table, code := 9666373656299501854999849316372451393,
        encodes := Ra1203.tableCode_eq ▸ encodesTable_tableCode Ra1203.cycles } 176859
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1204.table, code := 9749693871797881640728318513649029185,
        encodes := Ra1204.tableCode_eq ▸ encodesTable_tableCode Ra1204.cycles } 177013
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1205.table, code := 9749693871797881640800376178553917505,
        encodes := Ra1205.tableCode_eq ▸ encodesTable_tableCode Ra1205.cycles } 177014
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1206.table, code := 9749693871797881640800376180701401153,
        encodes := Ra1206.tableCode_eq ▸ encodesTable_tableCode Ra1206.cycles } 177015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1207.table, code := 9749775001436296247482142353483108417,
        encodes := Ra1207.tableCode_eq ▸ encodesTable_tableCode Ra1207.cycles } 177022
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1208.table, code := 9749775001436296247482142355630592065,
        encodes := Ra1208.tableCode_eq ▸ encodesTable_tableCode Ra1208.cycles } 177023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1209.table, code := 9749693874281015274216773426975346753,
        encodes := Ra1209.tableCode_eq ▸ encodesTable_tableCode Ra1209.cycles } 177137
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1210.table, code := 9749693874281015274288831094027718721,
        encodes := Ra1210.tableCode_eq ▸ encodesTable_tableCode Ra1210.cycles } 177139
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1211.table, code := 9749693874283433125856004892937949249,
        encodes := Ra1211.tableCode_eq ▸ encodesTable_tableCode Ra1211.cycles } 177141
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1212.table, code := 9749693874283433125928062557842837569,
        encodes := Ra1212.tableCode_eq ▸ encodesTable_tableCode Ra1212.cycles } 177142
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1213.table, code := 9749693874283433125928062559990321217,
        encodes := Ra1213.tableCode_eq ▸ encodesTable_tableCode Ra1213.cycles } 177143
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1214.table, code := 9749775003919429880970597268956909633,
        encodes := Ra1214.tableCode_eq ▸ encodesTable_tableCode Ra1214.cycles } 177147
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1215.table, code := 9749775003921847732609828732772028481,
        encodes := Ra1215.tableCode_eq ▸ encodesTable_tableCode Ra1215.cycles } 177150
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1216.table, code := 9749775003921847732609828734919512129,
        encodes := Ra1216.tableCode_eq ▸ encodesTable_tableCode Ra1216.cycles } 177151
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1152 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1152 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
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

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models018
