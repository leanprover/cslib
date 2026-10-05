/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1089
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1090
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1091
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1092
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1093
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1094
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1095
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1096
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1097
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1098
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1099
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1100
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1101
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1102
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1103
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1104
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1105
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1106
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1107
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1108
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1109
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1110
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1111
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1112
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1113
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1114
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1115
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1116
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1117
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1118
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1119
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1120
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1121
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1122
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1123
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1124
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1125
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1126
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1127
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1128
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1129
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1130
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1131
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1132
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1133
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1134
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1135
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1136
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1137
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1138
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1139
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1140
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1141
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1142
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1143
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1144
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1145
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1146
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1147
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1148
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1149
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1150
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1151
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1152

/-!
# Certified models 1089–1152 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models017

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1089.table, code := 9744582699471253883249296747593470017,
        encodes := Ra1089.tableCode_eq ▸ encodesTable_tableCode Ra1089.cycles } 167807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1090.table, code := 9744501572315972907606027151262093377,
        encodes := Ra1090.tableCode_eq ▸ encodesTable_tableCode Ra1090.cycles } 167907
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1091.table, code := 9744501572318390759245258617224695873,
        encodes := Ra1091.tableCode_eq ▸ encodesTable_tableCode Ra1091.cycles } 167911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1092.table, code := 9744582701954387514287793326191284289,
        encodes := Ra1092.tableCode_eq ▸ encodesTable_tableCode Ra1092.cycles } 167915
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1093.table, code := 9744582701956805365927024790006403137,
        encodes := Ra1093.tableCode_eq ▸ encodesTable_tableCode Ra1093.cycles } 167918
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1094.table, code := 9744582701956805365927024792153886785,
        encodes := Ra1094.tableCode_eq ▸ encodesTable_tableCode Ra1094.cycles } 167919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1095.table, code := 9744501572315972909983927818938224705,
        encodes := Ra1095.tableCode_eq ▸ encodesTable_tableCode Ra1095.cycles } 167921
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1096.table, code := 9744501572315972910055985485990596673,
        encodes := Ra1096.tableCode_eq ▸ encodesTable_tableCode Ra1096.cycles } 167923
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1097.table, code := 9744501572318390761623159284900827201,
        encodes := Ra1097.tableCode_eq ▸ encodesTable_tableCode Ra1097.cycles } 167925
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1098.table, code := 9744501572318390761695216951953199169,
        encodes := Ra1098.tableCode_eq ▸ encodesTable_tableCode Ra1098.cycles } 167927
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1099.table, code := 9744582701954387516665693993867415617,
        encodes := Ra1099.tableCode_eq ▸ encodesTable_tableCode Ra1099.cycles } 167929
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1100.table, code := 9744582701954387516737751660919787585,
        encodes := Ra1100.tableCode_eq ▸ encodesTable_tableCode Ra1100.cycles } 167931
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1101.table, code := 9744582701956805368304925459830018113,
        encodes := Ra1101.tableCode_eq ▸ encodesTable_tableCode Ra1101.cycles } 167933
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1102.table, code := 9744582701956805368376983124734906433,
        encodes := Ra1102.tableCode_eq ▸ encodesTable_tableCode Ra1102.cycles } 167934
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1103.table, code := 9744582701956805368376983126882390081,
        encodes := Ra1103.tableCode_eq ▸ encodesTable_tableCode Ra1103.cycles } 167935
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1104.table, code := 9749693869174512471436098572518690881,
        encodes := Ra1104.tableCode_eq ▸ encodesTable_tableCode Ra1104.cycles } 170979
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1105.table, code := 9749693869176930323075330036333809729,
        encodes := Ra1105.tableCode_eq ▸ encodesTable_tableCode Ra1105.cycles } 170982
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1106.table, code := 9749693869176930323075330038481293377,
        encodes := Ra1106.tableCode_eq ▸ encodesTable_tableCode Ra1106.cycles } 170983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1107.table, code := 9749774998812927078117864747447881793,
        encodes := Ra1107.tableCode_eq ▸ encodesTable_tableCode Ra1107.cycles } 170987
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1108.table, code := 9749774998815344929757096211263000641,
        encodes := Ra1108.tableCode_eq ▸ encodesTable_tableCode Ra1108.cycles } 170990
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1109.table, code := 9749774998815344929757096213410484289,
        encodes := Ra1109.tableCode_eq ▸ encodesTable_tableCode Ra1109.cycles } 170991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1110.table, code := 9749693869174512473813999240194822209,
        encodes := Ra1110.tableCode_eq ▸ encodesTable_tableCode Ra1110.cycles } 170993
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1111.table, code := 9749693869174512473886056907247194177,
        encodes := Ra1111.tableCode_eq ▸ encodesTable_tableCode Ra1111.cycles } 170995
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1112.table, code := 9749693869176930325453230706157424705,
        encodes := Ra1112.tableCode_eq ▸ encodesTable_tableCode Ra1112.cycles } 170997
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1113.table, code := 9749693869176930325525288371062313025,
        encodes := Ra1113.tableCode_eq ▸ encodesTable_tableCode Ra1113.cycles } 170998
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1114.table, code := 9749693869176930325525288373209796673,
        encodes := Ra1114.tableCode_eq ▸ encodesTable_tableCode Ra1114.cycles } 170999
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1115.table, code := 9749774998812927080495765415124013121,
        encodes := Ra1115.tableCode_eq ▸ encodesTable_tableCode Ra1115.cycles } 171001
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1116.table, code := 9749774998812927080567823082176385089,
        encodes := Ra1116.tableCode_eq ▸ encodesTable_tableCode Ra1116.cycles } 171003
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1117.table, code := 9749774998815344932134996881086615617,
        encodes := Ra1117.tableCode_eq ▸ encodesTable_tableCode Ra1117.cycles } 171005
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1118.table, code := 9749774998815344932207054545991503937,
        encodes := Ra1118.tableCode_eq ▸ encodesTable_tableCode Ra1118.cycles } 171006
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1119.table, code := 9749774998815344932207054548138987585,
        encodes := Ra1119.tableCode_eq ▸ encodesTable_tableCode Ra1119.cycles } 171007
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1120.table, code := 9749693866691378842559329677619761217,
        encodes := Ra1120.tableCode_eq ▸ encodesTable_tableCode Ra1120.cycles } 171879
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1121.table, code := 9749774996329793449241095852548952129,
        encodes := Ra1121.tableCode_eq ▸ encodesTable_tableCode Ra1121.cycles } 171887
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1122.table, code := 9749693866691378844937230345295892545,
        encodes := Ra1122.tableCode_eq ▸ encodesTable_tableCode Ra1122.cycles } 171893
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1123.table, code := 9749693866691378845009288012348264513,
        encodes := Ra1123.tableCode_eq ▸ encodesTable_tableCode Ra1123.cycles } 171895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1124.table, code := 9749774996329793451618996520225083457,
        encodes := Ra1124.tableCode_eq ▸ encodesTable_tableCode Ra1124.cycles } 171901
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1125.table, code := 9749774996329793451691054187277455425,
        encodes := Ra1125.tableCode_eq ▸ encodesTable_tableCode Ra1125.cycles } 171903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1126.table, code := 9749693869174512476047784590946078785,
        encodes := Ra1126.tableCode_eq ▸ encodesTable_tableCode Ra1126.cycles } 172003
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1127.table, code := 9749693869176930327687016054761197633,
        encodes := Ra1127.tableCode_eq ▸ encodesTable_tableCode Ra1127.cycles } 172006
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1128.table, code := 9749693869176930327687016056908681281,
        encodes := Ra1128.tableCode_eq ▸ encodesTable_tableCode Ra1128.cycles } 172007
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1129.table, code := 9749774998812927082729550765875269697,
        encodes := Ra1129.tableCode_eq ▸ encodesTable_tableCode Ra1129.cycles } 172011
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1130.table, code := 9749774998815344934368782229690388545,
        encodes := Ra1130.tableCode_eq ▸ encodesTable_tableCode Ra1130.cycles } 172014
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1131.table, code := 9749774998815344934368782231837872193,
        encodes := Ra1131.tableCode_eq ▸ encodesTable_tableCode Ra1131.cycles } 172015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1132.table, code := 9749693869174512478425685258622210113,
        encodes := Ra1132.tableCode_eq ▸ encodesTable_tableCode Ra1132.cycles } 172017
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1133.table, code := 9749693869174512478497742925674582081,
        encodes := Ra1133.tableCode_eq ▸ encodesTable_tableCode Ra1133.cycles } 172019
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1134.table, code := 9749693869176930330064916724584812609,
        encodes := Ra1134.tableCode_eq ▸ encodesTable_tableCode Ra1134.cycles } 172021
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1135.table, code := 9749693869176930330136974389489700929,
        encodes := Ra1135.tableCode_eq ▸ encodesTable_tableCode Ra1135.cycles } 172022
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1136.table, code := 9749693869176930330136974391637184577,
        encodes := Ra1136.tableCode_eq ▸ encodesTable_tableCode Ra1136.cycles } 172023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1137.table, code := 9749774998812927085107451433551401025,
        encodes := Ra1137.tableCode_eq ▸ encodesTable_tableCode Ra1137.cycles } 172025
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1138.table, code := 9749774998812927085179509100603772993,
        encodes := Ra1138.tableCode_eq ▸ encodesTable_tableCode Ra1138.cycles } 172027
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1139.table, code := 9749774998815344936746682899514003521,
        encodes := Ra1139.tableCode_eq ▸ encodesTable_tableCode Ra1139.cycles } 172029
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1140.table, code := 9749774998815344936818740564418891841,
        encodes := Ra1140.tableCode_eq ▸ encodesTable_tableCode Ra1140.cycles } 172030
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1141.table, code := 9749774998815344936818740566566375489,
        encodes := Ra1141.tableCode_eq ▸ encodesTable_tableCode Ra1141.cycles } 172031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1142.table, code := 9658341822096448693100553084913061953,
        encodes := Ra1142.tableCode_eq ▸ encodesTable_tableCode Ra1142.cycles } 173699
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1143.table, code := 9658422951734863299782319257694769217,
        encodes := Ra1143.tableCode_eq ▸ encodesTable_tableCode Ra1143.cycles } 173706
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1144.table, code := 9658422951734863299782319259842252865,
        encodes := Ra1144.tableCode_eq ▸ encodesTable_tableCode Ra1144.cycles } 173707
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1145.table, code := 9658341822096448695550511419641565249,
        encodes := Ra1145.tableCode_eq ▸ encodesTable_tableCode Ra1145.cycles } 173715
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1146.table, code := 9661100229802547682038053385458159681,
        encodes := Ra1146.tableCode_eq ▸ encodesTable_tableCode Ra1146.cycles } 173763
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1147.table, code := 9661181359440962288719819558239866945,
        encodes := Ra1147.tableCode_eq ▸ encodesTable_tableCode Ra1147.cycles } 173770
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1148.table, code := 9661181359440962288719819560387350593,
        encodes := Ra1148.tableCode_eq ▸ encodesTable_tableCode Ra1148.cycles } 173771
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1149.table, code := 9661100229802547684488011720186662977,
        encodes := Ra1149.tableCode_eq ▸ encodesTable_tableCode Ra1149.cycles } 173779
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1150.table, code := 9661181359440962291097720228063481921,
        encodes := Ra1150.tableCode_eq ▸ encodesTable_tableCode Ra1150.cycles } 173785
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1151.table, code := 9661181359440962291169777892968370241,
        encodes := Ra1151.tableCode_eq ▸ encodesTable_tableCode Ra1151.cycles } 173786
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1152.table, code := 9661181359440962291169777895115853889,
        encodes := Ra1152.tableCode_eq ▸ encodesTable_tableCode Ra1152.cycles } 173787
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1088 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1088 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1088 + i.val) 0 ≤ Data.profiles (1088 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1088 + i.val) 0 = Data.canonicalMask (1088 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1088 + i.val) < Data.canonicalMask (1088 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1088 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models017
