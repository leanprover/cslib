/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1089
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1090
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1091
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1092
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1093
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1094
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1095
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1096
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1097
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1098
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1099
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1100
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1101
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1102
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1103
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1104
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1105
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1106
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1107
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1108
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1109
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1110
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1111
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1112
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1113
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1114
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1115
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1116
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1117
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1118
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1119
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1120
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1121
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1122
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1123
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1124
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1125
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1126
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1127
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1128
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1129
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1130
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1131
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1132
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1133
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1134
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1135
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1136
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1137
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1138
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1139
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1140
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1141
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1142
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1143
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1144
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1145
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1146
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1147
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1148
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1149
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1150
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1151
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1152

/-!
# Certified models 1089–1152 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models017

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1089.table, code := 38379613942505308622202267454759243841,
        encodes := Ra1089.tableCode_eq ▸ encodesTable_tableCode Ra1089.cycles } 56687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1090.table, code := 38379695072218678989009746182233395265,
        encodes := Ra1090.tableCode_eq ▸ encodesTable_tableCode Ra1090.cycles } 56690
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1091.table, code := 38379695072218678989009746184380878913,
        encodes := Ra1091.tableCode_eq ▸ encodesTable_tableCode Ra1091.cycles } 56691
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1092.table, code := 38379776201859511447258686156072816705,
        encodes := Ra1092.tableCode_eq ▸ encodesTable_tableCode Ra1092.cycles } 56692
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1093.table, code := 38379776201859511447258686158220300353,
        encodes := Ra1093.tableCode_eq ▸ encodesTable_tableCode Ra1093.cycles } 56693
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1094.table, code := 38379776201859511447330743823125188673,
        encodes := Ra1094.tableCode_eq ▸ encodesTable_tableCode Ra1094.cycles } 56694
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1095.table, code := 38379776201859511447330743825272672321,
        encodes := Ra1095.tableCode_eq ▸ encodesTable_tableCode Ra1095.cycles } 56695
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1096.table, code := 38379695072218678991459704516961898561,
        encodes := Ra1096.tableCode_eq ▸ encodesTable_tableCode Ra1096.cycles } 56698
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1097.table, code := 38379695072218678991459704519109382209,
        encodes := Ra1097.tableCode_eq ▸ encodesTable_tableCode Ra1097.cycles } 56699
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1098.table, code := 38379776201859511449708644490801320001,
        encodes := Ra1098.tableCode_eq ▸ encodesTable_tableCode Ra1098.cycles } 56700
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1099.table, code := 38379776201859511449708644492948803649,
        encodes := Ra1099.tableCode_eq ▸ encodesTable_tableCode Ra1099.cycles } 56701
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1100.table, code := 38379776201859511449780702157853691969,
        encodes := Ra1100.tableCode_eq ▸ encodesTable_tableCode Ra1100.cycles } 56702
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1101.table, code := 38379776201859511449780702160001175617,
        encodes := Ra1101.tableCode_eq ▸ encodesTable_tableCode Ra1101.cycles } 56703
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1102.table, code := 41035311449708641952664050358687109185,
        encodes := Ra1102.tableCode_eq ▸ encodesTable_tableCode Ra1102.cycles } 56726
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1103.table, code := 41035311449708641952664050360834592833,
        encodes := Ra1103.tableCode_eq ▸ encodesTable_tableCode Ra1103.cycles } 56727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1104.table, code := 41035311449708641955041951028510724161,
        encodes := Ra1104.tableCode_eq ▸ encodesTable_tableCode Ra1104.cycles } 56733
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1105.table, code := 41035311449708641955114008693415612481,
        encodes := Ra1105.tableCode_eq ▸ encodesTable_tableCode Ra1105.cycles } 56734
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1106.table, code := 41035311449708641955114008695563096129,
        encodes := Ra1106.tableCode_eq ▸ encodesTable_tableCode Ra1106.cycles } 56735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1107.table, code := 41037907598142745143760064414732259393,
        encodes := Ra1107.tableCode_eq ▸ encodesTable_tableCode Ra1107.cycles } 56756
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1108.table, code := 41037907598142745143760064416879743041,
        encodes := Ra1108.tableCode_eq ▸ encodesTable_tableCode Ra1108.cycles } 56757
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1109.table, code := 41037907598142745143832122081784631361,
        encodes := Ra1109.tableCode_eq ▸ encodesTable_tableCode Ra1109.cycles } 56758
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1110.table, code := 41037907598142745143832122083932115009,
        encodes := Ra1110.tableCode_eq ▸ encodesTable_tableCode Ra1110.cycles } 56759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1111.table, code := 41037907598142745146210022751608246337,
        encodes := Ra1111.tableCode_eq ▸ encodesTable_tableCode Ra1111.cycles } 56765
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1112.table, code := 41037907598142745146282080416513134657,
        encodes := Ra1112.tableCode_eq ▸ encodesTable_tableCode Ra1112.cycles } 56766
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1113.table, code := 41037907598142745146282080418660618305,
        encodes := Ra1113.tableCode_eq ▸ encodesTable_tableCode Ra1113.cycles } 56767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1114.table, code := 41035798306689918495253486689851805761,
        encodes := Ra1114.tableCode_eq ▸ encodesTable_tableCode Ra1114.cycles } 56782
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1115.table, code := 41035798306689918495253486691999289409,
        encodes := Ra1115.tableCode_eq ▸ encodesTable_tableCode Ra1115.cycles } 56783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1116.table, code := 41035960566044121320381963060365234241,
        encodes := Ra1116.tableCode_eq ▸ encodesTable_tableCode Ra1116.cycles } 56790
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1117.table, code := 41035960566044121320381963062512717889,
        encodes := Ra1117.tableCode_eq ▸ encodesTable_tableCode Ra1117.cycles } 56791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1118.table, code := 41035960566044121322759863728041365569,
        encodes := Ra1118.tableCode_eq ▸ encodesTable_tableCode Ra1118.cycles } 56796
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1119.table, code := 41035960566044121322759863730188849217,
        encodes := Ra1119.tableCode_eq ▸ encodesTable_tableCode Ra1119.cycles } 56797
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1120.table, code := 41035960566044121322831921395093737537,
        encodes := Ra1120.tableCode_eq ▸ encodesTable_tableCode Ra1120.cycles } 56798
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1121.table, code := 41035960566044121322831921397241221185,
        encodes := Ra1121.tableCode_eq ▸ encodesTable_tableCode Ra1121.cycles } 56799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1122.table, code := 41038394455124021686349500745896955969,
        encodes := Ra1122.tableCode_eq ▸ encodesTable_tableCode Ra1122.cycles } 56812
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1123.table, code := 41038394455124021686349500748044439617,
        encodes := Ra1123.tableCode_eq ▸ encodesTable_tableCode Ra1123.cycles } 56813
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1124.table, code := 41038394455124021686421558412949327937,
        encodes := Ra1124.tableCode_eq ▸ encodesTable_tableCode Ra1124.cycles } 56814
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1125.table, code := 41038394455124021686421558415096811585,
        encodes := Ra1125.tableCode_eq ▸ encodesTable_tableCode Ra1125.cycles } 56815
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1126.table, code := 41038475584837392053156979477666074689,
        encodes := Ra1126.tableCode_eq ▸ encodesTable_tableCode Ra1126.cycles } 56817
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1127.table, code := 41038475584837392053229037142570963009,
        encodes := Ra1127.tableCode_eq ▸ encodesTable_tableCode Ra1127.cycles } 56818
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1128.table, code := 41038475584837392053229037144718446657,
        encodes := Ra1128.tableCode_eq ▸ encodesTable_tableCode Ra1128.cycles } 56819
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1129.table, code := 41038556714478224511477977116410384449,
        encodes := Ra1129.tableCode_eq ▸ encodesTable_tableCode Ra1129.cycles } 56820
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1130.table, code := 41038556714478224511477977118557868097,
        encodes := Ra1130.tableCode_eq ▸ encodesTable_tableCode Ra1130.cycles } 56821
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1131.table, code := 41038556714478224511550034783462756417,
        encodes := Ra1131.tableCode_eq ▸ encodesTable_tableCode Ra1131.cycles } 56822
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1132.table, code := 41038556714478224511550034785610240065,
        encodes := Ra1132.tableCode_eq ▸ encodesTable_tableCode Ra1132.cycles } 56823
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1133.table, code := 41038475584837392055606937812394577985,
        encodes := Ra1133.tableCode_eq ▸ encodesTable_tableCode Ra1133.cycles } 56825
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1134.table, code := 41038475584837392055678995477299466305,
        encodes := Ra1134.tableCode_eq ▸ encodesTable_tableCode Ra1134.cycles } 56826
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1135.table, code := 41038475584837392055678995479446949953,
        encodes := Ra1135.tableCode_eq ▸ encodesTable_tableCode Ra1135.cycles } 56827
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1136.table, code := 41038556714478224513927935451138887745,
        encodes := Ra1136.tableCode_eq ▸ encodesTable_tableCode Ra1136.cycles } 56828
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1137.table, code := 41038556714478224513927935453286371393,
        encodes := Ra1137.tableCode_eq ▸ encodesTable_tableCode Ra1137.cycles } 56829
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1138.table, code := 41038556714478224513999993118191259713,
        encodes := Ra1138.tableCode_eq ▸ encodesTable_tableCode Ra1138.cycles } 56830
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1139.table, code := 41038556714478224513999993120338743361,
        encodes := Ra1139.tableCode_eq ▸ encodesTable_tableCode Ra1139.cycles } 56831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1140.table, code := 40952883816297892676379681156321513537,
        encodes := Ra1140.tableCode_eq ▸ encodesTable_tableCode Ra1140.cycles } 57047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1141.table, code := 40952883816297892678829639491050016833,
        encodes := Ra1141.tableCode_eq ▸ encodesTable_tableCode Ra1141.cycles } 57055
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1142.table, code := 40955479964731995867475695212366663745,
        encodes := Ra1142.tableCode_eq ▸ encodesTable_tableCode Ra1142.cycles } 57077
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1143.table, code := 40955479964731995867547752879419035713,
        encodes := Ra1143.tableCode_eq ▸ encodesTable_tableCode Ra1143.cycles } 57079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1144.table, code := 40955479964731995869997711214147539009,
        encodes := Ra1144.tableCode_eq ▸ encodesTable_tableCode Ra1144.cycles } 57087
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1145.table, code := 38376936664430372977252826439997460545,
        encodes := Ra1145.tableCode_eq ▸ encodesTable_tableCode Ra1145.cycles } 57160
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1146.table, code := 38376936664430372977252826442144944193,
        encodes := Ra1146.tableCode_eq ▸ encodesTable_tableCode Ra1146.cycles } 57161
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1147.table, code := 38377180053425408260774358118455054401,
        encodes := Ra1147.tableCode_eq ▸ encodesTable_tableCode Ra1147.cycles } 57174
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1148.table, code := 38377180053425408260774358120602538049,
        encodes := Ra1148.tableCode_eq ▸ encodesTable_tableCode Ra1148.cycles } 57175
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1149.table, code := 38377180053425408263224316453183557697,
        encodes := Ra1149.tableCode_eq ▸ encodesTable_tableCode Ra1149.cycles } 57182
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1150.table, code := 38377180053425408263224316455331041345,
        encodes := Ra1150.tableCode_eq ▸ encodesTable_tableCode Ra1150.cycles } 57183
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1151.table, code := 38379613942505308626813953471039148097,
        encodes := Ra1151.tableCode_eq ▸ encodesTable_tableCode Ra1151.cycles } 57198
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1152.table, code := 38379613942505308626813953473186631745,
        encodes := Ra1152.tableCode_eq ▸ encodesTable_tableCode Ra1152.cycles } 57199
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (1088 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1088 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
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

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models017
