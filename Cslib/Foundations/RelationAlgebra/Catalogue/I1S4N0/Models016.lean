/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1025
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1026
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1027
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1028
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1029
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1030
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1031
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1032
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1033
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1034
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1035
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1036
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1037
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1038
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1039
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1040
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1041
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1042
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1043
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1044
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1045
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1046
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1047
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1048
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1049
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1050
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1051
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1052
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1053
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1054
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1055
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1056
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1057
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1058
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1059
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1060
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1061
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1062
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1063
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1064
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1065
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1066
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1067
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1068
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1069
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1070
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1071
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1072
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1073
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1074
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1075
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1076
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1077
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1078
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1079
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1080
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1081
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1082
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1083
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1084
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1085
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1086
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1087
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1088

/-!
# Certified models 1025–1088 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models016

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1025.table, code := 4588550953644291833483269934302892097,
        encodes := Ra1025.tableCode_eq ▸ encodesTable_tableCode Ra1025.cycles } 162679
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1026.table, code := 4588632083282706440165036107084599361,
        encodes := Ra1026.tableCode_eq ▸ encodesTable_tableCode Ra1026.cycles } 162686
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1027.table, code := 4588632083282706440165036109232083009,
        encodes := Ra1027.tableCode_eq ▸ encodesTable_tableCode Ra1027.cycles } 162687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1028.table, code := 4588550956129843318610956311444328513,
        encodes := Ra1028.tableCode_eq ▸ encodesTable_tableCode Ra1028.cycles } 162806
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1029.table, code := 4588550956129843318610956313591812161,
        encodes := Ra1029.tableCode_eq ▸ encodesTable_tableCode Ra1029.cycles } 162807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1030.table, code := 4588632085768257925292722486373519425,
        encodes := Ra1030.tableCode_eq ▸ encodesTable_tableCode Ra1030.cycles } 162814
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1031.table, code := 4588632085768257925292722488521003073,
        encodes := Ra1031.tableCode_eq ▸ encodesTable_tableCode Ra1031.cycles } 162815
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1032.table, code := 4505149606106570839483255791064191041,
        encodes := Ra1032.tableCode_eq ▸ encodesTable_tableCode Ra1032.cycles } 163430
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1033.table, code := 4505149606106570839483255793211674689,
        encodes := Ra1033.tableCode_eq ▸ encodesTable_tableCode Ra1033.cycles } 163431
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1034.table, code := 4505230735744985446165021965993381953,
        encodes := Ra1034.tableCode_eq ▸ encodesTable_tableCode Ra1034.cycles } 163438
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1035.table, code := 4505230735744985446165021968140865601,
        encodes := Ra1035.tableCode_eq ▸ encodesTable_tableCode Ra1035.cycles } 163439
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1036.table, code := 4505149606106570841933214125792694337,
        encodes := Ra1036.tableCode_eq ▸ encodesTable_tableCode Ra1036.cycles } 163446
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1037.table, code := 4505149606106570841933214127940177985,
        encodes := Ra1037.tableCode_eq ▸ encodesTable_tableCode Ra1037.cycles } 163447
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1038.table, code := 4505230735744985448614980300721885249,
        encodes := Ra1038.tableCode_eq ▸ encodesTable_tableCode Ra1038.cycles } 163454
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1039.table, code := 4505230735744985448614980302869368897,
        encodes := Ra1039.tableCode_eq ▸ encodesTable_tableCode Ra1039.cycles } 163455
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1040.table, code := 4502391200883605486412111073669025857,
        encodes := Ra1040.tableCode_eq ▸ encodesTable_tableCode Ra1040.cycles } 163505
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1041.table, code := 4502472330522020093093877246450733121,
        encodes := Ra1041.tableCode_eq ▸ encodesTable_tableCode Ra1041.cycles } 163512
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1042.table, code := 4502472330522020093093877248598216769,
        encodes := Ra1042.tableCode_eq ▸ encodesTable_tableCode Ra1042.cycles } 163513
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1043.table, code := 4505149608592122324610942170353111105,
        encodes := Ra1043.tableCode_eq ▸ encodesTable_tableCode Ra1043.cycles } 163558
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1044.table, code := 4505149608592122324610942172500594753,
        encodes := Ra1044.tableCode_eq ▸ encodesTable_tableCode Ra1044.cycles } 163559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1045.table, code := 4505230738230536931292708345282302017,
        encodes := Ra1045.tableCode_eq ▸ encodesTable_tableCode Ra1045.cycles } 163566
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1046.table, code := 4505230738230536931292708347429785665,
        encodes := Ra1046.tableCode_eq ▸ encodesTable_tableCode Ra1046.cycles } 163567
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1047.table, code := 4505149608592122327060900505081614401,
        encodes := Ra1047.tableCode_eq ▸ encodesTable_tableCode Ra1047.cycles } 163574
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1048.table, code := 4505149608592122327060900507229098049,
        encodes := Ra1048.tableCode_eq ▸ encodesTable_tableCode Ra1048.cycles } 163575
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1049.table, code := 4505230738230536933742666680010805313,
        encodes := Ra1049.tableCode_eq ▸ encodesTable_tableCode Ra1049.cycles } 163582
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1050.table, code := 4505230738230536933742666682158288961,
        encodes := Ra1050.tableCode_eq ▸ encodesTable_tableCode Ra1050.cycles } 163583
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1051.table, code := 4585792545938192849157455650037698625,
        encodes := Ra1051.tableCode_eq ▸ encodesTable_tableCode Ra1051.cycles } 163638
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1052.table, code := 4585792545938192849157455652185182273,
        encodes := Ra1052.tableCode_eq ▸ encodesTable_tableCode Ra1052.cycles } 163639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1053.table, code := 4585873675576607455839221824966889537,
        encodes := Ra1053.tableCode_eq ▸ encodesTable_tableCode Ra1053.cycles } 163646
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1054.table, code := 4585873675576607455839221827114373185,
        encodes := Ra1054.tableCode_eq ▸ encodesTable_tableCode Ra1054.cycles } 163647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1055.table, code := 4588550953644291835644997615854293057,
        encodes := Ra1055.tableCode_eq ▸ encodesTable_tableCode Ra1055.cycles } 163686
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1056.table, code := 4588550953644291835644997618001776705,
        encodes := Ra1056.tableCode_eq ▸ encodesTable_tableCode Ra1056.cycles } 163687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1057.table, code := 4588632083282706442326763790783483969,
        encodes := Ra1057.tableCode_eq ▸ encodesTable_tableCode Ra1057.cycles } 163694
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1058.table, code := 4588632083282706442326763792930967617,
        encodes := Ra1058.tableCode_eq ▸ encodesTable_tableCode Ra1058.cycles } 163695
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1059.table, code := 4588550953644291838094955950582796353,
        encodes := Ra1059.tableCode_eq ▸ encodesTable_tableCode Ra1059.cycles } 163702
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1060.table, code := 4588550953644291838094955952730280001,
        encodes := Ra1060.tableCode_eq ▸ encodesTable_tableCode Ra1060.cycles } 163703
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1061.table, code := 4588632083282706444776722125511987265,
        encodes := Ra1061.tableCode_eq ▸ encodesTable_tableCode Ra1061.cycles } 163710
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1062.table, code := 4588632083282706444776722127659470913,
        encodes := Ra1062.tableCode_eq ▸ encodesTable_tableCode Ra1062.cycles } 163711
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1063.table, code := 4585792548423744331835183694598115393,
        encodes := Ra1063.tableCode_eq ▸ encodesTable_tableCode Ra1063.cycles } 163750
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1064.table, code := 4585792548423744331835183696745599041,
        encodes := Ra1064.tableCode_eq ▸ encodesTable_tableCode Ra1064.cycles } 163751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1065.table, code := 4585873678062158938516949869527306305,
        encodes := Ra1065.tableCode_eq ▸ encodesTable_tableCode Ra1065.cycles } 163758
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1066.table, code := 4585873678062158938516949871674789953,
        encodes := Ra1066.tableCode_eq ▸ encodesTable_tableCode Ra1066.cycles } 163759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1067.table, code := 4585792548423744334285142029326618689,
        encodes := Ra1067.tableCode_eq ▸ encodesTable_tableCode Ra1067.cycles } 163766
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1068.table, code := 4585792548423744334285142031474102337,
        encodes := Ra1068.tableCode_eq ▸ encodesTable_tableCode Ra1068.cycles } 163767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1069.table, code := 4585873678062158940966908204255809601,
        encodes := Ra1069.tableCode_eq ▸ encodesTable_tableCode Ra1069.cycles } 163774
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1070.table, code := 4585873678062158940966908206403293249,
        encodes := Ra1070.tableCode_eq ▸ encodesTable_tableCode Ra1070.cycles } 163775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1071.table, code := 4588550956129843320772683995143213121,
        encodes := Ra1071.tableCode_eq ▸ encodesTable_tableCode Ra1071.cycles } 163814
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1072.table, code := 4588550956129843320772683997290696769,
        encodes := Ra1072.tableCode_eq ▸ encodesTable_tableCode Ra1072.cycles } 163815
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1073.table, code := 4588632085768257927454450170072404033,
        encodes := Ra1073.tableCode_eq ▸ encodesTable_tableCode Ra1073.cycles } 163822
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1074.table, code := 4588632085768257927454450172219887681,
        encodes := Ra1074.tableCode_eq ▸ encodesTable_tableCode Ra1074.cycles } 163823
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1075.table, code := 4588550956129843323222642329871716417,
        encodes := Ra1075.tableCode_eq ▸ encodesTable_tableCode Ra1075.cycles } 163830
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1076.table, code := 4588550956129843323222642332019200065,
        encodes := Ra1076.tableCode_eq ▸ encodesTable_tableCode Ra1076.cycles } 163831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1077.table, code := 4588632085768257929904408504800907329,
        encodes := Ra1077.tableCode_eq ▸ encodesTable_tableCode Ra1077.cycles } 163838
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1078.table, code := 4588632085768257929904408506948390977,
        encodes := Ra1078.tableCode_eq ▸ encodesTable_tableCode Ra1078.cycles } 163839
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1079.table, code := 9744501572315972905372241800510836801,
        encodes := Ra1079.tableCode_eq ▸ encodesTable_tableCode Ra1079.cycles } 166897
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1080.table, code := 9744501572315972905444299467563208769,
        encodes := Ra1080.tableCode_eq ▸ encodesTable_tableCode Ra1080.cycles } 166899
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1081.table, code := 9744501572318390757083530933525811265,
        encodes := Ra1081.tableCode_eq ▸ encodesTable_tableCode Ra1081.cycles } 166903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1082.table, code := 9744582701956805363765297106307518529,
        encodes := Ra1082.tableCode_eq ▸ encodesTable_tableCode Ra1082.cycles } 166910
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1083.table, code := 9744582701956805363765297108455002177,
        encodes := Ra1083.tableCode_eq ▸ encodesTable_tableCode Ra1083.cycles } 166911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1084.table, code := 9744501569832839274117572237935775809,
        encodes := Ra1084.tableCode_eq ▸ encodesTable_tableCode Ra1084.cycles } 167783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1085.table, code := 9744582699471253880799338412864966721,
        encodes := Ra1085.tableCode_eq ▸ encodesTable_tableCode Ra1085.cycles } 167791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1086.table, code := 9744501569832839276495472905611907137,
        encodes := Ra1086.tableCode_eq ▸ encodesTable_tableCode Ra1086.cycles } 167797
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1087.table, code := 9744501569832839276567530572664279105,
        encodes := Ra1087.tableCode_eq ▸ encodesTable_tableCode Ra1087.cycles } 167799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1088.table, code := 9744582699471253883177239080541098049,
        encodes := Ra1088.tableCode_eq ▸ encodesTable_tableCode Ra1088.cycles } 167805
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1024 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1024 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1024 + i.val) 0 ≤ Data.profiles (1024 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1024 + i.val) 0 = Data.canonicalMask (1024 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1024 + i.val) < Data.canonicalMask (1024 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1024 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models016
