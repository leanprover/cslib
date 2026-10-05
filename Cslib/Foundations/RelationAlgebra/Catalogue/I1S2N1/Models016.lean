/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1025
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1026
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1027
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1028
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1029
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1030
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1031
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1032
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1033
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1034
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1035
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1036
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1037
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1038
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1039
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1040
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1041
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1042
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1043
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1044
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1045
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1046
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1047
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1048
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1049
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1050
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1051
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1052
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1053
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1054
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1055
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1056
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1057
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1058
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1059
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1060
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1061
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1062
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1063
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1064
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1065
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1066
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1067
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1068
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1069
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1070
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1071
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1072
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1073
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1074
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1075
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1076
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1077
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1078
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1079
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1080
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1081
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1082
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1083
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1084
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1085
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1086
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1087
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1088

/-!
# Certified models 1025–1088 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models016

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1025.table, code := 41032715301129462916060268148883198017,
        encodes := Ra1025.tableCode_eq ▸ encodesTable_tableCode Ra1025.cycles } 55740
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1026.table, code := 41032715301129462916060268151030681665,
        encodes := Ra1026.tableCode_eq ▸ encodesTable_tableCode Ra1026.cycles } 55741
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1027.table, code := 41032715301129462916132325815935569985,
        encodes := Ra1027.tableCode_eq ▸ encodesTable_tableCode Ra1027.cycles } 55742
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1028.table, code := 41032715301129462916132325818083053633,
        encodes := Ra1028.tableCode_eq ▸ encodesTable_tableCode Ra1028.cycles } 55743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1029.table, code := 41033364417464942283778180850561323073,
        encodes := Ra1029.tableCode_eq ▸ encodesTable_tableCode Ra1029.cycles } 55804
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1030.table, code := 41033364417464942283778180852708806721,
        encodes := Ra1030.tableCode_eq ▸ encodesTable_tableCode Ra1030.cycles } 55805
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1031.table, code := 41033364417464942283850238517613695041,
        encodes := Ra1031.tableCode_eq ▸ encodesTable_tableCode Ra1031.cycles } 55806
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1032.table, code := 41033364417464942283850238519761178689,
        encodes := Ra1032.tableCode_eq ▸ encodesTable_tableCode Ra1032.cycles } 55807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1033.table, code := 40950287667718713637325940609641615425,
        encodes := Ra1033.tableCode_eq ▸ encodesTable_tableCode Ra1033.cycles } 56052
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1034.table, code := 40950287667718713637325940611789099073,
        encodes := Ra1034.tableCode_eq ▸ encodesTable_tableCode Ra1034.cycles } 56053
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1035.table, code := 40950287667718713637397998276693987393,
        encodes := Ra1035.tableCode_eq ▸ encodesTable_tableCode Ra1035.cycles } 56054
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1036.table, code := 40950287667718713637397998278841471041,
        encodes := Ra1036.tableCode_eq ▸ encodesTable_tableCode Ra1036.cycles } 56055
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1037.table, code := 40950287667718713639775898944370118721,
        encodes := Ra1037.tableCode_eq ▸ encodesTable_tableCode Ra1037.cycles } 56060
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1038.table, code := 40950287667718713639775898946517602369,
        encodes := Ra1038.tableCode_eq ▸ encodesTable_tableCode Ra1038.cycles } 56061
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1039.table, code := 40950287667718713639847956611422490689,
        encodes := Ra1039.tableCode_eq ▸ encodesTable_tableCode Ra1039.cycles } 56062
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1040.table, code := 40950287667718713639847956613569974337,
        encodes := Ra1040.tableCode_eq ▸ encodesTable_tableCode Ra1040.cycles } 56063
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1041.table, code := 38374583904846229221720617573922639937,
        encodes := Ra1041.tableCode_eq ▸ encodesTable_tableCode Ra1041.cycles } 56180
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1042.table, code := 38374583904846229221720617576070123585,
        encodes := Ra1042.tableCode_eq ▸ encodesTable_tableCode Ra1042.cycles } 56181
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1043.table, code := 38374583904846229221792675240975011905,
        encodes := Ra1043.tableCode_eq ▸ encodesTable_tableCode Ra1043.cycles } 56182
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1044.table, code := 38374583904846229221792675243122495553,
        encodes := Ra1044.tableCode_eq ▸ encodesTable_tableCode Ra1044.cycles } 56183
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1045.table, code := 38374583904846229224170575908651143233,
        encodes := Ra1045.tableCode_eq ▸ encodesTable_tableCode Ra1045.cycles } 56188
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1046.table, code := 38374583904846229224170575910798626881,
        encodes := Ra1046.tableCode_eq ▸ encodesTable_tableCode Ra1046.cycles } 56189
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1047.table, code := 38374583904846229224242633575703515201,
        encodes := Ra1047.tableCode_eq ▸ encodesTable_tableCode Ra1047.cycles } 56190
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1048.table, code := 38374583904846229224242633577850998849,
        encodes := Ra1048.tableCode_eq ▸ encodesTable_tableCode Ra1048.cycles } 56191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1049.table, code := 41032715301129462918221995832582082625,
        encodes := Ra1049.tableCode_eq ▸ encodesTable_tableCode Ra1049.cycles } 56244
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1050.table, code := 41032715301129462918221995834729566273,
        encodes := Ra1050.tableCode_eq ▸ encodesTable_tableCode Ra1050.cycles } 56245
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1051.table, code := 41032715301129462918294053499634454593,
        encodes := Ra1051.tableCode_eq ▸ encodesTable_tableCode Ra1051.cycles } 56246
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1052.table, code := 41032715301129462918294053501781938241,
        encodes := Ra1052.tableCode_eq ▸ encodesTable_tableCode Ra1052.cycles } 56247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1053.table, code := 41032715301129462920671954167310585921,
        encodes := Ra1053.tableCode_eq ▸ encodesTable_tableCode Ra1053.cycles } 56252
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1054.table, code := 41032715301129462920671954169458069569,
        encodes := Ra1054.tableCode_eq ▸ encodesTable_tableCode Ra1054.cycles } 56253
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1055.table, code := 41032715301129462920744011834362957889,
        encodes := Ra1055.tableCode_eq ▸ encodesTable_tableCode Ra1055.cycles } 56254
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1056.table, code := 41032715301129462920744011836510441537,
        encodes := Ra1056.tableCode_eq ▸ encodesTable_tableCode Ra1056.cycles } 56255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1057.table, code := 41033283287824109827618910895515897921,
        encodes := Ra1057.tableCode_eq ▸ encodesTable_tableCode Ra1057.cycles } 56305
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1058.table, code := 41033283287824109827690968562568269889,
        encodes := Ra1058.tableCode_eq ▸ encodesTable_tableCode Ra1058.cycles } 56307
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1059.table, code := 41033364417464942285939908534260207681,
        encodes := Ra1059.tableCode_eq ▸ encodesTable_tableCode Ra1059.cycles } 56308
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1060.table, code := 41033364417464942285939908536407691329,
        encodes := Ra1060.tableCode_eq ▸ encodesTable_tableCode Ra1060.cycles } 56309
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1061.table, code := 41033364417464942286011966201312579649,
        encodes := Ra1061.tableCode_eq ▸ encodesTable_tableCode Ra1061.cycles } 56310
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1062.table, code := 41033364417464942286011966203460063297,
        encodes := Ra1062.tableCode_eq ▸ encodesTable_tableCode Ra1062.cycles } 56311
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1063.table, code := 41033283287824109830068869230244401217,
        encodes := Ra1063.tableCode_eq ▸ encodesTable_tableCode Ra1063.cycles } 56313
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1064.table, code := 41033283287824109830140926897296773185,
        encodes := Ra1064.tableCode_eq ▸ encodesTable_tableCode Ra1064.cycles } 56315
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1065.table, code := 41033364417464942288389866868988710977,
        encodes := Ra1065.tableCode_eq ▸ encodesTable_tableCode Ra1065.cycles } 56316
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1066.table, code := 41033364417464942288389866871136194625,
        encodes := Ra1066.tableCode_eq ▸ encodesTable_tableCode Ra1066.cycles } 56317
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1067.table, code := 41033364417464942288461924536041082945,
        encodes := Ra1067.tableCode_eq ▸ encodesTable_tableCode Ra1067.cycles } 56318
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1068.table, code := 41033364417464942288461924538188566593,
        encodes := Ra1068.tableCode_eq ▸ encodesTable_tableCode Ra1068.cycles } 56319
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1069.table, code := 40952883816297892671767995135746641985,
        encodes := Ra1069.tableCode_eq ▸ encodesTable_tableCode Ra1069.cycles } 56534
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1070.table, code := 40952883816297892671767995137894125633,
        encodes := Ra1070.tableCode_eq ▸ encodesTable_tableCode Ra1070.cycles } 56535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1071.table, code := 40952883816297892674217953470475145281,
        encodes := Ra1071.tableCode_eq ▸ encodesTable_tableCode Ra1071.cycles } 56542
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1072.table, code := 40952883816297892674217953472622628929,
        encodes := Ra1072.tableCode_eq ▸ encodesTable_tableCode Ra1072.cycles } 56543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1073.table, code := 40955317705377793037735532823425847361,
        encodes := Ra1073.tableCode_eq ▸ encodesTable_tableCode Ra1073.cycles } 56557
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1074.table, code := 40955317705377793037807590490478219329,
        encodes := Ra1074.tableCode_eq ▸ encodesTable_tableCode Ra1074.cycles } 56559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1075.table, code := 40955479964731995862864009191791792193,
        encodes := Ra1075.tableCode_eq ▸ encodesTable_tableCode Ra1075.cycles } 56564
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1076.table, code := 40955479964731995862864009193939275841,
        encodes := Ra1076.tableCode_eq ▸ encodesTable_tableCode Ra1076.cycles } 56565
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1077.table, code := 40955479964731995862936066858844164161,
        encodes := Ra1077.tableCode_eq ▸ encodesTable_tableCode Ra1077.cycles } 56566
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1078.table, code := 40955479964731995862936066860991647809,
        encodes := Ra1078.tableCode_eq ▸ encodesTable_tableCode Ra1078.cycles } 56567
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1079.table, code := 40955479964731995865313967528667779137,
        encodes := Ra1079.tableCode_eq ▸ encodesTable_tableCode Ra1079.cycles } 56573
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1080.table, code := 40955479964731995865386025193572667457,
        encodes := Ra1080.tableCode_eq ▸ encodesTable_tableCode Ra1080.cycles } 56574
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1081.table, code := 40955479964731995865386025195720151105,
        encodes := Ra1081.tableCode_eq ▸ encodesTable_tableCode Ra1081.cycles } 56575
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1082.table, code := 38376936664430372972641140421570072641,
        encodes := Ra1082.tableCode_eq ▸ encodesTable_tableCode Ra1082.cycles } 56648
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1083.table, code := 38376936664430372972641140423717556289,
        encodes := Ra1083.tableCode_eq ▸ encodesTable_tableCode Ra1083.cycles } 56649
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1084.table, code := 38377180053425408256162672100027666497,
        encodes := Ra1084.tableCode_eq ▸ encodesTable_tableCode Ra1084.cycles } 56662
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1085.table, code := 38377180053425408256162672102175150145,
        encodes := Ra1085.tableCode_eq ▸ encodesTable_tableCode Ra1085.cycles } 56663
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1086.table, code := 38377180053425408258612630434756169793,
        encodes := Ra1086.tableCode_eq ▸ encodesTable_tableCode Ra1086.cycles } 56670
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1087.table, code := 38377180053425408258612630436903653441,
        encodes := Ra1087.tableCode_eq ▸ encodesTable_tableCode Ra1087.cycles } 56671
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1088.table, code := 38379613942505308622202267452611760193,
        encodes := Ra1088.tableCode_eq ▸ encodesTable_tableCode Ra1088.cycles } 56686
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (1024 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1024 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
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

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models016
