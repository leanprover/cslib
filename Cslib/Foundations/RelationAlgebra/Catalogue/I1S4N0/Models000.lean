/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0001
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0002
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0003
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0004
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0005
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0006
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0007
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0008
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0009
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0010
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0011
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0012
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0013
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0014
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0015
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0016
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0017
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0018
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0019
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0020
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0021
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0022
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0023
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0024
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0025
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0026
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0027
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0028
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0029
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0030
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0031
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0032
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0033
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0034
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0035
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0036
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0037
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0038
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0039
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0040
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0041
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0042
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0043
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0044
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0045
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0046
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0047
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0048
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0049
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0050
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0051
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0052
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0053
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0054
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0055
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0056
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0057
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0058
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0059
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0060
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0061
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0062
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0063
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0064

/-!
# Certified models 1–64 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models000

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0001.table, code := 4074513065921488898219576396966268993,
        encodes := Ra0001.tableCode_eq ▸ encodesTable_tableCode Ra0001.cycles } 1009
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0002.table, code := 4074594195562321356612631704910434369,
        encodes := Ra0002.tableCode_eq ▸ encodesTable_tableCode Ra0002.cycles } 1023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0003.table, code := 4074594195562321361224317723337822273,
        encodes := Ra0003.tableCode_eq ▸ encodesTable_tableCode Ra0003.cycles } 2047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0004.table, code := 4074594195717064018320628865804013633,
        encodes := Ra0004.tableCode_eq ▸ encodesTable_tableCode Ra0004.cycles } 3071
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0005.table, code := 4074594195717064022932314884231401537,
        encodes := Ra0005.tableCode_eq ▸ encodesTable_tableCode Ra0005.cycles } 4095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0006.table, code := 1417841923983765025233394805212713025,
        encodes := Ra0006.tableCode_eq ▸ encodesTable_tableCode Ra0006.cycles } 6416
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0007.table, code := 1417841926469316510361081186649116737,
        encodes := Ra0007.tableCode_eq ▸ encodesTable_tableCode Ra0007.cycles } 6545
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0008.table, code := 4076946955146465109622824569204379713,
        encodes := Ra0008.tableCode_eq ▸ encodesTable_tableCode Ra0008.cycles } 7057
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0009.table, code := 4077028084787297567943822210096173121,
        encodes := Ra0009.tableCode_eq ▸ encodesTable_tableCode Ra0009.cycles } 7069
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0010.table, code := 4079705362934771128441388664596205633,
        encodes := Ra0010.tableCode_eq ▸ encodesTable_tableCode Ra0010.cycles } 7155
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0011.table, code := 4079786492575603586762386305487999041,
        encodes := Ra0011.tableCode_eq ▸ encodesTable_tableCode Ra0011.cycles } 7167
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0012.table, code := 1417841923983765029845080823640100929,
        encodes := Ra0012.tableCode_eq ▸ encodesTable_tableCode Ra0012.cycles } 7440
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0013.table, code := 1417841926469316514972767205076504641,
        encodes := Ra0013.tableCode_eq ▸ encodesTable_tableCode Ra0013.cycles } 7569
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0014.table, code := 4076946955146465114234510587631767617,
        encodes := Ra0014.tableCode_eq ▸ encodesTable_tableCode Ra0014.cycles } 8081
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0015.table, code := 4077028084787297572555508228523561025,
        encodes := Ra0015.tableCode_eq ▸ encodesTable_tableCode Ra0015.cycles } 8093
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0016.table, code := 4079705362934771133053074683023593537,
        encodes := Ra0016.tableCode_eq ▸ encodesTable_tableCode Ra0016.cycles } 8179
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0017.table, code := 4079786492575603591374072323915386945,
        encodes := Ra0017.tableCode_eq ▸ encodesTable_tableCode Ra0017.cycles } 8191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0018.table, code := 4074594200823566823335089071011926081,
        encodes := Ra0018.tableCode_eq ▸ encodesTable_tableCode Ra0018.cycles } 10239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0019.table, code := 4074594200978309480431400213478117441,
        encodes := Ra0019.tableCode_eq ▸ encodesTable_tableCode Ra0019.cycles } 11263
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0020.table, code := 4074594200978309485043086231905505345,
        encodes := Ra0020.tableCode_eq ▸ encodesTable_tableCode Ra0020.cycles } 12287
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0021.table, code := 1417841929172474853067274452111462465,
        encodes := Ra0021.tableCode_eq ▸ encodesTable_tableCode Ra0021.cycles } 12578
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0022.table, code := 1417841931658026338194960833547866177,
        encodes := Ra0022.tableCode_eq ▸ encodesTable_tableCode Ra0022.cycles } 12707
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0023.table, code := 4079786495196554902037474112979603521,
        encodes := Ra0023.tableCode_eq ▸ encodesTable_tableCode Ra0023.cycles } 13183
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0024.table, code := 4079786497682106387165160492268523585,
        encodes := Ra0024.tableCode_eq ▸ encodesTable_tableCode Ra0024.cycles } 13311
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0025.table, code := 1417841929172474857678960470538850369,
        encodes := Ra0025.tableCode_eq ▸ encodesTable_tableCode Ra0025.cycles } 13602
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0026.table, code := 1417841931658026342806646851975254081,
        encodes := Ra0026.tableCode_eq ▸ encodesTable_tableCode Ra0026.cycles } 13731
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0027.table, code := 4079786495196554906649160131406991425,
        encodes := Ra0027.tableCode_eq ▸ encodesTable_tableCode Ra0027.cycles } 14207
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0028.table, code := 4079786497682106391776846510695911489,
        encodes := Ra0028.tableCode_eq ▸ encodesTable_tableCode Ra0028.cycles } 14335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0029.table, code := 1417841929327217517225229947733545025,
        encodes := Ra0029.tableCode_eq ▸ encodesTable_tableCode Ra0029.cycles } 14642
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0030.table, code := 1417841931812769002352916329169948737,
        encodes := Ra0030.tableCode_eq ▸ encodesTable_tableCode Ra0030.cycles } 14771
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0031.table, code := 4079786495351297563745471273873182785,
        encodes := Ra0031.tableCode_eq ▸ encodesTable_tableCode Ra0031.cycles } 15231
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0032.table, code := 4079786497836849048873157653162102849,
        encodes := Ra0032.tableCode_eq ▸ encodesTable_tableCode Ra0032.cycles } 15359
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0033.table, code := 1417841929327217521836915966160932929,
        encodes := Ra0033.tableCode_eq ▸ encodesTable_tableCode Ra0033.cycles } 15666
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0034.table, code := 1417841931812769006964602347597336641,
        encodes := Ra0034.tableCode_eq ▸ encodesTable_tableCode Ra0034.cycles } 15795
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0035.table, code := 4079786495351297568357157292300570689,
        encodes := Ra0035.tableCode_eq ▸ encodesTable_tableCode Ra0035.cycles } 16255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0036.table, code := 4079786497836849053484843671589490753,
        encodes := Ra0036.tableCode_eq ▸ encodesTable_tableCode Ra0036.cycles } 16383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0037.table, code := 4164891562860951105881506439416254529,
        encodes := Ra0037.tableCode_eq ▸ encodesTable_tableCode Ra0037.cycles } 17040
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0038.table, code := 4164891562860951105881506441563738177,
        encodes := Ra0038.tableCode_eq ▸ encodesTable_tableCode Ra0038.cycles } 17041
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0039.table, code := 4251132447827810579182810000489975873,
        encodes := Ra0039.tableCode_eq ▸ encodesTable_tableCode Ra0039.cycles } 17406
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0040.table, code := 4251132447827810579182810002637459521,
        encodes := Ra0040.tableCode_eq ▸ encodesTable_tableCode Ra0040.cycles } 17407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0041.table, code := 4251132447827810581344537684188860481,
        encodes := Ra0041.tableCode_eq ▸ encodesTable_tableCode Ra0041.cycles } 18414
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0042.table, code := 4251132447827810581344537686336344129,
        encodes := Ra0042.tableCode_eq ▸ encodesTable_tableCode Ra0042.cycles } 18415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0043.table, code := 4251132447827810583794496018917363777,
        encodes := Ra0043.tableCode_eq ▸ encodesTable_tableCode Ra0043.cycles } 18430
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0044.table, code := 4251132447827810583794496021064847425,
        encodes := Ra0044.tableCode_eq ▸ encodesTable_tableCode Ra0044.cycles } 18431
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0045.table, code := 4167649970724210608166235366817534017,
        encodes := Ra0045.tableCode_eq ▸ encodesTable_tableCode Ra0045.cycles } 19156
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0046.table, code := 4167649970724210608166235368965017665,
        encodes := Ra0046.tableCode_eq ▸ encodesTable_tableCode Ra0046.cycles } 19157
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0047.table, code := 4251132447982553240890807161383555137,
        encodes := Ra0047.tableCode_eq ▸ encodesTable_tableCode Ra0047.cycles } 19454
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0048.table, code := 4251132447982553240890807163531038785,
        encodes := Ra0048.tableCode_eq ▸ encodesTable_tableCode Ra0048.cycles } 19455
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0049.table, code := 4251132447982553243052534845082439745,
        encodes := Ra0049.tableCode_eq ▸ encodesTable_tableCode Ra0049.cycles } 20462
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0050.table, code := 4251132447982553243052534847229923393,
        encodes := Ra0050.tableCode_eq ▸ encodesTable_tableCode Ra0050.cycles } 20463
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0051.table, code := 4251132447982553245502493179810943041,
        encodes := Ra0051.tableCode_eq ▸ encodesTable_tableCode Ra0051.cycles } 20478
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0052.table, code := 4251132447982553245502493181958426689,
        encodes := Ra0052.tableCode_eq ▸ encodesTable_tableCode Ra0052.cycles } 20479
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0053.table, code := 4256324744841092809332564601067540545,
        encodes := Ra0053.tableCode_eq ▸ encodesTable_tableCode Ra0053.cycles } 23550
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0054.table, code := 4256324744841092809332564603215024193,
        encodes := Ra0054.tableCode_eq ▸ encodesTable_tableCode Ra0054.cycles } 23551
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0055.table, code := 4172923397303371817782508794704826433,
        encodes := Ra0055.tableCode_eq ▸ encodesTable_tableCode Ra0055.cycles } 24318
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0056.table, code := 4172923397303371817782508796852310081,
        encodes := Ra0056.tableCode_eq ▸ encodesTable_tableCode Ra0056.cycles } 24319
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0057.table, code := 4256324744841092811494292284766425153,
        encodes := Ra0057.tableCode_eq ▸ encodesTable_tableCode Ra0057.cycles } 24558
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0058.table, code := 4256324744841092811494292286913908801,
        encodes := Ra0058.tableCode_eq ▸ encodesTable_tableCode Ra0058.cycles } 24559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0059.table, code := 4256324744841092813944250619494928449,
        encodes := Ra0059.tableCode_eq ▸ encodesTable_tableCode Ra0059.cycles } 24574
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0060.table, code := 4256324744841092813944250621642412097,
        encodes := Ra0060.tableCode_eq ▸ encodesTable_tableCode Ra0060.cycles } 24575
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0061.table, code := 4164891568122196572603963805517746241,
        encodes := Ra0061.tableCode_eq ▸ encodesTable_tableCode Ra0061.cycles } 26256
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0062.table, code := 4164891568122196572603963807665229889,
        encodes := Ra0062.tableCode_eq ▸ encodesTable_tableCode Ra0062.cycles } 26257
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0063.table, code := 4248292915659917566387804962631716929,
        encodes := Ra0063.tableCode_eq ▸ encodesTable_tableCode Ra0063.cycles } 26498
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0064.table, code := 4248292915659917566387804964779200577,
        encodes := Ra0064.tableCode_eq ▸ encodesTable_tableCode Ra0064.cycles } 26499
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (0 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (0 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (0 + i.val) 0 ≤ Data.profiles (0 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (0 + i.val) 0 = Data.canonicalMask (0 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (0 + i.val) < Data.canonicalMask (0 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (0 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models000
