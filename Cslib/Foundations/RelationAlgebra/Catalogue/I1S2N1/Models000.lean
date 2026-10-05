/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0001
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0002
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0003
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0004
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0005
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0006
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0007
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0008
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0009
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0010
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0011
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0012
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0013
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0014
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0015
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0016
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0017
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0018
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0019
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0020
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0021
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0022
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0023
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0024
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0025
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0026
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0027
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0028
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0029
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0030
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0031
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0032
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0033
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0034
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0035
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0036
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0037
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0038
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0039
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0040
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0041
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0042
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0043
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0044
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0045
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0046
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0047
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0048
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0049
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0050
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0051
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0052
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0053
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0054
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0055
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0056
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0057
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0058
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0059
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0060
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0061
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0062
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0063
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0064

/-!
# Certified models 1–64 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models000

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0001.table, code := 2786823483380992864190801829192536129,
        encodes := Ra0001.tableCode_eq ▸ encodesTable_tableCode Ra0001.cycles } 505
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0002.table, code := 2786904613021825322583857137136701505,
        encodes := Ra0002.tableCode_eq ▸ encodesTable_tableCode Ra0002.cycles } 511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0003.table, code := 2786904613021825327195543155564089409,
        encodes := Ra0003.tableCode_eq ▸ encodesTable_tableCode Ra0003.cycles } 1023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0004.table, code := 2705531506524261059262169372986445889,
        encodes := Ra0004.tableCode_eq ▸ encodesTable_tableCode Ra0004.cycles } 1160
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0005.table, code := 2789257372605969075594050001430646849,
        encodes := Ra0005.tableCode_eq ▸ encodesTable_tableCode Ra0005.cycles } 1481
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0006.table, code := 2789338502246801533915047642322440257,
        encodes := Ra0006.tableCode_eq ▸ encodesTable_tableCode Ra0006.cycles } 1485
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0007.table, code := 2792015780394275094412614096822472769,
        encodes := Ra0007.tableCode_eq ▸ encodesTable_tableCode Ra0007.cycles } 1531
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0008.table, code := 2792096910035107552733611737714266177,
        encodes := Ra0008.tableCode_eq ▸ encodesTable_tableCode Ra0008.cycles } 1535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0009.table, code := 2705531506524261063873855391413833793,
        encodes := Ra0009.tableCode_eq ▸ encodesTable_tableCode Ra0009.cycles } 1672
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0010.table, code := 2789257372605969080205736019858034753,
        encodes := Ra0010.tableCode_eq ▸ encodesTable_tableCode Ra0010.cycles } 1993
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0011.table, code := 2789338502246801538526733660749828161,
        encodes := Ra0011.tableCode_eq ▸ encodesTable_tableCode Ra0011.cycles } 1997
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0012.table, code := 2792015780394275099024300115249860673,
        encodes := Ra0012.tableCode_eq ▸ encodesTable_tableCode Ra0012.cycles } 2043
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0013.table, code := 2792096910035107557345297756141654081,
        encodes := Ra0013.tableCode_eq ▸ encodesTable_tableCode Ra0013.cycles } 2047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0014.table, code := 2807673958912289956774559488894308417,
        encodes := Ra0014.tableCode_eq ▸ encodesTable_tableCode Ra0014.cycles } 2559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0015.table, code := 2807673958912289961386245507321696321,
        encodes := Ra0015.tableCode_eq ▸ encodesTable_tableCode Ra0015.cycles } 3071
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0016.table, code := 2812866255925572186924314089471873089,
        encodes := Ra0016.tableCode_eq ▸ encodesTable_tableCode Ra0016.cycles } 3583
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0017.table, code := 2812866255925572191536000107899260993,
        encodes := Ra0017.tableCode_eq ▸ encodesTable_tableCode Ra0017.cycles } 4095
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0018.table, code := 5452581145401447139910281007189987393,
        encodes := Ra0018.tableCode_eq ▸ encodesTable_tableCode Ra0018.cycles } 4424
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0019.table, code := 5452581145401447139910281009337471041,
        encodes := Ra0019.tableCode_eq ▸ encodesTable_tableCode Ra0019.cycles } 4425
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0020.table, code := 8111361658020160201751671299851423809,
        encodes := Ra0020.tableCode_eq ▸ encodesTable_tableCode Ra0020.cycles } 4546
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0021.table, code := 8111361658020160201751671301998907457,
        encodes := Ra0021.tableCode_eq ▸ encodesTable_tableCode Ra0021.cycles } 4547
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0022.table, code := 8111442787660992660072668940743217217,
        encodes := Ra0022.tableCode_eq ▸ encodesTable_tableCode Ra0022.cycles } 4550
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0023.table, code := 8111442787660992660072668942890700865,
        encodes := Ra0023.tableCode_eq ▸ encodesTable_tableCode Ra0023.cycles } 4551
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0024.table, code := 8114201195449298681269133703811174465,
        encodes := Ra0024.tableCode_eq ▸ encodesTable_tableCode Ra0024.cycles } 4606
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0025.table, code := 8114201195449298681269133705958658113,
        encodes := Ra0025.tableCode_eq ▸ encodesTable_tableCode Ra0025.cycles } 4607
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0026.table, code := 8114201195449298683430861387510059073,
        encodes := Ra0026.tableCode_eq ▸ encodesTable_tableCode Ra0026.cycles } 5110
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0027.table, code := 8114201195449298683430861389657542721,
        encodes := Ra0027.tableCode_eq ▸ encodesTable_tableCode Ra0027.cycles } 5111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0028.table, code := 8114201195449298685880819722238562369,
        encodes := Ra0028.tableCode_eq ▸ encodesTable_tableCode Ra0028.cycles } 5118
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0029.table, code := 8114201195449298685880819724386046017,
        encodes := Ra0029.tableCode_eq ▸ encodesTable_tableCode Ra0029.cycles } 5119
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0030.table, code := 8119393492462580911418888304388739137,
        encodes := Ra0030.tableCode_eq ▸ encodesTable_tableCode Ra0030.cycles } 5630
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0031.table, code := 8119393492462580911418888306536222785,
        encodes := Ra0031.tableCode_eq ▸ encodesTable_tableCode Ra0031.cycles } 5631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0032.table, code := 5460612979843867851811283362478559297,
        encodes := Ra0032.tableCode_eq ▸ encodesTable_tableCode Ra0032.cycles } 6014
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0033.table, code := 5460612979843867851811283364626042945,
        encodes := Ra0033.tableCode_eq ▸ encodesTable_tableCode Ra0033.cycles } 6015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0034.table, code := 8119393492462580913580615988087623745,
        encodes := Ra0034.tableCode_eq ▸ encodesTable_tableCode Ra0034.cycles } 6134
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0035.table, code := 8119393492462580913580615990235107393,
        encodes := Ra0035.tableCode_eq ▸ encodesTable_tableCode Ra0035.cycles } 6135
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0036.table, code := 8119393492462580916030574322816127041,
        encodes := Ra0036.tableCode_eq ▸ encodesTable_tableCode Ra0036.cycles } 6142
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0037.table, code := 8119393492462580916030574324963610689,
        encodes := Ra0037.tableCode_eq ▸ encodesTable_tableCode Ra0037.cycles } 6143
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0038.table, code := 8134970541339763315459836055568781377,
        encodes := Ra0038.tableCode_eq ▸ encodesTable_tableCode Ra0038.cycles } 6654
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0039.table, code := 8134970541339763315459836057716265025,
        encodes := Ra0039.tableCode_eq ▸ encodesTable_tableCode Ra0039.cycles } 6655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0040.table, code := 8134970541339763317621563739267665985,
        encodes := Ra0040.tableCode_eq ▸ encodesTable_tableCode Ra0040.cycles } 7158
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0041.table, code := 8134970541339763317621563741415149633,
        encodes := Ra0041.tableCode_eq ▸ encodesTable_tableCode Ra0041.cycles } 7159
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0042.table, code := 8134970541339763320071522073996169281,
        encodes := Ra0042.tableCode_eq ▸ encodesTable_tableCode Ra0042.cycles } 7166
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0043.table, code := 8134970541339763320071522076143652929,
        encodes := Ra0043.tableCode_eq ▸ encodesTable_tableCode Ra0043.cycles } 7167
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0044.table, code := 8139513722017566177891677954468220993,
        encodes := Ra0044.tableCode_eq ▸ encodesTable_tableCode Ra0044.cycles } 7614
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0045.table, code := 8139513722017566177891677956615704641,
        encodes := Ra0045.tableCode_eq ▸ encodesTable_tableCode Ra0045.cycles } 7615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0046.table, code := 8140162838353045545609590656146346049,
        encodes := Ra0046.tableCode_eq ▸ encodesTable_tableCode Ra0046.cycles } 7678
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0047.table, code := 8140162838353045545609590658293829697,
        encodes := Ra0047.tableCode_eq ▸ encodesTable_tableCode Ra0047.cycles } 7679
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0048.table, code := 8139513722017566182503363975043092545,
        encodes := Ra0048.tableCode_eq ▸ encodesTable_tableCode Ra0048.cycles } 8127
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0049.table, code := 8140162838353045547771318339845230657,
        encodes := Ra0049.tableCode_eq ▸ encodesTable_tableCode Ra0049.cycles } 8182
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0050.table, code := 8140162838353045547771318341992714305,
        encodes := Ra0050.tableCode_eq ▸ encodesTable_tableCode Ra0050.cycles } 8183
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0051.table, code := 8140162838353045550221276674573733953,
        encodes := Ra0051.tableCode_eq ▸ encodesTable_tableCode Ra0051.cycles } 8190
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0052.table, code := 8140162838353045550221276676721217601,
        encodes := Ra0052.tableCode_eq ▸ encodesTable_tableCode Ra0052.cycles } 8191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0053.table, code := 2970987921265769860657349514775236673,
        encodes := Ra0053.tableCode_eq ▸ encodesTable_tableCode Ra0053.cycles } 10691
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0054.table, code := 2971069050906602318978347155667030081,
        encodes := Ra0054.tableCode_eq ▸ encodesTable_tableCode Ra0054.cycles } 10695
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0055.table, code := 2973827458694908340174811918734987329,
        encodes := Ra0055.tableCode_eq ▸ encodesTable_tableCode Ra0055.cycles } 10751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0056.table, code := 2970987921265769865269035533202624577,
        encodes := Ra0056.tableCode_eq ▸ encodesTable_tableCode Ra0056.cycles } 11203
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0057.table, code := 2971069050906602323590033174094417985,
        encodes := Ra0057.tableCode_eq ▸ encodesTable_tableCode Ra0057.cycles } 11207
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0058.table, code := 2973827458694908344786497937162375233,
        encodes := Ra0058.tableCode_eq ▸ encodesTable_tableCode Ra0058.cycles } 11263
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0059.table, code := 2979019755708190570324566519312552001,
        encodes := Ra0059.tableCode_eq ▸ encodesTable_tableCode Ra0059.cycles } 11775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0060.table, code := 2979019755708190574936252537739939905,
        encodes := Ra0060.tableCode_eq ▸ encodesTable_tableCode Ra0060.cycles } 12287
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0061.table, code := 8298284503693243221720526751273324609,
        encodes := Ra0061.tableCode_eq ▸ encodesTable_tableCode Ra0061.cycles } 14793
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0062.table, code := 8298284503693243221792584416178212929,
        encodes := Ra0062.tableCode_eq ▸ encodesTable_tableCode Ra0062.cycles } 14794
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0063.table, code := 8298284503693243221792584418325696577,
        encodes := Ra0063.tableCode_eq ▸ encodesTable_tableCode Ra0063.cycles } 14795
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0064.table, code := 8301124041122381698788030820504571969,
        encodes := Ra0064.tableCode_eq ▸ encodesTable_tableCode Ra0064.cycles } 14845
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (0 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (0 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
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

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models000
