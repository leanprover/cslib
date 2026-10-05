/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0065
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0066
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0067
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0068
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0069
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0070
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0071
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0072
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0073
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0074
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0075
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0076
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0077
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0078
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0079
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0080
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0081
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0082
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0083
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0084
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0085
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0086
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0087
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0088
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0089
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0090
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0091
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0092
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0093
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0094
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0095
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0096
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0097
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0098
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0099
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0100
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0101
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0102
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0103
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0104
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0105
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0106
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0107
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0108
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0109
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0110
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0111
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0112
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0113
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0114
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0115
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0116
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0117
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0118
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0119
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0120
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0121
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0122
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0123
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0124
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0125
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0126
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0127
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0128

/-!
# Certified models 65–128 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models001

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0065.table, code := 4248374045300750024708802603523510337,
        encodes := Ra0065.tableCode_eq ▸ encodesTable_tableCode Ra0065.cycles } 26510
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0066.table, code := 4248374045300750024708802605670993985,
        encodes := Ra0066.tableCode_eq ▸ encodesTable_tableCode Ra0066.cycles } 26511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0067.table, code := 4248292915659917568837763297360220225,
        encodes := Ra0067.tableCode_eq ▸ encodesTable_tableCode Ra0067.cycles } 26514
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0068.table, code := 4248292915659917568837763299507703873,
        encodes := Ra0068.tableCode_eq ▸ encodesTable_tableCode Ra0068.cycles } 26515
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0069.table, code := 4251051323450641436773542856933773377,
        encodes := Ra0069.tableCode_eq ▸ encodesTable_tableCode Ra0069.cycles } 26598
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0070.table, code := 4251051323450641436773542859081257025,
        encodes := Ra0070.tableCode_eq ▸ encodesTable_tableCode Ra0070.cycles } 26599
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0071.table, code := 4251132453089056043455309031862964289,
        encodes := Ra0071.tableCode_eq ▸ encodesTable_tableCode Ra0071.cycles } 26606
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0072.table, code := 4251132453089056043455309034010447937,
        encodes := Ra0072.tableCode_eq ▸ encodesTable_tableCode Ra0072.cycles } 26607
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0073.table, code := 4251051323450641439223501191662276673,
        encodes := Ra0073.tableCode_eq ▸ encodesTable_tableCode Ra0073.cycles } 26614
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0074.table, code := 4251051323450641439223501193809760321,
        encodes := Ra0074.tableCode_eq ▸ encodesTable_tableCode Ra0074.cycles } 26615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0075.table, code := 4251132453089056045905267366591467585,
        encodes := Ra0075.tableCode_eq ▸ encodesTable_tableCode Ra0075.cycles } 26622
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0076.table, code := 4251132453089056045905267368738951233,
        encodes := Ra0076.tableCode_eq ▸ encodesTable_tableCode Ra0076.cycles } 26623
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0077.table, code := 4251051323605384096319812334128468033,
        encodes := Ra0077.tableCode_eq ▸ encodesTable_tableCode Ra0077.cycles } 27638
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0078.table, code := 4251051323605384096319812336275951681,
        encodes := Ra0078.tableCode_eq ▸ encodesTable_tableCode Ra0078.cycles } 27639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0079.table, code := 4251132453243798703001578509057658945,
        encodes := Ra0079.tableCode_eq ▸ encodesTable_tableCode Ra0079.cycles } 27646
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0080.table, code := 4251132453243798703001578511205142593,
        encodes := Ra0080.tableCode_eq ▸ encodesTable_tableCode Ra0080.cycles } 27647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0081.table, code := 4251051323605384098481540017827352641,
        encodes := Ra0081.tableCode_eq ▸ encodesTable_tableCode Ra0081.cycles } 28646
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0082.table, code := 4251051323605384098481540019974836289,
        encodes := Ra0082.tableCode_eq ▸ encodesTable_tableCode Ra0082.cycles } 28647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0083.table, code := 4251132453243798705163306192756543553,
        encodes := Ra0083.tableCode_eq ▸ encodesTable_tableCode Ra0083.cycles } 28654
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0084.table, code := 4251132453243798705163306194904027201,
        encodes := Ra0084.tableCode_eq ▸ encodesTable_tableCode Ra0084.cycles } 28655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0085.table, code := 4251051323605384100931498352555855937,
        encodes := Ra0085.tableCode_eq ▸ encodesTable_tableCode Ra0085.cycles } 28662
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0086.table, code := 4251051323605384100931498354703339585,
        encodes := Ra0086.tableCode_eq ▸ encodesTable_tableCode Ra0086.cycles } 28663
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0087.table, code := 4251132453243798707613264527485046849,
        encodes := Ra0087.tableCode_eq ▸ encodesTable_tableCode Ra0087.cycles } 28670
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0088.table, code := 4251132453243798707613264529632530497,
        encodes := Ra0088.tableCode_eq ▸ encodesTable_tableCode Ra0088.cycles } 28671
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0089.table, code := 4256243617823629517925886233629954113,
        encodes := Ra0089.tableCode_eq ▸ encodesTable_tableCode Ra0089.cycles } 29558
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0090.table, code := 4256243617823629517925886235777437761,
        encodes := Ra0090.tableCode_eq ▸ encodesTable_tableCode Ra0090.cycles } 29559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0091.table, code := 4256324747462044124607652408559145025,
        encodes := Ra0091.tableCode_eq ▸ encodesTable_tableCode Ra0091.cycles } 29566
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0092.table, code := 4256324747462044124607652410706628673,
        encodes := Ra0092.tableCode_eq ▸ encodesTable_tableCode Ra0092.cycles } 29567
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0093.table, code := 4253566342241496620797838487302967361,
        encodes := Ra0093.tableCode_eq ▸ encodesTable_tableCode Ra0093.cycles } 29630
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0094.table, code := 4253566342241496620797838489450451009,
        encodes := Ra0094.tableCode_eq ▸ encodesTable_tableCode Ra0094.cycles } 29631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0095.table, code := 4256243620309181003053572612918874177,
        encodes := Ra0095.tableCode_eq ▸ encodesTable_tableCode Ra0095.cycles } 29686
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0096.table, code := 4256243620309181003053572615066357825,
        encodes := Ra0096.tableCode_eq ▸ encodesTable_tableCode Ra0096.cycles } 29687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0097.table, code := 4256324749947595609735338787848065089,
        encodes := Ra0097.tableCode_eq ▸ encodesTable_tableCode Ra0097.cycles } 29694
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0098.table, code := 4256324749947595609735338789995548737,
        encodes := Ra0098.tableCode_eq ▸ encodesTable_tableCode Ra0098.cycles } 29695
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0099.table, code := 4256243617823629522537572254204825665,
        encodes := Ra0099.tableCode_eq ▸ encodesTable_tableCode Ra0099.cycles } 30583
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0100.table, code := 4256324747462044129219338426986532929,
        encodes := Ra0100.tableCode_eq ▸ encodesTable_tableCode Ra0100.cycles } 30590
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0101.table, code := 4256324747462044129219338429134016577,
        encodes := Ra0101.tableCode_eq ▸ encodesTable_tableCode Ra0101.cycles } 30591
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0102.table, code := 4253566342241496622959566171001851969,
        encodes := Ra0102.tableCode_eq ▸ encodesTable_tableCode Ra0102.cycles } 30638
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0103.table, code := 4253566342241496622959566173149335617,
        encodes := Ra0103.tableCode_eq ▸ encodesTable_tableCode Ra0103.cycles } 30639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0104.table, code := 4253566342241496625409524505730355265,
        encodes := Ra0104.tableCode_eq ▸ encodesTable_tableCode Ra0104.cycles } 30654
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0105.table, code := 4253566342241496625409524507877838913,
        encodes := Ra0105.tableCode_eq ▸ encodesTable_tableCode Ra0105.cycles } 30655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0106.table, code := 4256243620309181005215300296617758785,
        encodes := Ra0106.tableCode_eq ▸ encodesTable_tableCode Ra0106.cycles } 30694
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0107.table, code := 4256243620309181005215300298765242433,
        encodes := Ra0107.tableCode_eq ▸ encodesTable_tableCode Ra0107.cycles } 30695
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0108.table, code := 4256324749947595611897066471546949697,
        encodes := Ra0108.tableCode_eq ▸ encodesTable_tableCode Ra0108.cycles } 30702
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0109.table, code := 4256324749947595611897066473694433345,
        encodes := Ra0109.tableCode_eq ▸ encodesTable_tableCode Ra0109.cycles } 30703
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0110.table, code := 4256243620309181007665258631346262081,
        encodes := Ra0110.tableCode_eq ▸ encodesTable_tableCode Ra0110.cycles } 30710
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0111.table, code := 4256243620309181007665258633493745729,
        encodes := Ra0111.tableCode_eq ▸ encodesTable_tableCode Ra0111.cycles } 30711
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0112.table, code := 4256324749947595614347024806275452993,
        encodes := Ra0112.tableCode_eq ▸ encodesTable_tableCode Ra0112.cycles } 30718
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0113.table, code := 4256324749947595614347024808422936641,
        encodes := Ra0113.tableCode_eq ▸ encodesTable_tableCode Ra0113.cycles } 30719
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0114.table, code := 4256324747616786786315649569452724289,
        encodes := Ra0114.tableCode_eq ▸ encodesTable_tableCode Ra0114.cycles } 31614
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0115.table, code := 4256324747616786786315649571600207937,
        encodes := Ra0115.tableCode_eq ▸ encodesTable_tableCode Ra0115.cycles } 31615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0116.table, code := 4253566342396239282505835648196546625,
        encodes := Ra0116.tableCode_eq ▸ encodesTable_tableCode Ra0116.cycles } 31678
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0117.table, code := 4253566342396239282505835650344030273,
        encodes := Ra0117.tableCode_eq ▸ encodesTable_tableCode Ra0117.cycles } 31679
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0118.table, code := 4256243620463923664761569773812453441,
        encodes := Ra0118.tableCode_eq ▸ encodesTable_tableCode Ra0118.cycles } 31734
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0119.table, code := 4256243620463923664761569775959937089,
        encodes := Ra0119.tableCode_eq ▸ encodesTable_tableCode Ra0119.cycles } 31735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0120.table, code := 4256324750102338271443335948741644353,
        encodes := Ra0120.tableCode_eq ▸ encodesTable_tableCode Ra0120.cycles } 31742
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0121.table, code := 4256324750102338271443335950889128001,
        encodes := Ra0121.tableCode_eq ▸ encodesTable_tableCode Ra0121.cycles } 31743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0122.table, code := 4170164994856100439244490708818858049,
        encodes := Ra0122.tableCode_eq ▸ encodesTable_tableCode Ra0122.cycles } 32440
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0123.table, code := 4170164994856100439244490710966341697,
        encodes := Ra0123.tableCode_eq ▸ encodesTable_tableCode Ra0123.cycles } 32441
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0124.table, code := 4172842272926202673211513967449739329,
        encodes := Ra0124.tableCode_eq ▸ encodesTable_tableCode Ra0124.cycles } 32502
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0125.table, code := 4172842272926202673211513969597222977,
        encodes := Ra0125.tableCode_eq ▸ encodesTable_tableCode Ra0125.cycles } 32503
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0126.table, code := 4172923402564617279893280142378930241,
        encodes := Ra0126.tableCode_eq ▸ encodesTable_tableCode Ra0126.cycles } 32510
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0127.table, code := 4172923402564617279893280144526413889,
        encodes := Ra0127.tableCode_eq ▸ encodesTable_tableCode Ra0127.cycles } 32511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0128.table, code := 4256324747616786790927335590027595841,
        encodes := Ra0128.tableCode_eq ▸ encodesTable_tableCode Ra0128.cycles } 32639
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (64 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (64 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (64 + i.val) 0 ≤ Data.profiles (64 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (64 + i.val) 0 = Data.canonicalMask (64 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (64 + i.val) < Data.canonicalMask (64 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (64 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models001
