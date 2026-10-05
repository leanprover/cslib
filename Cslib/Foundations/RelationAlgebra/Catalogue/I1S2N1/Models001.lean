/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0065
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0066
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0067
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0068
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0069
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0070
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0071
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0072
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0073
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0074
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0075
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0076
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0077
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0078
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0079
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0080
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0081
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0082
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0083
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0084
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0085
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0086
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0087
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0088
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0089
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0090
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0091
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0092
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0093
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0094
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0095
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0096
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0097
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0098
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0099
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0100
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0101
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0102
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0103
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0104
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0105
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0106
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0107
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0108
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0109
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0110
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0111
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0112
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0113
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0114
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0115
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0116
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0117
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0118
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0119
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0120
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0121
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0122
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0123
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0124
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0125
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0126
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0127
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0128

/-!
# Certified models 65–128 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models001

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0065.table, code := 8301124041122381698860088485409460289,
        encodes := Ra0065.tableCode_eq ▸ encodesTable_tableCode Ra0065.cycles } 14846
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0066.table, code := 8301124041122381698860088487556943937,
        encodes := Ra0066.tableCode_eq ▸ encodesTable_tableCode Ra0066.cycles } 14847
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0067.table, code := 8298284503693243223954312102024581185,
        encodes := Ra0067.tableCode_eq ▸ encodesTable_tableCode Ra0067.cycles } 15299
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0068.table, code := 8298365633334075682275309740768890945,
        encodes := Ra0068.tableCode_eq ▸ encodesTable_tableCode Ra0068.cycles } 15302
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0069.table, code := 8298365633334075682275309742916374593,
        encodes := Ra0069.tableCode_eq ▸ encodesTable_tableCode Ra0069.cycles } 15303
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0070.table, code := 8298284503693243226404270436753084481,
        encodes := Ra0070.tableCode_eq ▸ encodesTable_tableCode Ra0070.cycles } 15307
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0071.table, code := 8301042911481549242700818530364035137,
        encodes := Ra0071.tableCode_eq ▸ encodesTable_tableCode Ra0071.cycles } 15347
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0072.table, code := 8301124041122381701021816169108344897,
        encodes := Ra0072.tableCode_eq ▸ encodesTable_tableCode Ra0072.cycles } 15350
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0073.table, code := 8301124041122381701021816171255828545,
        encodes := Ra0073.tableCode_eq ▸ encodesTable_tableCode Ra0073.cycles } 15351
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0074.table, code := 8301042911481549245150776865092538433,
        encodes := Ra0074.tableCode_eq ▸ encodesTable_tableCode Ra0074.cycles } 15355
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0075.table, code := 8301124041122381703399716838931959873,
        encodes := Ra0075.tableCode_eq ▸ encodesTable_tableCode Ra0075.cycles } 15357
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0076.table, code := 8301124041122381703471774503836848193,
        encodes := Ra0076.tableCode_eq ▸ encodesTable_tableCode Ra0076.cycles } 15358
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0077.table, code := 8301124041122381703471774505984331841,
        encodes := Ra0077.tableCode_eq ▸ encodesTable_tableCode Ra0077.cycles } 15359
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0078.table, code := 8303557930347357910263336657647571009,
        encodes := Ra0078.tableCode_eq ▸ encodesTable_tableCode Ra0078.cycles } 15822
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0079.table, code := 8303557930347357910263336659795054657,
        encodes := Ra0079.tableCode_eq ▸ encodesTable_tableCode Ra0079.cycles } 15823
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0080.table, code := 8303720189701560737769713697984614465,
        encodes := Ra0080.tableCode_eq ▸ encodesTable_tableCode Ra0080.cycles } 15837
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0081.table, code := 8303720189701560737841771362889502785,
        encodes := Ra0081.tableCode_eq ▸ encodesTable_tableCode Ra0081.cycles } 15838
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0082.table, code := 8303720189701560737841771365036986433,
        encodes := Ra0082.tableCode_eq ▸ encodesTable_tableCode Ra0082.cycles } 15839
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0083.table, code := 8306316338135663928937785421082136641,
        encodes := Ra0083.tableCode_eq ▸ encodesTable_tableCode Ra0083.cycles } 15869
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0084.table, code := 8306316338135663929009843085987024961,
        encodes := Ra0084.tableCode_eq ▸ encodesTable_tableCode Ra0084.cycles } 15870
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0085.table, code := 8306316338135663929009843088134508609,
        encodes := Ra0085.tableCode_eq ▸ encodesTable_tableCode Ra0085.cycles } 15871
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0086.table, code := 8303557930347357914875022678222442561,
        encodes := Ra0086.tableCode_eq ▸ encodesTable_tableCode Ra0086.cycles } 16335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0087.table, code := 8303720189701560740003499048735871041,
        encodes := Ra0087.tableCode_eq ▸ encodesTable_tableCode Ra0087.cycles } 16343
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0088.table, code := 8303720189701560742453457383464374337,
        encodes := Ra0088.tableCode_eq ▸ encodesTable_tableCode Ra0088.cycles } 16351
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0089.table, code := 8306316338135663931171570771833393217,
        encodes := Ra0089.tableCode_eq ▸ encodesTable_tableCode Ra0089.cycles } 16375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0090.table, code := 8306316338135663933621529106561896513,
        encodes := Ra0090.tableCode_eq ▸ encodesTable_tableCode Ra0090.cycles } 16383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0091.table, code := 25051474503060636679177718718552870977,
        encodes := Ra0091.tableCode_eq ▸ encodesTable_tableCode Ra0091.cycles } 16895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0092.table, code := 25051474503060636683789404736980258881,
        encodes := Ra0092.tableCode_eq ▸ encodesTable_tableCode Ra0092.cycles } 17407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0093.table, code := 22311402013585191807579836967280709697,
        encodes := Ra0093.tableCode_eq ▸ encodesTable_tableCode Ra0093.cycles } 17414
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0094.table, code := 22311402013585191807579836969428193345,
        encodes := Ra0094.tableCode_eq ▸ encodesTable_tableCode Ra0094.cycles } 17415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0095.table, code := 22311402013585191809957737637104324673,
        encodes := Ra0095.tableCode_eq ▸ encodesTable_tableCode Ra0095.cycles } 17421
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0096.table, code := 22311402013585191810029795302009212993,
        encodes := Ra0096.tableCode_eq ▸ encodesTable_tableCode Ra0096.cycles } 17422
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0097.table, code := 22311402013585191810029795304156696641,
        encodes := Ra0097.tableCode_eq ▸ encodesTable_tableCode Ra0097.cycles } 17423
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0098.table, code := 22311564272939394635086214005470269505,
        encodes := Ra0098.tableCode_eq ▸ encodesTable_tableCode Ra0098.cycles } 17428
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0099.table, code := 22314160421373497826254285728567791681,
        encodes := Ra0099.tableCode_eq ▸ encodesTable_tableCode Ra0099.cycles } 17460
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0100.table, code := 22314160421373497828704244065443778625,
        encodes := Ra0100.tableCode_eq ▸ encodesTable_tableCode Ra0100.cycles } 17469
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0101.table, code := 22314160421373497828776301730348666945,
        encodes := Ra0101.tableCode_eq ▸ encodesTable_tableCode Ra0101.cycles } 17470
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0102.table, code := 22314160421373497828776301732496150593,
        encodes := Ra0102.tableCode_eq ▸ encodesTable_tableCode Ra0102.cycles } 17471
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0103.table, code := 22312051129920671177675650338782449729,
        encodes := Ra0103.tableCode_eq ▸ encodesTable_tableCode Ra0103.cycles } 17485
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0104.table, code := 24970182526203904874177028595294408769,
        encodes := Ra0104.tableCode_eq ▸ encodesTable_tableCode Ra0104.cycles } 17548
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0105.table, code := 24970182526203904874177028597441892417,
        encodes := Ra0105.tableCode_eq ▸ encodesTable_tableCode Ra0105.cycles } 17549
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0106.table, code := 24970831642539384241894941296972533825,
        encodes := Ra0106.tableCode_eq ▸ encodesTable_tableCode Ra0106.cycles } 17612
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0107.table, code := 24970831642539384241894941299120017473,
        encodes := Ra0107.tableCode_eq ▸ encodesTable_tableCode Ra0107.cycles } 17613
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0108.table, code := 22395046750026067367968620620361764929,
        encodes := Ra0108.tableCode_eq ▸ encodesTable_tableCode Ra0108.cycles } 17736
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0109.table, code := 22395046750026067367968620622509248577,
        encodes := Ra0109.tableCode_eq ▸ encodesTable_tableCode Ra0109.cycles } 17737
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0110.table, code := 22395127879666899826289618261253558337,
        encodes := Ra0110.tableCode_eq ▸ encodesTable_tableCode Ra0110.cycles } 17740
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0111.table, code := 22395127879666899826289618263401041985,
        encodes := Ra0111.tableCode_eq ▸ encodesTable_tableCode Ra0111.cycles } 17741
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0112.table, code := 25053827262644780432187911582846816321,
        encodes := Ra0112.tableCode_eq ▸ encodesTable_tableCode Ra0112.cycles } 17865
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0113.table, code := 25053908392285612890508909221591126081,
        encodes := Ra0113.tableCode_eq ▸ encodesTable_tableCode Ra0113.cycles } 17868
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0114.table, code := 25053908392285612890508909223738609729,
        encodes := Ra0114.tableCode_eq ▸ encodesTable_tableCode Ra0114.cycles } 17869
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0115.table, code := 25056585670433086448556517343510138945,
        encodes := Ra0115.tableCode_eq ▸ encodesTable_tableCode Ra0115.cycles } 17907
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0116.table, code := 25056666800073918906877514982254448705,
        encodes := Ra0116.tableCode_eq ▸ encodesTable_tableCode Ra0116.cycles } 17910
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0117.table, code := 25056666800073918906877514984401932353,
        encodes := Ra0117.tableCode_eq ▸ encodesTable_tableCode Ra0117.cycles } 17911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0118.table, code := 25056585670433086450934418011186270273,
        encodes := Ra0118.tableCode_eq ▸ encodesTable_tableCode Ra0118.cycles } 17913
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0119.table, code := 25056585670433086451006475678238642241,
        encodes := Ra0119.tableCode_eq ▸ encodesTable_tableCode Ra0119.cycles } 17915
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0120.table, code := 25056666800073918909255415652078063681,
        encodes := Ra0120.tableCode_eq ▸ encodesTable_tableCode Ra0120.cycles } 17917
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0121.table, code := 25056666800073918909327473316982952001,
        encodes := Ra0121.tableCode_eq ▸ encodesTable_tableCode Ra0121.cycles } 17918
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0122.table, code := 25056666800073918909327473319130435649,
        encodes := Ra0122.tableCode_eq ▸ encodesTable_tableCode Ra0122.cycles } 17919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0123.table, code := 22311402013585191812191522987855581249,
        encodes := Ra0123.tableCode_eq ▸ encodesTable_tableCode Ra0123.cycles } 17927
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0124.table, code := 22311402013585191814641481322584084545,
        encodes := Ra0124.tableCode_eq ▸ encodesTable_tableCode Ra0124.cycles } 17935
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0125.table, code := 22311564272939394642219916027826016321,
        encodes := Ra0125.tableCode_eq ▸ encodesTable_tableCode Ra0125.cycles } 17951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0126.table, code := 22314160421373497830938029416195035201,
        encodes := Ra0126.tableCode_eq ▸ encodesTable_tableCode Ra0126.cycles } 17975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0127.table, code := 22314160421373497833387987750923538497,
        encodes := Ra0127.tableCode_eq ▸ encodesTable_tableCode Ra0127.cycles } 17983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0128.table, code := 22312051129920671182287336357209837633,
        encodes := Ra0128.tableCode_eq ▸ encodesTable_tableCode Ra0128.cycles } 17997
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (64 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (64 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
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

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models001
