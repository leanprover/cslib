/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0961
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0962
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0963
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0964
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0965
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0966
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0967
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0968
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0969
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0970
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0971
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0972
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0973
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0974
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0975
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0976
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0977
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0978
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0979
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0980
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0981
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0982
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0983
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0984
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0985
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0986
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0987
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0988
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0989
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0990
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0991
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0992
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0993
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0994
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0995
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0996
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0997
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0998
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0999
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1000
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1001
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1002
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1003
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1004
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1005
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1006
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1007
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1008
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1009
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1010
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1011
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1012
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1013
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1014
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1015
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1016
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1017
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1018
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1019
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1020
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1021
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1022
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1023
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra1024

/-!
# Certified models 961–1024 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models015

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0961.table, code := 41017787368587759879737233101528764481,
        encodes := Ra0961.tableCode_eq ▸ encodesTable_tableCode Ra0961.cycles } 54781
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0962.table, code := 41017787368587759879809290766433652801,
        encodes := Ra0962.tableCode_eq ▸ encodesTable_tableCode Ra0962.cycles } 54782
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0963.table, code := 41017787368587759879809290768581136449,
        encodes := Ra0963.tableCode_eq ▸ encodesTable_tableCode Ra0963.cycles } 54783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0964.table, code := 40934061502506051865567080158930931777,
        encodes := Ra0964.tableCode_eq ▸ encodesTable_tableCode Ra0964.cycles } 54965
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0965.table, code := 40934061502506051865639137825983303745,
        encodes := Ra0965.tableCode_eq ▸ encodesTable_tableCode Ra0965.cycles } 54967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0966.table, code := 40934061502506051868089096160711807041,
        encodes := Ra0966.tableCode_eq ▸ encodesTable_tableCode Ra0966.cycles } 54975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0967.table, code := 40934548359487328408156516487948144705,
        encodes := Ra0967.tableCode_eq ▸ encodesTable_tableCode Ra0967.cycles } 55020
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0968.table, code := 40934548359487328408156516490095628353,
        encodes := Ra0968.tableCode_eq ▸ encodesTable_tableCode Ra0968.cycles } 55021
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0969.table, code := 40934548359487328408228574155000516673,
        encodes := Ra0969.tableCode_eq ▸ encodesTable_tableCode Ra0969.cycles } 55022
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0970.table, code := 40934548359487328408228574157148000321,
        encodes := Ra0970.tableCode_eq ▸ encodesTable_tableCode Ra0970.cycles } 55023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0971.table, code := 40934629489200698774963995219717263425,
        encodes := Ra0971.tableCode_eq ▸ encodesTable_tableCode Ra0971.cycles } 55025
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0972.table, code := 40934629489200698775036052884622151745,
        encodes := Ra0972.tableCode_eq ▸ encodesTable_tableCode Ra0972.cycles } 55026
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0973.table, code := 40934629489200698775036052886769635393,
        encodes := Ra0973.tableCode_eq ▸ encodesTable_tableCode Ra0973.cycles } 55027
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0974.table, code := 40934710618841531233284992858461573185,
        encodes := Ra0974.tableCode_eq ▸ encodesTable_tableCode Ra0974.cycles } 55028
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0975.table, code := 40934710618841531233284992860609056833,
        encodes := Ra0975.tableCode_eq ▸ encodesTable_tableCode Ra0975.cycles } 55029
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0976.table, code := 40934710618841531233357050525513945153,
        encodes := Ra0976.tableCode_eq ▸ encodesTable_tableCode Ra0976.cycles } 55030
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0977.table, code := 40934710618841531233357050527661428801,
        encodes := Ra0977.tableCode_eq ▸ encodesTable_tableCode Ra0977.cycles } 55031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0978.table, code := 40934629489200698777413953554445766721,
        encodes := Ra0978.tableCode_eq ▸ encodesTable_tableCode Ra0978.cycles } 55033
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0979.table, code := 40934629489200698777486011219350655041,
        encodes := Ra0979.tableCode_eq ▸ encodesTable_tableCode Ra0979.cycles } 55034
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0980.table, code := 40934629489200698777486011221498138689,
        encodes := Ra0980.tableCode_eq ▸ encodesTable_tableCode Ra0980.cycles } 55035
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0981.table, code := 40934710618841531235734951193190076481,
        encodes := Ra0981.tableCode_eq ▸ encodesTable_tableCode Ra0981.cycles } 55036
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0982.table, code := 40934710618841531235734951195337560129,
        encodes := Ra0982.tableCode_eq ▸ encodesTable_tableCode Ra0982.cycles } 55037
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0983.table, code := 40934710618841531235807008860242448449,
        encodes := Ra0983.tableCode_eq ▸ encodesTable_tableCode Ra0983.cycles } 55038
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0984.table, code := 40934710618841531235807008862389932097,
        encodes := Ra0984.tableCode_eq ▸ encodesTable_tableCode Ra0984.cycles } 55039
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0985.table, code := 38356167318539908343062124088239853633,
        encodes := Ra0985.tableCode_eq ▸ encodesTable_tableCode Ra0985.cycles } 55112
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0986.table, code := 38356167318539908343062124090387337281,
        encodes := Ra0986.tableCode_eq ▸ encodesTable_tableCode Ra0986.cycles } 55113
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0987.table, code := 38356410707534943629033614101425950785,
        encodes := Ra0987.tableCode_eq ▸ encodesTable_tableCode Ra0987.cycles } 55134
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0988.table, code := 38356410707534943629033614103573434433,
        encodes := Ra0988.tableCode_eq ▸ encodesTable_tableCode Ra0988.cycles } 55135
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0989.table, code := 38358925726328214359430729848903176257,
        encodes := Ra0989.tableCode_eq ▸ encodesTable_tableCode Ra0989.cycles } 55154
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0990.table, code := 38358925726328214359430729851050659905,
        encodes := Ra0990.tableCode_eq ▸ encodesTable_tableCode Ra0990.cycles } 55155
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0991.table, code := 38359006855969046817679669822742597697,
        encodes := Ra0991.tableCode_eq ▸ encodesTable_tableCode Ra0991.cycles } 55156
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0992.table, code := 38359006855969046817679669824890081345,
        encodes := Ra0992.tableCode_eq ▸ encodesTable_tableCode Ra0992.cycles } 55157
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0993.table, code := 38359006855969046817751727489794969665,
        encodes := Ra0993.tableCode_eq ▸ encodesTable_tableCode Ra0993.cycles } 55158
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0994.table, code := 38359006855969046817751727491942453313,
        encodes := Ra0994.tableCode_eq ▸ encodesTable_tableCode Ra0994.cycles } 55159
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0995.table, code := 38358925726328214361880688183631679553,
        encodes := Ra0995.tableCode_eq ▸ encodesTable_tableCode Ra0995.cycles } 55162
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0996.table, code := 38358925726328214361880688185779163201,
        encodes := Ra0996.tableCode_eq ▸ encodesTable_tableCode Ra0996.cycles } 55163
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0997.table, code := 38359006855969046820129628157471100993,
        encodes := Ra0997.tableCode_eq ▸ encodesTable_tableCode Ra0997.cycles } 55164
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0998.table, code := 38359006855969046820129628159618584641,
        encodes := Ra0998.tableCode_eq ▸ encodesTable_tableCode Ra0998.cycles } 55165
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0999.table, code := 38359006855969046820201685824523472961,
        encodes := Ra0999.tableCode_eq ▸ encodesTable_tableCode Ra0999.cycles } 55166
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1000.table, code := 38359006855969046820201685826670956609,
        encodes := Ra1000.tableCode_eq ▸ encodesTable_tableCode Ra1000.cycles } 55167
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1001.table, code := 41015028960799453865674470356521586753,
        encodes := Ra1001.tableCode_eq ▸ encodesTable_tableCode Ra1001.cycles } 55246
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1002.table, code := 41015028960799453865674470358669070401,
        encodes := Ra1002.tableCode_eq ▸ encodesTable_tableCode Ra1002.cycles } 55247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1003.table, code := 41015191220153656693180847394711146561,
        encodes := Ra1003.tableCode_eq ▸ encodesTable_tableCode Ra1003.cycles } 55260
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1004.table, code := 41015191220153656693180847396858630209,
        encodes := Ra1004.tableCode_eq ▸ encodesTable_tableCode Ra1004.cycles } 55261
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1005.table, code := 41015191220153656693252905061763518529,
        encodes := Ra1005.tableCode_eq ▸ encodesTable_tableCode Ra1005.cycles } 55262
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1006.table, code := 41015191220153656693252905063911002177,
        encodes := Ra1006.tableCode_eq ▸ encodesTable_tableCode Ra1006.cycles } 55263
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1007.table, code := 41017706238946927423577963144335855681,
        encodes := Ra1007.tableCode_eq ▸ encodesTable_tableCode Ra1007.cycles } 55281
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1008.table, code := 41017706238946927423650020809240744001,
        encodes := Ra1008.tableCode_eq ▸ encodesTable_tableCode Ra1008.cycles } 55282
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1009.table, code := 41017706238946927423650020811388227649,
        encodes := Ra1009.tableCode_eq ▸ encodesTable_tableCode Ra1009.cycles } 55283
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1010.table, code := 41017787368587759881898960783080165441,
        encodes := Ra1010.tableCode_eq ▸ encodesTable_tableCode Ra1010.cycles } 55284
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1011.table, code := 41017787368587759881898960785227649089,
        encodes := Ra1011.tableCode_eq ▸ encodesTable_tableCode Ra1011.cycles } 55285
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1012.table, code := 41017787368587759881971018450132537409,
        encodes := Ra1012.tableCode_eq ▸ encodesTable_tableCode Ra1012.cycles } 55286
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1013.table, code := 41017787368587759881971018452280021057,
        encodes := Ra1013.tableCode_eq ▸ encodesTable_tableCode Ra1013.cycles } 55287
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1014.table, code := 41017706238946927426027921479064358977,
        encodes := Ra1014.tableCode_eq ▸ encodesTable_tableCode Ra1014.cycles } 55289
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1015.table, code := 41017706238946927426099979143969247297,
        encodes := Ra1015.tableCode_eq ▸ encodesTable_tableCode Ra1015.cycles } 55290
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1016.table, code := 41017706238946927426099979146116730945,
        encodes := Ra1016.tableCode_eq ▸ encodesTable_tableCode Ra1016.cycles } 55291
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1017.table, code := 41017787368587759884348919117808668737,
        encodes := Ra1017.tableCode_eq ▸ encodesTable_tableCode Ra1017.cycles } 55292
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1018.table, code := 41017787368587759884348919119956152385,
        encodes := Ra1018.tableCode_eq ▸ encodesTable_tableCode Ra1018.cycles } 55293
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1019.table, code := 41017787368587759884420976784861040705,
        encodes := Ra1019.tableCode_eq ▸ encodesTable_tableCode Ra1019.cycles } 55294
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1020.table, code := 41017787368587759884420976787008524353,
        encodes := Ra1020.tableCode_eq ▸ encodesTable_tableCode Ra1020.cycles } 55295
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1021.table, code := 40950287667718713635164212925942730817,
        encodes := Ra1021.tableCode_eq ▸ encodesTable_tableCode Ra1021.cycles } 55548
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1022.table, code := 40950287667718713635164212928090214465,
        encodes := Ra1022.tableCode_eq ▸ encodesTable_tableCode Ra1022.cycles } 55549
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1023.table, code := 40950287667718713635236270592995102785,
        encodes := Ra1023.tableCode_eq ▸ encodesTable_tableCode Ra1023.cycles } 55550
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1024.table, code := 40950287667718713635236270595142586433,
        encodes := Ra1024.tableCode_eq ▸ encodesTable_tableCode Ra1024.cycles } 55551
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (960 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (960 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (960 + i.val) 0 ≤ Data.profiles (960 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (960 + i.val) 0 = Data.canonicalMask (960 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (960 + i.val) < Data.canonicalMask (960 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (960 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models015
