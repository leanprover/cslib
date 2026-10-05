/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0961
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0962
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0963
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0964
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0965
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0966
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0967
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0968
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0969
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0970
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0971
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0972
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0973
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0974
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0975
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0976
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0977
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0978
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0979
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0980
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0981
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0982
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0983
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0984
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0985
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0986
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0987
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0988
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0989
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0990
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0991
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0992
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0993
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0994
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0995
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0996
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0997
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0998
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0999
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1000
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1001
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1002
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1003
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1004
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1005
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1006
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1007
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1008
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1009
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1010
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1011
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1012
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1013
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1014
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1015
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1016
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1017
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1018
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1019
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1020
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1021
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1022
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1023
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1024

/-!
# Certified models 961–1024 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models015

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0961.table, code := 4505230735590242784457024807247286337,
        encodes := Ra0961.tableCode_eq ▸ encodesTable_tableCode Ra0961.cycles } 161391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0962.table, code := 4505149605951828180225216964899115073,
        encodes := Ra0962.tableCode_eq ▸ encodesTable_tableCode Ra0962.cycles } 161398
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0963.table, code := 4505149605951828180225216967046598721,
        encodes := Ra0963.tableCode_eq ▸ encodesTable_tableCode Ra0963.cycles } 161399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0964.table, code := 4505230735590242786906983139828305985,
        encodes := Ra0964.tableCode_eq ▸ encodesTable_tableCode Ra0964.cycles } 161406
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0965.table, code := 4505230735590242786906983141975789633,
        encodes := Ra0965.tableCode_eq ▸ encodesTable_tableCode Ra0965.cycles } 161407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0966.table, code := 4502391200728862824704113912775446593,
        encodes := Ra0966.tableCode_eq ▸ encodesTable_tableCode Ra0966.cycles } 161457
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0967.table, code := 4502472330367277431385880085557153857,
        encodes := Ra0967.tableCode_eq ▸ encodesTable_tableCode Ra0967.cycles } 161464
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0968.table, code := 4502472330367277431385880087704637505,
        encodes := Ra0968.tableCode_eq ▸ encodesTable_tableCode Ra0968.cycles } 161465
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0969.table, code := 4505149608437379662902945009459531841,
        encodes := Ra0969.tableCode_eq ▸ encodesTable_tableCode Ra0969.cycles } 161510
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0970.table, code := 4505149608437379662902945011607015489,
        encodes := Ra0970.tableCode_eq ▸ encodesTable_tableCode Ra0970.cycles } 161511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0971.table, code := 4505230738075794269584711184388722753,
        encodes := Ra0971.tableCode_eq ▸ encodesTable_tableCode Ra0971.cycles } 161518
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0972.table, code := 4505230738075794269584711186536206401,
        encodes := Ra0972.tableCode_eq ▸ encodesTable_tableCode Ra0972.cycles } 161519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0973.table, code := 4505149608437379665352903344188035137,
        encodes := Ra0973.tableCode_eq ▸ encodesTable_tableCode Ra0973.cycles } 161526
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0974.table, code := 4505149608437379665352903346335518785,
        encodes := Ra0974.tableCode_eq ▸ encodesTable_tableCode Ra0974.cycles } 161527
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0975.table, code := 4505230738075794272034669519117226049,
        encodes := Ra0975.tableCode_eq ▸ encodesTable_tableCode Ra0975.cycles } 161534
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0976.table, code := 4505230738075794272034669521264709697,
        encodes := Ra0976.tableCode_eq ▸ encodesTable_tableCode Ra0976.cycles } 161535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0977.table, code := 4585792545783450187449458489144119361,
        encodes := Ra0977.tableCode_eq ▸ encodesTable_tableCode Ra0977.cycles } 161590
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0978.table, code := 4585792545783450187449458491291603009,
        encodes := Ra0978.tableCode_eq ▸ encodesTable_tableCode Ra0978.cycles } 161591
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0979.table, code := 4585873675421864794131224664073310273,
        encodes := Ra0979.tableCode_eq ▸ encodesTable_tableCode Ra0979.cycles } 161598
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0980.table, code := 4585873675421864794131224666220793921,
        encodes := Ra0980.tableCode_eq ▸ encodesTable_tableCode Ra0980.cycles } 161599
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0981.table, code := 4588550953489549173937000454960713793,
        encodes := Ra0981.tableCode_eq ▸ encodesTable_tableCode Ra0981.cycles } 161638
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0982.table, code := 4588550953489549173937000457108197441,
        encodes := Ra0982.tableCode_eq ▸ encodesTable_tableCode Ra0982.cycles } 161639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0983.table, code := 4588632083127963780618766629889904705,
        encodes := Ra0983.tableCode_eq ▸ encodesTable_tableCode Ra0983.cycles } 161646
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0984.table, code := 4588632083127963780618766632037388353,
        encodes := Ra0984.tableCode_eq ▸ encodesTable_tableCode Ra0984.cycles } 161647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0985.table, code := 4588550953489549176386958789689217089,
        encodes := Ra0985.tableCode_eq ▸ encodesTable_tableCode Ra0985.cycles } 161654
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0986.table, code := 4588550953489549176386958791836700737,
        encodes := Ra0986.tableCode_eq ▸ encodesTable_tableCode Ra0986.cycles } 161655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0987.table, code := 4588632083127963783068724964618408001,
        encodes := Ra0987.tableCode_eq ▸ encodesTable_tableCode Ra0987.cycles } 161662
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0988.table, code := 4588632083127963783068724966765891649,
        encodes := Ra0988.tableCode_eq ▸ encodesTable_tableCode Ra0988.cycles } 161663
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0989.table, code := 4585792548269001670127186533704536129,
        encodes := Ra0989.tableCode_eq ▸ encodesTable_tableCode Ra0989.cycles } 161702
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0990.table, code := 4585792548269001670127186535852019777,
        encodes := Ra0990.tableCode_eq ▸ encodesTable_tableCode Ra0990.cycles } 161703
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0991.table, code := 4585873677907416276808952708633727041,
        encodes := Ra0991.tableCode_eq ▸ encodesTable_tableCode Ra0991.cycles } 161710
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0992.table, code := 4585873677907416276808952710781210689,
        encodes := Ra0992.tableCode_eq ▸ encodesTable_tableCode Ra0992.cycles } 161711
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0993.table, code := 4585792548269001672577144868433039425,
        encodes := Ra0993.tableCode_eq ▸ encodesTable_tableCode Ra0993.cycles } 161718
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0994.table, code := 4585792548269001672577144870580523073,
        encodes := Ra0994.tableCode_eq ▸ encodesTable_tableCode Ra0994.cycles } 161719
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0995.table, code := 4585873677907416279258911043362230337,
        encodes := Ra0995.tableCode_eq ▸ encodesTable_tableCode Ra0995.cycles } 161726
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0996.table, code := 4585873677907416279258911045509713985,
        encodes := Ra0996.tableCode_eq ▸ encodesTable_tableCode Ra0996.cycles } 161727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0997.table, code := 4588550955975100659064686834249633857,
        encodes := Ra0997.tableCode_eq ▸ encodesTable_tableCode Ra0997.cycles } 161766
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0998.table, code := 4588550955975100659064686836397117505,
        encodes := Ra0998.tableCode_eq ▸ encodesTable_tableCode Ra0998.cycles } 161767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0999.table, code := 4588632085613515265746453009178824769,
        encodes := Ra0999.tableCode_eq ▸ encodesTable_tableCode Ra0999.cycles } 161774
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1000.table, code := 4588632085613515265746453011326308417,
        encodes := Ra1000.tableCode_eq ▸ encodesTable_tableCode Ra1000.cycles } 161775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1001.table, code := 4588550955975100661514645168978137153,
        encodes := Ra1001.tableCode_eq ▸ encodesTable_tableCode Ra1001.cycles } 161782
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1002.table, code := 4588550955975100661514645171125620801,
        encodes := Ra1002.tableCode_eq ▸ encodesTable_tableCode Ra1002.cycles } 161783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1003.table, code := 4588632085613515268196411343907328065,
        encodes := Ra1003.tableCode_eq ▸ encodesTable_tableCode Ra1003.cycles } 161790
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1004.table, code := 4588632085613515268196411346054811713,
        encodes := Ra1004.tableCode_eq ▸ encodesTable_tableCode Ra1004.cycles } 161791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1005.table, code := 4505149606106570837321528107365306433,
        encodes := Ra1005.tableCode_eq ▸ encodesTable_tableCode Ra1005.cycles } 162422
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1006.table, code := 4505149606106570837321528109512790081,
        encodes := Ra1006.tableCode_eq ▸ encodesTable_tableCode Ra1006.cycles } 162423
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1007.table, code := 4505230735744985444003294282294497345,
        encodes := Ra1007.tableCode_eq ▸ encodesTable_tableCode Ra1007.cycles } 162430
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1008.table, code := 4505230735744985444003294284441980993,
        encodes := Ra1008.tableCode_eq ▸ encodesTable_tableCode Ra1008.cycles } 162431
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1009.table, code := 4502391200883605481800425055241637953,
        encodes := Ra1009.tableCode_eq ▸ encodesTable_tableCode Ra1009.cycles } 162481
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1010.table, code := 4502472330522020088482191228023345217,
        encodes := Ra1010.tableCode_eq ▸ encodesTable_tableCode Ra1010.cycles } 162488
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1011.table, code := 4502472330522020088482191230170828865,
        encodes := Ra1011.tableCode_eq ▸ encodesTable_tableCode Ra1011.cycles } 162489
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1012.table, code := 4505149608592122319999256151925723201,
        encodes := Ra1012.tableCode_eq ▸ encodesTable_tableCode Ra1012.cycles } 162534
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1013.table, code := 4505149608592122319999256154073206849,
        encodes := Ra1013.tableCode_eq ▸ encodesTable_tableCode Ra1013.cycles } 162535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1014.table, code := 4505230738230536926681022326854914113,
        encodes := Ra1014.tableCode_eq ▸ encodesTable_tableCode Ra1014.cycles } 162542
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1015.table, code := 4505230738230536926681022329002397761,
        encodes := Ra1015.tableCode_eq ▸ encodesTable_tableCode Ra1015.cycles } 162543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1016.table, code := 4505149608592122322449214486654226497,
        encodes := Ra1016.tableCode_eq ▸ encodesTable_tableCode Ra1016.cycles } 162550
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1017.table, code := 4505149608592122322449214488801710145,
        encodes := Ra1017.tableCode_eq ▸ encodesTable_tableCode Ra1017.cycles } 162551
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1018.table, code := 4505230738230536929130980661583417409,
        encodes := Ra1018.tableCode_eq ▸ encodesTable_tableCode Ra1018.cycles } 162558
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1019.table, code := 4505230738230536929130980663730901057,
        encodes := Ra1019.tableCode_eq ▸ encodesTable_tableCode Ra1019.cycles } 162559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1020.table, code := 4588550953644291831033311597426905153,
        encodes := Ra1020.tableCode_eq ▸ encodesTable_tableCode Ra1020.cycles } 162662
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1021.table, code := 4588550953644291831033311599574388801,
        encodes := Ra1021.tableCode_eq ▸ encodesTable_tableCode Ra1021.cycles } 162663
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1022.table, code := 4588632083282706437715077772356096065,
        encodes := Ra1022.tableCode_eq ▸ encodesTable_tableCode Ra1022.cycles } 162670
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1023.table, code := 4588632083282706437715077774503579713,
        encodes := Ra1023.tableCode_eq ▸ encodesTable_tableCode Ra1023.cycles } 162671
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1024.table, code := 4588550953644291833483269932155408449,
        encodes := Ra1024.tableCode_eq ▸ encodesTable_tableCode Ra1024.cycles } 162678
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (960 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (960 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
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

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models015
