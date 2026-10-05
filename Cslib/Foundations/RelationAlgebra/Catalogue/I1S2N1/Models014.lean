/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0897
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0898
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0899
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0900
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0901
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0902
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0903
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0904
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0905
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0906
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0907
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0908
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0909
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0910
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0911
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0912
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0913
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0914
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0915
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0916
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0917
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0918
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0919
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0920
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0921
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0922
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0923
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0924
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0925
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0926
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0927
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0928
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0929
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0930
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0931
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0932
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0933
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0934
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0935
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0936
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0937
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0938
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0939
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0940
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0941
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0942
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0943
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0944
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0945
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0946
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0947
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0948
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0949
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0950
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0951
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0952
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0953
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0954
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0955
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0956
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0957
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0958
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0959
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0960

/-!
# Certified models 897–960 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models014

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0897.table, code := 41012513941933645195878166878486794305,
        encodes := Ra0897.tableCode_eq ▸ encodesTable_tableCode Ra0897.cycles } 54265
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0898.table, code := 41012513941933645195950224545539166273,
        encodes := Ra0898.tableCode_eq ▸ encodesTable_tableCode Ra0898.cycles } 54267
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0899.table, code := 41012595071574477654199164517231104065,
        encodes := Ra0899.tableCode_eq ▸ encodesTable_tableCode Ra0899.cycles } 54268
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0900.table, code := 41012595071574477654199164519378587713,
        encodes := Ra0900.tableCode_eq ▸ encodesTable_tableCode Ra0900.cycles } 54269
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0901.table, code := 41012595071574477654271222184283476033,
        encodes := Ra0901.tableCode_eq ▸ encodesTable_tableCode Ra0901.cycles } 54270
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0902.table, code := 41012595071574477654271222186430959681,
        encodes := Ra0902.tableCode_eq ▸ encodesTable_tableCode Ra0902.cycles } 54271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0903.table, code := 40934061502506051860955394138356060225,
        encodes := Ra0903.tableCode_eq ▸ encodesTable_tableCode Ra0903.cycles } 54452
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0904.table, code := 40934061502506051860955394140503543873,
        encodes := Ra0904.tableCode_eq ▸ encodesTable_tableCode Ra0904.cycles } 54453
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0905.table, code := 40934061502506051861027451805408432193,
        encodes := Ra0905.tableCode_eq ▸ encodesTable_tableCode Ra0905.cycles } 54454
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0906.table, code := 40934061502506051861027451807555915841,
        encodes := Ra0906.tableCode_eq ▸ encodesTable_tableCode Ra0906.cycles } 54455
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0907.table, code := 40934061502506051863405352475232047169,
        encodes := Ra0907.tableCode_eq ▸ encodesTable_tableCode Ra0907.cycles } 54461
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0908.table, code := 40934061502506051863477410140136935489,
        encodes := Ra0908.tableCode_eq ▸ encodesTable_tableCode Ra0908.cycles } 54462
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0909.table, code := 40934061502506051863477410142284419137,
        encodes := Ra0909.tableCode_eq ▸ encodesTable_tableCode Ra0909.cycles } 54463
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0910.table, code := 40934548359487328403544830469520756801,
        encodes := Ra0910.tableCode_eq ▸ encodesTable_tableCode Ra0910.cycles } 54508
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0911.table, code := 40934548359487328403544830471668240449,
        encodes := Ra0911.tableCode_eq ▸ encodesTable_tableCode Ra0911.cycles } 54509
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0912.table, code := 40934548359487328403616888136573128769,
        encodes := Ra0912.tableCode_eq ▸ encodesTable_tableCode Ra0912.cycles } 54510
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0913.table, code := 40934548359487328403616888138720612417,
        encodes := Ra0913.tableCode_eq ▸ encodesTable_tableCode Ra0913.cycles } 54511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0914.table, code := 40934629489200698770352309201289875521,
        encodes := Ra0914.tableCode_eq ▸ encodesTable_tableCode Ra0914.cycles } 54513
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0915.table, code := 40934629489200698770424366866194763841,
        encodes := Ra0915.tableCode_eq ▸ encodesTable_tableCode Ra0915.cycles } 54514
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0916.table, code := 40934629489200698770424366868342247489,
        encodes := Ra0916.tableCode_eq ▸ encodesTable_tableCode Ra0916.cycles } 54515
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0917.table, code := 40934710618841531228673306840034185281,
        encodes := Ra0917.tableCode_eq ▸ encodesTable_tableCode Ra0917.cycles } 54516
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0918.table, code := 40934710618841531228673306842181668929,
        encodes := Ra0918.tableCode_eq ▸ encodesTable_tableCode Ra0918.cycles } 54517
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0919.table, code := 40934710618841531228745364507086557249,
        encodes := Ra0919.tableCode_eq ▸ encodesTable_tableCode Ra0919.cycles } 54518
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0920.table, code := 40934710618841531228745364509234040897,
        encodes := Ra0920.tableCode_eq ▸ encodesTable_tableCode Ra0920.cycles } 54519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0921.table, code := 40934629489200698772802267536018378817,
        encodes := Ra0921.tableCode_eq ▸ encodesTable_tableCode Ra0921.cycles } 54521
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0922.table, code := 40934629489200698772874325200923267137,
        encodes := Ra0922.tableCode_eq ▸ encodesTable_tableCode Ra0922.cycles } 54522
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0923.table, code := 40934629489200698772874325203070750785,
        encodes := Ra0923.tableCode_eq ▸ encodesTable_tableCode Ra0923.cycles } 54523
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0924.table, code := 40934710618841531231123265174762688577,
        encodes := Ra0924.tableCode_eq ▸ encodesTable_tableCode Ra0924.cycles } 54524
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0925.table, code := 40934710618841531231123265176910172225,
        encodes := Ra0925.tableCode_eq ▸ encodesTable_tableCode Ra0925.cycles } 54525
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0926.table, code := 40934710618841531231195322841815060545,
        encodes := Ra0926.tableCode_eq ▸ encodesTable_tableCode Ra0926.cycles } 54526
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0927.table, code := 40934710618841531231195322843962544193,
        encodes := Ra0927.tableCode_eq ▸ encodesTable_tableCode Ra0927.cycles } 54527
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0928.table, code := 38356167318539908338450438069812465729,
        encodes := Ra0928.tableCode_eq ▸ encodesTable_tableCode Ra0928.cycles } 54600
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0929.table, code := 38356167318539908338450438071959949377,
        encodes := Ra0929.tableCode_eq ▸ encodesTable_tableCode Ra0929.cycles } 54601
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0930.table, code := 38356410707534943624421928082998562881,
        encodes := Ra0930.tableCode_eq ▸ encodesTable_tableCode Ra0930.cycles } 54622
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0931.table, code := 38356410707534943624421928085146046529,
        encodes := Ra0931.tableCode_eq ▸ encodesTable_tableCode Ra0931.cycles } 54623
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0932.table, code := 38358925726328214354819043830475788353,
        encodes := Ra0932.tableCode_eq ▸ encodesTable_tableCode Ra0932.cycles } 54642
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0933.table, code := 38358925726328214354819043832623272001,
        encodes := Ra0933.tableCode_eq ▸ encodesTable_tableCode Ra0933.cycles } 54643
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0934.table, code := 38359006855969046813067983804315209793,
        encodes := Ra0934.tableCode_eq ▸ encodesTable_tableCode Ra0934.cycles } 54644
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0935.table, code := 38359006855969046813067983806462693441,
        encodes := Ra0935.tableCode_eq ▸ encodesTable_tableCode Ra0935.cycles } 54645
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0936.table, code := 38359006855969046813140041471367581761,
        encodes := Ra0936.tableCode_eq ▸ encodesTable_tableCode Ra0936.cycles } 54646
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0937.table, code := 38359006855969046813140041473515065409,
        encodes := Ra0937.tableCode_eq ▸ encodesTable_tableCode Ra0937.cycles } 54647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0938.table, code := 38358925726328214357269002165204291649,
        encodes := Ra0938.tableCode_eq ▸ encodesTable_tableCode Ra0938.cycles } 54650
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0939.table, code := 38358925726328214357269002167351775297,
        encodes := Ra0939.tableCode_eq ▸ encodesTable_tableCode Ra0939.cycles } 54651
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0940.table, code := 38359006855969046815517942139043713089,
        encodes := Ra0940.tableCode_eq ▸ encodesTable_tableCode Ra0940.cycles } 54652
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0941.table, code := 38359006855969046815517942141191196737,
        encodes := Ra0941.tableCode_eq ▸ encodesTable_tableCode Ra0941.cycles } 54653
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0942.table, code := 38359006855969046815589999806096085057,
        encodes := Ra0942.tableCode_eq ▸ encodesTable_tableCode Ra0942.cycles } 54654
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0943.table, code := 38359006855969046815589999808243568705,
        encodes := Ra0943.tableCode_eq ▸ encodesTable_tableCode Ra0943.cycles } 54655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0944.table, code := 41015028960799453861062784338094198849,
        encodes := Ra0944.tableCode_eq ▸ encodesTable_tableCode Ra0944.cycles } 54734
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0945.table, code := 41015028960799453861062784340241682497,
        encodes := Ra0945.tableCode_eq ▸ encodesTable_tableCode Ra0945.cycles } 54735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0946.table, code := 41015191220153656688569161376283758657,
        encodes := Ra0946.tableCode_eq ▸ encodesTable_tableCode Ra0946.cycles } 54748
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0947.table, code := 41015191220153656688569161378431242305,
        encodes := Ra0947.tableCode_eq ▸ encodesTable_tableCode Ra0947.cycles } 54749
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0948.table, code := 41015191220153656688641219043336130625,
        encodes := Ra0948.tableCode_eq ▸ encodesTable_tableCode Ra0948.cycles } 54750
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0949.table, code := 41015191220153656688641219045483614273,
        encodes := Ra0949.tableCode_eq ▸ encodesTable_tableCode Ra0949.cycles } 54751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0950.table, code := 41017706238946927418966277125908467777,
        encodes := Ra0950.tableCode_eq ▸ encodesTable_tableCode Ra0950.cycles } 54769
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0951.table, code := 41017706238946927419038334790813356097,
        encodes := Ra0951.tableCode_eq ▸ encodesTable_tableCode Ra0951.cycles } 54770
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0952.table, code := 41017706238946927419038334792960839745,
        encodes := Ra0952.tableCode_eq ▸ encodesTable_tableCode Ra0952.cycles } 54771
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0953.table, code := 41017787368587759877287274764652777537,
        encodes := Ra0953.tableCode_eq ▸ encodesTable_tableCode Ra0953.cycles } 54772
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0954.table, code := 41017787368587759877287274766800261185,
        encodes := Ra0954.tableCode_eq ▸ encodesTable_tableCode Ra0954.cycles } 54773
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0955.table, code := 41017787368587759877359332431705149505,
        encodes := Ra0955.tableCode_eq ▸ encodesTable_tableCode Ra0955.cycles } 54774
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0956.table, code := 41017787368587759877359332433852633153,
        encodes := Ra0956.tableCode_eq ▸ encodesTable_tableCode Ra0956.cycles } 54775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0957.table, code := 41017706238946927421416235460636971073,
        encodes := Ra0957.tableCode_eq ▸ encodesTable_tableCode Ra0957.cycles } 54777
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0958.table, code := 41017706238946927421488293125541859393,
        encodes := Ra0958.tableCode_eq ▸ encodesTable_tableCode Ra0958.cycles } 54778
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0959.table, code := 41017706238946927421488293127689343041,
        encodes := Ra0959.tableCode_eq ▸ encodesTable_tableCode Ra0959.cycles } 54779
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0960.table, code := 41017787368587759879737233099381280833,
        encodes := Ra0960.tableCode_eq ▸ encodesTable_tableCode Ra0960.cycles } 54780
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (896 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (896 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (896 + i.val) 0 ≤ Data.profiles (896 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (896 + i.val) 0 = Data.canonicalMask (896 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (896 + i.val) < Data.canonicalMask (896 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (896 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models014
