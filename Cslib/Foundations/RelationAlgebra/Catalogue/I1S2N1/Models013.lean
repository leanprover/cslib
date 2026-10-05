/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0833
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0834
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0835
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0836
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0837
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0838
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0839
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0840
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0841
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0842
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0843
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0844
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0845
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0846
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0847
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0848
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0849
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0850
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0851
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0852
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0853
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0854
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0855
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0856
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0857
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0858
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0859
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0860
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0861
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0862
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0863
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0864
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0865
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0866
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0867
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0868
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0869
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0870
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0871
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0872
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0873
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0874
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0875
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0876
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0877
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0878
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0879
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0880
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0881
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0882
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0883
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0884
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0885
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0886
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0887
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0888
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0889
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0890
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0891
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0892
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0893
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0894
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0895
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0896

/-!
# Certified models 833–896 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models013

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0833.table, code := 35710529886074439333815434560321884225,
        encodes := Ra0833.tableCode_eq ▸ encodesTable_tableCode Ra0833.cycles } 53177
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0834.table, code := 35710529886074439333887492227374256193,
        encodes := Ra0834.tableCode_eq ▸ encodesTable_tableCode Ra0834.cycles } 53179
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0835.table, code := 35710611015715271792136432201213677633,
        encodes := Ra0835.tableCode_eq ▸ encodesTable_tableCode Ra0835.cycles } 53181
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0836.table, code := 35710611015715271792208489866118565953,
        encodes := Ra0836.tableCode_eq ▸ encodesTable_tableCode Ra0836.cycles } 53182
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0837.table, code := 35710611015715271792208489868266049601,
        encodes := Ra0837.tableCode_eq ▸ encodesTable_tableCode Ra0837.cycles } 53183
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0838.table, code := 35708663983616647968686273179794280513,
        encodes := Ra0838.tableCode_eq ▸ encodesTable_tableCode Ra0838.cycles } 53213
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0839.table, code := 35708663983616647968758330844699168833,
        encodes := Ra0839.tableCode_eq ▸ encodesTable_tableCode Ra0839.cycles } 53214
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0840.table, code := 35708663983616647968758330846846652481,
        encodes := Ra0840.tableCode_eq ▸ encodesTable_tableCode Ra0840.cycles } 53215
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0841.table, code := 35711179002409918699155446594323877953,
        encodes := Ra0841.tableCode_eq ▸ encodesTable_tableCode Ra0841.cycles } 53235
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0842.table, code := 35711260132050751157476444233068187713,
        encodes := Ra0842.tableCode_eq ▸ encodesTable_tableCode Ra0842.cycles } 53238
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0843.table, code := 35711260132050751157476444235215671361,
        encodes := Ra0843.tableCode_eq ▸ encodesTable_tableCode Ra0843.cycles } 53239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0844.table, code := 35711179002409918701533347262000009281,
        encodes := Ra0844.tableCode_eq ▸ encodesTable_tableCode Ra0844.cycles } 53241
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0845.table, code := 35711179002409918701605404929052381249,
        encodes := Ra0845.tableCode_eq ▸ encodesTable_tableCode Ra0845.cycles } 53243
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0846.table, code := 35711260132050751159854344902891802689,
        encodes := Ra0846.tableCode_eq ▸ encodesTable_tableCode Ra0846.cycles } 53245
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0847.table, code := 35711260132050751159926402567796691009,
        encodes := Ra0847.tableCode_eq ▸ encodesTable_tableCode Ra0847.cycles } 53246
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0848.table, code := 35711260132050751159926402569944174657,
        encodes := Ra0848.tableCode_eq ▸ encodesTable_tableCode Ra0848.cycles } 53247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0849.table, code := 40928869205492769633255597872506998849,
        encodes := Ra0849.tableCode_eq ▸ encodesTable_tableCode Ra0849.cycles } 53436
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0850.table, code := 40928869205492769633255597874654482497,
        encodes := Ra0850.tableCode_eq ▸ encodesTable_tableCode Ra0850.cycles } 53437
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0851.table, code := 40928869205492769633327655539559370817,
        encodes := Ra0851.tableCode_eq ▸ encodesTable_tableCode Ra0851.cycles } 53438
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0852.table, code := 40928869205492769633327655541706854465,
        encodes := Ra0852.tableCode_eq ▸ encodesTable_tableCode Ra0852.cycles } 53439
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0853.table, code := 40929518321828249000973510574185123905,
        encodes := Ra0853.tableCode_eq ▸ encodesTable_tableCode Ra0853.cycles } 53500
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0854.table, code := 40929518321828249000973510576332607553,
        encodes := Ra0854.tableCode_eq ▸ encodesTable_tableCode Ra0854.cycles } 53501
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0855.table, code := 40929518321828249001045568241237495873,
        encodes := Ra0855.tableCode_eq ▸ encodesTable_tableCode Ra0855.cycles } 53502
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0856.table, code := 40929518321828249001045568243384979521,
        encodes := Ra0856.tableCode_eq ▸ encodesTable_tableCode Ra0856.cycles } 53503
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0857.table, code := 38350975021526626108300683469234901057,
        encodes := Ra0857.tableCode_eq ▸ encodesTable_tableCode Ra0857.cycles } 53576
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0858.table, code := 38350975021526626108300683471382384705,
        encodes := Ra0858.tableCode_eq ▸ encodesTable_tableCode Ra0858.cycles } 53577
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0859.table, code := 41009755534145339170142073761896337473,
        encodes := Ra0859.tableCode_eq ▸ encodesTable_tableCode Ra0859.cycles } 53698
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0860.table, code := 41009755534145339170142073764043821121,
        encodes := Ra0860.tableCode_eq ▸ encodesTable_tableCode Ra0860.cycles } 53699
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0861.table, code := 41009836663786171628463071402788130881,
        encodes := Ra0861.tableCode_eq ▸ encodesTable_tableCode Ra0861.cycles } 53702
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0862.table, code := 41009836663786171628463071404935614529,
        encodes := Ra0862.tableCode_eq ▸ encodesTable_tableCode Ra0862.cycles } 53703
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0863.table, code := 41012595071574477649587478498803716161,
        encodes := Ra0863.tableCode_eq ▸ encodesTable_tableCode Ra0863.cycles } 53756
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0864.table, code := 41012595071574477649587478500951199809,
        encodes := Ra0864.tableCode_eq ▸ encodesTable_tableCode Ra0864.cycles } 53757
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0865.table, code := 41012595071574477649659536165856088129,
        encodes := Ra0865.tableCode_eq ▸ encodesTable_tableCode Ra0865.cycles } 53758
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0866.table, code := 41012595071574477649659536168003571777,
        encodes := Ra0866.tableCode_eq ▸ encodesTable_tableCode Ra0866.cycles } 53759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0867.table, code := 40928869205492769635417325556205883457,
        encodes := Ra0867.tableCode_eq ▸ encodesTable_tableCode Ra0867.cycles } 53940
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0868.table, code := 40928869205492769635417325558353367105,
        encodes := Ra0868.tableCode_eq ▸ encodesTable_tableCode Ra0868.cycles } 53941
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0869.table, code := 40928869205492769635489383223258255425,
        encodes := Ra0869.tableCode_eq ▸ encodesTable_tableCode Ra0869.cycles } 53942
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0870.table, code := 40928869205492769635489383225405739073,
        encodes := Ra0870.tableCode_eq ▸ encodesTable_tableCode Ra0870.cycles } 53943
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0871.table, code := 40928869205492769637867283890934386753,
        encodes := Ra0871.tableCode_eq ▸ encodesTable_tableCode Ra0871.cycles } 53948
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0872.table, code := 40928869205492769637867283893081870401,
        encodes := Ra0872.tableCode_eq ▸ encodesTable_tableCode Ra0872.cycles } 53949
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0873.table, code := 40928869205492769637939341557986758721,
        encodes := Ra0873.tableCode_eq ▸ encodesTable_tableCode Ra0873.cycles } 53950
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0874.table, code := 40928869205492769637939341560134242369,
        encodes := Ra0874.tableCode_eq ▸ encodesTable_tableCode Ra0874.cycles } 53951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0875.table, code := 40929518321828249003135238257884008513,
        encodes := Ra0875.tableCode_eq ▸ encodesTable_tableCode Ra0875.cycles } 54004
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0876.table, code := 40929518321828249003135238260031492161,
        encodes := Ra0876.tableCode_eq ▸ encodesTable_tableCode Ra0876.cycles } 54005
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0877.table, code := 40929518321828249003207295924936380481,
        encodes := Ra0877.tableCode_eq ▸ encodesTable_tableCode Ra0877.cycles } 54006
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0878.table, code := 40929518321828249003207295927083864129,
        encodes := Ra0878.tableCode_eq ▸ encodesTable_tableCode Ra0878.cycles } 54007
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0879.table, code := 40929518321828249005585196592612511809,
        encodes := Ra0879.tableCode_eq ▸ encodesTable_tableCode Ra0879.cycles } 54012
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0880.table, code := 40929518321828249005585196594759995457,
        encodes := Ra0880.tableCode_eq ▸ encodesTable_tableCode Ra0880.cycles } 54013
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0881.table, code := 40929518321828249005657254259664883777,
        encodes := Ra0881.tableCode_eq ▸ encodesTable_tableCode Ra0881.cycles } 54014
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0882.table, code := 40929518321828249005657254261812367425,
        encodes := Ra0882.tableCode_eq ▸ encodesTable_tableCode Ra0882.cycles } 54015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0883.table, code := 38353814558955764587529915222165033025,
        encodes := Ra0883.tableCode_eq ▸ encodesTable_tableCode Ra0883.cycles } 54132
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0884.table, code := 38353814558955764587529915224312516673,
        encodes := Ra0884.tableCode_eq ▸ encodesTable_tableCode Ra0884.cycles } 54133
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0885.table, code := 38353814558955764587601972889217404993,
        encodes := Ra0885.tableCode_eq ▸ encodesTable_tableCode Ra0885.cycles } 54134
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0886.table, code := 38353814558955764587601972891364888641,
        encodes := Ra0886.tableCode_eq ▸ encodesTable_tableCode Ra0886.cycles } 54135
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0887.table, code := 38353814558955764589979873556893536321,
        encodes := Ra0887.tableCode_eq ▸ encodesTable_tableCode Ra0887.cycles } 54140
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0888.table, code := 38353814558955764589979873559041019969,
        encodes := Ra0888.tableCode_eq ▸ encodesTable_tableCode Ra0888.cycles } 54141
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0889.table, code := 38353814558955764590051931223945908289,
        encodes := Ra0889.tableCode_eq ▸ encodesTable_tableCode Ra0889.cycles } 54142
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0890.table, code := 38353814558955764590051931226093391937,
        encodes := Ra0890.tableCode_eq ▸ encodesTable_tableCode Ra0890.cycles } 54143
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0891.table, code := 41012513941933645193428208543758291009,
        encodes := Ra0891.tableCode_eq ▸ encodesTable_tableCode Ra0891.cycles } 54257
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0892.table, code := 41012513941933645193500266210810662977,
        encodes := Ra0892.tableCode_eq ▸ encodesTable_tableCode Ra0892.cycles } 54259
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0893.table, code := 41012595071574477651749206182502600769,
        encodes := Ra0893.tableCode_eq ▸ encodesTable_tableCode Ra0893.cycles } 54260
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0894.table, code := 41012595071574477651749206184650084417,
        encodes := Ra0894.tableCode_eq ▸ encodesTable_tableCode Ra0894.cycles } 54261
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0895.table, code := 41012595071574477651821263849554972737,
        encodes := Ra0895.tableCode_eq ▸ encodesTable_tableCode Ra0895.cycles } 54262
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0896.table, code := 41012595071574477651821263851702456385,
        encodes := Ra0896.tableCode_eq ▸ encodesTable_tableCode Ra0896.cycles } 54263
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (832 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (832 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (832 + i.val) 0 ≤ Data.profiles (832 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (832 + i.val) 0 = Data.canonicalMask (832 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (832 + i.val) < Data.canonicalMask (832 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (832 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models013
