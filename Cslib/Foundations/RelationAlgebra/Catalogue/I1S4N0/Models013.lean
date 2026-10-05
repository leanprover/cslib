/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0833
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0834
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0835
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0836
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0837
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0838
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0839
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0840
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0841
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0842
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0843
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0844
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0845
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0846
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0847
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0848
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0849
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0850
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0851
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0852
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0853
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0854
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0855
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0856
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0857
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0858
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0859
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0860
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0861
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0862
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0863
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0864
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0865
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0866
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0867
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0868
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0869
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0870
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0871
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0872
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0873
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0874
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0875
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0876
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0877
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0878
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0879
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0880
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0881
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0882
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0883
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0884
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0885
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0886
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0887
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0888
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0889
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0890
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0891
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0892
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0893
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0894
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0895
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0896

/-!
# Certified models 833–896 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models013

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0833.table, code := 1666829044318136806773283552965693505,
        encodes := Ra0833.tableCode_eq ▸ encodesTable_tableCode Ra0833.cycles } 138411
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0834.table, code := 1666829044320554658412515016780812353,
        encodes := Ra0834.tableCode_eq ▸ encodesTable_tableCode Ra0834.cycles } 138414
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0835.table, code := 1666829044320554658412515018928296001,
        encodes := Ra0835.tableCode_eq ▸ encodesTable_tableCode Ra0835.cycles } 138415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0836.table, code := 1666829044318136809223241887694196801,
        encodes := Ra0836.tableCode_eq ▸ encodesTable_tableCode Ra0836.cycles } 138427
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0837.table, code := 1666829044320554660862473351509315649,
        encodes := Ra0837.tableCode_eq ▸ encodesTable_tableCode Ra0837.cycles } 138430
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0838.table, code := 1666829044320554660862473353656799297,
        encodes := Ra0838.tableCode_eq ▸ encodesTable_tableCode Ra0838.cycles } 138431
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0839.table, code := 4325852943274663771922155300473540673,
        encodes := Ra0839.tableCode_eq ▸ encodesTable_tableCode Ra0839.cycles } 138897
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0840.table, code := 4325934072913078378603921473255247937,
        encodes := Ra0840.tableCode_eq ▸ encodesTable_tableCode Ra0840.cycles } 138904
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0841.table, code := 4325934072913078378603921475402731585,
        encodes := Ra0841.tableCode_eq ▸ encodesTable_tableCode Ra0841.cycles } 138905
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0842.table, code := 4409254288329251134595442209789841473,
        encodes := Ra0842.tableCode_eq ▸ encodesTable_tableCode Ra0842.cycles } 139028
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0843.table, code := 4409254288329251134595442211937325121,
        encodes := Ra0843.tableCode_eq ▸ encodesTable_tableCode Ra0843.cycles } 139029
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0844.table, code := 4409335417967665741277208384719032385,
        encodes := Ra0844.tableCode_eq ▸ encodesTable_tableCode Ra0844.cycles } 139036
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0845.table, code := 4409335417967665741277208386866516033,
        encodes := Ra0845.tableCode_eq ▸ encodesTable_tableCode Ra0845.cycles } 139037
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0846.table, code := 4409254290814802619723128591226245185,
        encodes := Ra0846.tableCode_eq ▸ encodesTable_tableCode Ra0846.cycles } 139157
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0847.table, code := 4409335420453217226404894764007952449,
        encodes := Ra0847.tableCode_eq ▸ encodesTable_tableCode Ra0847.cycles } 139164
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0848.table, code := 4409335420453217226404894766155436097,
        encodes := Ra0848.tableCode_eq ▸ encodesTable_tableCode Ra0848.cycles } 139165
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0849.table, code := 4412012698603108636091734349742084161,
        encodes := Ra0849.tableCode_eq ▸ encodesTable_tableCode Ra0849.cycles } 139238
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0850.table, code := 4412012698603108636091734351889567809,
        encodes := Ra0850.tableCode_eq ▸ encodesTable_tableCode Ra0850.cycles } 139239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0851.table, code := 4412093828241523242773500524671275073,
        encodes := Ra0851.tableCode_eq ▸ encodesTable_tableCode Ra0851.cycles } 139246
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0852.table, code := 4412093828241523242773500526818758721,
        encodes := Ra0852.tableCode_eq ▸ encodesTable_tableCode Ra0852.cycles } 139247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0853.table, code := 4412012698603108638541692684470587457,
        encodes := Ra0853.tableCode_eq ▸ encodesTable_tableCode Ra0853.cycles } 139254
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0854.table, code := 4412012698603108638541692686618071105,
        encodes := Ra0854.tableCode_eq ▸ encodesTable_tableCode Ra0854.cycles } 139255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0855.table, code := 4412093828241523245223458859399778369,
        encodes := Ra0855.tableCode_eq ▸ encodesTable_tableCode Ra0855.cycles } 139262
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0856.table, code := 4412093828241523245223458861547262017,
        encodes := Ra0856.tableCode_eq ▸ encodesTable_tableCode Ra0856.cycles } 139263
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0857.table, code := 1666829049342432577367051611951861825,
        encodes := Ra0857.tableCode_eq ▸ encodesTable_tableCode Ra0857.cycles } 144523
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0858.table, code := 1666829049344850429006283075766980673,
        encodes := Ra0858.tableCode_eq ▸ encodesTable_tableCode Ra0858.cycles } 144526
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0859.table, code := 1666829049344850429006283077914464321,
        encodes := Ra0859.tableCode_eq ▸ encodesTable_tableCode Ra0859.cycles } 144527
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0860.table, code := 1666829049342432579817009946680365121,
        encodes := Ra0860.tableCode_eq ▸ encodesTable_tableCode Ra0860.cycles } 144539
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0861.table, code := 1666829049424639607176057739746218049,
        encodes := Ra0861.tableCode_eq ▸ encodesTable_tableCode Ra0861.cycles } 144555
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0862.table, code := 1666829049427057458815289203561336897,
        encodes := Ra0862.tableCode_eq ▸ encodesTable_tableCode Ra0862.cycles } 144558
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0863.table, code := 1666829049427057458815289205708820545,
        encodes := Ra0863.tableCode_eq ▸ encodesTable_tableCode Ra0863.cycles } 144559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0864.table, code := 1666829049424639609626016074474721345,
        encodes := Ra0864.tableCode_eq ▸ encodesTable_tableCode Ra0864.cycles } 144571
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0865.table, code := 1666829049427057461193189873384951873,
        encodes := Ra0865.tableCode_eq ▸ encodesTable_tableCode Ra0865.cycles } 144573
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0866.table, code := 1666829049427057461265247538289840193,
        encodes := Ra0866.tableCode_eq ▸ encodesTable_tableCode Ra0866.cycles } 144574
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0867.table, code := 1666829049427057461265247540437323841,
        encodes := Ra0867.tableCode_eq ▸ encodesTable_tableCode Ra0867.cycles } 144575
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0868.table, code := 4325852948381166572324929487254065217,
        encodes := Ra0868.tableCode_eq ▸ encodesTable_tableCode Ra0868.cycles } 145041
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0869.table, code := 4325934078019581179006695660035772481,
        encodes := Ra0869.tableCode_eq ▸ encodesTable_tableCode Ra0869.cycles } 145048
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0870.table, code := 4325934078019581179006695662183256129,
        encodes := Ra0870.tableCode_eq ▸ encodesTable_tableCode Ra0870.cycles } 145049
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0871.table, code := 4328611356087265558884529120123031617,
        encodes := Ra0871.tableCode_eq ▸ encodesTable_tableCode Ra0871.cycles } 145091
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0872.table, code := 4328692485725680165566295292904738881,
        encodes := Ra0872.tableCode_eq ▸ encodesTable_tableCode Ra0872.cycles } 145098
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0873.table, code := 4328692485725680165566295295052222529,
        encodes := Ra0873.tableCode_eq ▸ encodesTable_tableCode Ra0873.cycles } 145099
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0874.table, code := 4328611356087265561334487454851534913,
        encodes := Ra0874.tableCode_eq ▸ encodesTable_tableCode Ra0874.cycles } 145107
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0875.table, code := 4328692485725680168016253627633242177,
        encodes := Ra0875.tableCode_eq ▸ encodesTable_tableCode Ra0875.cycles } 145114
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0876.table, code := 4328692485725680168016253629780725825,
        encodes := Ra0876.tableCode_eq ▸ encodesTable_tableCode Ra0876.cycles } 145115
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0877.table, code := 4412012701224059953816780491962191937,
        encodes := Ra0877.tableCode_eq ▸ encodesTable_tableCode Ra0877.cycles } 145270
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0878.table, code := 4412012701224059953816780494109675585,
        encodes := Ra0878.tableCode_eq ▸ encodesTable_tableCode Ra0878.cycles } 145271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0879.table, code := 4412093830862474560498546666891382849,
        encodes := Ra0879.tableCode_eq ▸ encodesTable_tableCode Ra0879.cycles } 145278
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0880.table, code := 4412093830862474560498546669038866497,
        encodes := Ra0880.tableCode_eq ▸ encodesTable_tableCode Ra0880.cycles } 145279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0881.table, code := 4412012703709611438944466871251112001,
        encodes := Ra0881.tableCode_eq ▸ encodesTable_tableCode Ra0881.cycles } 145398
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0882.table, code := 4412012703709611438944466873398595649,
        encodes := Ra0882.tableCode_eq ▸ encodesTable_tableCode Ra0882.cycles } 145399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0883.table, code := 4412093833348026045626233046180302913,
        encodes := Ra0883.tableCode_eq ▸ encodesTable_tableCode Ra0883.cycles } 145406
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0884.table, code := 4412093833348026045626233048327786561,
        encodes := Ra0884.tableCode_eq ▸ encodesTable_tableCode Ra0884.cycles } 145407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0885.table, code := 1666829049499593088552552552961675329,
        encodes := Ra0885.tableCode_eq ▸ encodesTable_tableCode Ra0885.cycles } 145566
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0886.table, code := 1666829049499593088552552555109158977,
        encodes := Ra0886.tableCode_eq ▸ encodesTable_tableCode Ra0886.cycles } 145567
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0887.table, code := 1666829049581800118361558680756031553,
        encodes := Ra0887.tableCode_eq ▸ encodesTable_tableCode Ra0887.cycles } 145598
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0888.table, code := 1666829049581800118361558682903515201,
        encodes := Ra0888.tableCode_eq ▸ encodesTable_tableCode Ra0888.cycles } 145599
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0889.table, code := 4325852948535909229421240629720256577,
        encodes := Ra0889.tableCode_eq ▸ encodesTable_tableCode Ra0889.cycles } 146065
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0890.table, code := 4325934078174323836103006802501963841,
        encodes := Ra0890.tableCode_eq ▸ encodesTable_tableCode Ra0890.cycles } 146072
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0891.table, code := 4325934078174323836103006804649447489,
        encodes := Ra0891.tableCode_eq ▸ encodesTable_tableCode Ra0891.cycles } 146073
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0892.table, code := 4412012701378802608463133299699880001,
        encodes := Ra0892.tableCode_eq ▸ encodesTable_tableCode Ra0892.cycles } 146278
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0893.table, code := 4412012701378802608463133301847363649,
        encodes := Ra0893.tableCode_eq ▸ encodesTable_tableCode Ra0893.cycles } 146279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0894.table, code := 4412093831017217215144899474629070913,
        encodes := Ra0894.tableCode_eq ▸ encodesTable_tableCode Ra0894.cycles } 146286
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0895.table, code := 4412093831017217215144899476776554561,
        encodes := Ra0895.tableCode_eq ▸ encodesTable_tableCode Ra0895.cycles } 146287
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0896.table, code := 4412012701378802610913091634428383297,
        encodes := Ra0896.tableCode_eq ▸ encodesTable_tableCode Ra0896.cycles } 146294
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (832 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (832 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
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

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models013
