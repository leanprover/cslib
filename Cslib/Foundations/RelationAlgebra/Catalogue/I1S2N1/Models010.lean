/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0641
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0642
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0643
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0644
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0645
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0646
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0647
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0648
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0649
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0650
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0651
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0652
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0653
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0654
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0655
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0656
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0657
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0658
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0659
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0660
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0661
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0662
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0663
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0664
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0665
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0666
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0667
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0668
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0669
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0670
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0671
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0672
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0673
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0674
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0675
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0676
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0677
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0678
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0679
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0680
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0681
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0682
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0683
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0684
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0685
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0686
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0687
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0688
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0689
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0690
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0691
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0692
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0693
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0694
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0695
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0696
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0697
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0698
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0699
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0700
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0701
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0702
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0703
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0704

/-!
# Certified models 641–704 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models010

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0641.table, code := 13446690242011939803332540986380521537,
        encodes := Ra0641.tableCode_eq ▸ encodesTable_tableCode Ra0641.cycles } 36862
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0642.table, code := 13446690242011939803332540988528005185,
        encodes := Ra0642.tableCode_eq ▸ encodesTable_tableCode Ra0642.cycles } 36863
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0643.table, code := 18748025181535666293065674584439918657,
        encodes := Ra0643.tableCode_eq ▸ encodesTable_tableCode Ra0643.cycles } 37374
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0644.table, code := 18748025181535666293065674586587402305,
        encodes := Ra0644.tableCode_eq ▸ encodesTable_tableCode Ra0644.cycles } 37375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0645.table, code := 16089244668916953231008111307801235521,
        encodes := Ra0645.tableCode_eq ▸ encodesTable_tableCode Ra0645.cycles } 37750
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0646.table, code := 16089244668916953231008111309948719169,
        encodes := Ra0646.tableCode_eq ▸ encodesTable_tableCode Ra0646.cycles } 37751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0647.table, code := 16089244668916953233458069642529738817,
        encodes := Ra0647.tableCode_eq ▸ encodesTable_tableCode Ra0647.cycles } 37758
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0648.table, code := 16089244668916953233458069644677222465,
        encodes := Ra0648.tableCode_eq ▸ encodesTable_tableCode Ra0648.cycles } 37759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0649.table, code := 18748025181535666295227402268138803265,
        encodes := Ra0649.tableCode_eq ▸ encodesTable_tableCode Ra0649.cycles } 37878
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0650.table, code := 18748025181535666295227402270286286913,
        encodes := Ra0650.tableCode_eq ▸ encodesTable_tableCode Ra0650.cycles } 37879
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0651.table, code := 18748025181535666297677360602867306561,
        encodes := Ra0651.tableCode_eq ▸ encodesTable_tableCode Ra0651.cycles } 37886
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0652.table, code := 18748025181535666297677360605014790209,
        encodes := Ra0652.tableCode_eq ▸ encodesTable_tableCode Ra0652.cycles } 37887
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0653.table, code := 16094436965930235456546179889951412289,
        encodes := Ra0653.tableCode_eq ▸ encodesTable_tableCode Ra0653.cycles } 38262
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0654.table, code := 16094436965930235456546179892098895937,
        encodes := Ra0654.tableCode_eq ▸ encodesTable_tableCode Ra0654.cycles } 38263
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0655.table, code := 16094436965930235458996138224679915585,
        encodes := Ra0655.tableCode_eq ▸ encodesTable_tableCode Ra0655.cycles } 38270
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0656.table, code := 16094436965930235458996138226827399233,
        encodes := Ra0656.tableCode_eq ▸ encodesTable_tableCode Ra0656.cycles } 38271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0657.table, code := 18753217478548948520765470850288980033,
        encodes := Ra0657.tableCode_eq ▸ encodesTable_tableCode Ra0657.cycles } 38390
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0658.table, code := 18753217478548948520765470852436463681,
        encodes := Ra0658.tableCode_eq ▸ encodesTable_tableCode Ra0658.cycles } 38391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0659.table, code := 18753217478548948523215429185017483329,
        encodes := Ra0659.tableCode_eq ▸ encodesTable_tableCode Ra0659.cycles } 38398
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0660.table, code := 18753217478548948523215429187164966977,
        encodes := Ra0660.tableCode_eq ▸ encodesTable_tableCode Ra0660.cycles } 38399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0661.table, code := 16094436965930235461157865908378800193,
        encodes := Ra0661.tableCode_eq ▸ encodesTable_tableCode Ra0661.cycles } 38774
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0662.table, code := 16094436965930235461157865910526283841,
        encodes := Ra0662.tableCode_eq ▸ encodesTable_tableCode Ra0662.cycles } 38775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0663.table, code := 16094436965930235463607824243107303489,
        encodes := Ra0663.tableCode_eq ▸ encodesTable_tableCode Ra0663.cycles } 38782
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0664.table, code := 16094436965930235463607824245254787137,
        encodes := Ra0664.tableCode_eq ▸ encodesTable_tableCode Ra0664.cycles } 38783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0665.table, code := 18753217478548948525377156868716367937,
        encodes := Ra0665.tableCode_eq ▸ encodesTable_tableCode Ra0665.cycles } 38902
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0666.table, code := 18753217478548948525377156870863851585,
        encodes := Ra0666.tableCode_eq ▸ encodesTable_tableCode Ra0666.cycles } 38903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0667.table, code := 18753217478548948527827115203444871233,
        encodes := Ra0667.tableCode_eq ▸ encodesTable_tableCode Ra0667.cycles } 38910
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0668.table, code := 18753217478548948527827115205592354881,
        encodes := Ra0668.tableCode_eq ▸ encodesTable_tableCode Ra0668.cycles } 38911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0669.table, code := 18768794527426130927256376936197525569,
        encodes := Ra0669.tableCode_eq ▸ encodesTable_tableCode Ra0669.cycles } 39422
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0670.table, code := 18768794527426130927256376938345009217,
        encodes := Ra0670.tableCode_eq ▸ encodesTable_tableCode Ra0670.cycles } 39423
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0671.table, code := 18768794527426130929418104619896410177,
        encodes := Ra0671.tableCode_eq ▸ encodesTable_tableCode Ra0671.cycles } 39926
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0672.table, code := 18768794527426130929418104622043893825,
        encodes := Ra0672.tableCode_eq ▸ encodesTable_tableCode Ra0672.cycles } 39927
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0673.table, code := 18768794527426130931868062954624913473,
        encodes := Ra0673.tableCode_eq ▸ encodesTable_tableCode Ra0673.cycles } 39934
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0674.table, code := 18768794527426130931868062956772397121,
        encodes := Ra0674.tableCode_eq ▸ encodesTable_tableCode Ra0674.cycles } 39935
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0675.table, code := 18773337708103933789688218835096965185,
        encodes := Ra0675.tableCode_eq ▸ encodesTable_tableCode Ra0675.cycles } 40382
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0676.table, code := 18773337708103933789688218837244448833,
        encodes := Ra0676.tableCode_eq ▸ encodesTable_tableCode Ra0676.cycles } 40383
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0677.table, code := 18773986824439413154956173202046586945,
        encodes := Ra0677.tableCode_eq ▸ encodesTable_tableCode Ra0677.cycles } 40438
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0678.table, code := 18773986824439413154956173204194070593,
        encodes := Ra0678.tableCode_eq ▸ encodesTable_tableCode Ra0678.cycles } 40439
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0679.table, code := 18773986824439413157406131536775090241,
        encodes := Ra0679.tableCode_eq ▸ encodesTable_tableCode Ra0679.cycles } 40446
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0680.table, code := 18773986824439413157406131538922573889,
        encodes := Ra0680.tableCode_eq ▸ encodesTable_tableCode Ra0680.cycles } 40447
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0681.table, code := 18773337708103933794299904855671836737,
        encodes := Ra0681.tableCode_eq ▸ encodesTable_tableCode Ra0681.cycles } 40895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0682.table, code := 18773986824439413159567859220473974849,
        encodes := Ra0682.tableCode_eq ▸ encodesTable_tableCode Ra0682.cycles } 40950
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0683.table, code := 18773986824439413159567859222621458497,
        encodes := Ra0683.tableCode_eq ▸ encodesTable_tableCode Ra0683.cycles } 40951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0684.table, code := 18773986824439413162017817555202478145,
        encodes := Ra0684.tableCode_eq ▸ encodesTable_tableCode Ra0684.cycles } 40958
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0685.table, code := 18773986824439413162017817557349961793,
        encodes := Ra0685.tableCode_eq ▸ encodesTable_tableCode Ra0685.cycles } 40959
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0686.table, code := 10946031394733424408234599432918929473,
        encodes := Ra0686.tableCode_eq ▸ encodesTable_tableCode Ra0686.cycles } 43330
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0687.table, code := 10946031394733424408234599435066413121,
        encodes := Ra0687.tableCode_eq ▸ encodesTable_tableCode Ra0687.cycles } 43331
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0688.table, code := 10946031394733424410612500102742544449,
        encodes := Ra0688.tableCode_eq ▸ encodesTable_tableCode Ra0688.cycles } 43337
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0689.table, code := 10946031394733424410684557767647432769,
        encodes := Ra0689.tableCode_eq ▸ encodesTable_tableCode Ra0689.cycles } 43338
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0690.table, code := 10946031394733424410684557769794916417,
        encodes := Ra0690.tableCode_eq ▸ encodesTable_tableCode Ra0690.cycles } 43339
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0691.table, code := 13604893036992969930774888034148290625,
        encodes := Ra0691.tableCode_eq ▸ encodesTable_tableCode Ra0691.cycles } 43462
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0692.table, code := 13604893036992969930774888036295774273,
        encodes := Ra0692.tableCode_eq ▸ encodesTable_tableCode Ra0692.cycles } 43463
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0693.table, code := 13607651444781275951899295130163875905,
        encodes := Ra0693.tableCode_eq ▸ encodesTable_tableCode Ra0693.cycles } 43516
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0694.table, code := 13607651444781275951899295132311359553,
        encodes := Ra0694.tableCode_eq ▸ encodesTable_tableCode Ra0694.cycles } 43517
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0695.table, code := 13607651444781275951971352797216247873,
        encodes := Ra0695.tableCode_eq ▸ encodesTable_tableCode Ra0695.cycles } 43518
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0696.table, code := 13607651444781275951971352799363731521,
        encodes := Ra0696.tableCode_eq ▸ encodesTable_tableCode Ra0696.cycles } 43519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0697.table, code := 10946031394733424412846285453493801025,
        encodes := Ra0697.tableCode_eq ▸ encodesTable_tableCode Ra0697.cycles } 43843
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0698.table, code := 10946031394733424415296243788222304321,
        encodes := Ra0698.tableCode_eq ▸ encodesTable_tableCode Ra0698.cycles } 43851
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0699.table, code := 13604893036992969935386574052575678529,
        encodes := Ra0699.tableCode_eq ▸ encodesTable_tableCode Ra0699.cycles } 43974
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0700.table, code := 13604893036992969935386574054723162177,
        encodes := Ra0700.tableCode_eq ▸ encodesTable_tableCode Ra0700.cycles } 43975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0701.table, code := 13607570315140443498189983509846954049,
        encodes := Ra0701.tableCode_eq ▸ encodesTable_tableCode Ra0701.cycles } 44025
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0702.table, code := 13607570315140443498262041176899326017,
        encodes := Ra0702.tableCode_eq ▸ encodesTable_tableCode Ra0702.cycles } 44027
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0703.table, code := 13607651444781275956510981148591263809,
        encodes := Ra0703.tableCode_eq ▸ encodesTable_tableCode Ra0703.cycles } 44028
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0704.table, code := 13607651444781275956510981150738747457,
        encodes := Ra0704.tableCode_eq ▸ encodesTable_tableCode Ra0704.cycles } 44029
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (640 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (640 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (640 + i.val) 0 ≤ Data.profiles (640 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (640 + i.val) 0 = Data.canonicalMask (640 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (640 + i.val) < Data.canonicalMask (640 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (640 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models010
