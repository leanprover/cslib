/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0641
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0642
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0643
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0644
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0645
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0646
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0647
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0648
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0649
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0650
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0651
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0652
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0653
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0654
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0655
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0656
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0657
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0658
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0659
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0660
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0661
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0662
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0663
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0664
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0665
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0666
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0667
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0668
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0669
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0670
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0671
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0672
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0673
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0674
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0675
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0676
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0677
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0678
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0679
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0680
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0681
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0682
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0683
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0684
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0685
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0686
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0687
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0688
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0689
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0690
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0691
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0692
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0693
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0694
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0695
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0696
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0697
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0698
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0699
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0700
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0701
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0702
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0703
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0704

/-!
# Certified models 641–704 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models010

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0641.table, code := 9593924795677602356817833199482966081,
        encodes := Ra0641.tableCode_eq ▸ encodesTable_tableCode Ra0641.cycles } 121841
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0642.table, code := 9593924795677602356889890864387854401,
        encodes := Ra0642.tableCode_eq ▸ encodesTable_tableCode Ra0642.cycles } 121842
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0643.table, code := 9593924795677602356889890866535338049,
        encodes := Ra0643.tableCode_eq ▸ encodesTable_tableCode Ra0643.cycles } 121843
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0644.table, code := 9593924795680020208457064665445568577,
        encodes := Ra0644.tableCode_eq ▸ encodesTable_tableCode Ra0644.cycles } 121845
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0645.table, code := 9593924795680020208529122330350456897,
        encodes := Ra0645.tableCode_eq ▸ encodesTable_tableCode Ra0645.cycles } 121846
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0646.table, code := 9593924795680020208529122332497940545,
        encodes := Ra0646.tableCode_eq ▸ encodesTable_tableCode Ra0646.cycles } 121847
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0647.table, code := 9594005925316016963499599374412156993,
        encodes := Ra0647.tableCode_eq ▸ encodesTable_tableCode Ra0647.cycles } 121849
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0648.table, code := 9594005925316016963571657039317045313,
        encodes := Ra0648.tableCode_eq ▸ encodesTable_tableCode Ra0648.cycles } 121850
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0649.table, code := 9594005925316016963571657041464528961,
        encodes := Ra0649.tableCode_eq ▸ encodesTable_tableCode Ra0649.cycles } 121851
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0650.table, code := 9594005925318434815138830840374759489,
        encodes := Ra0650.tableCode_eq ▸ encodesTable_tableCode Ra0650.cycles } 121853
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0651.table, code := 9594005925318434815210888505279647809,
        encodes := Ra0651.tableCode_eq ▸ encodesTable_tableCode Ra0651.cycles } 121854
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0652.table, code := 9594005925318434815210888507427131457,
        encodes := Ra0652.tableCode_eq ▸ encodesTable_tableCode Ra0652.cycles } 121855
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0653.table, code := 9591247515126784343307429511291998273,
        encodes := Ra0653.tableCode_eq ▸ encodesTable_tableCode Ra0653.cycles } 122671
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0654.table, code := 9591247515126784345757387846020501569,
        encodes := Ra0654.tableCode_eq ▸ encodesTable_tableCode Ra0654.cycles } 122687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0655.table, code := 9594005922832883332244929811837096001,
        encodes := Ra0655.tableCode_eq ▸ encodesTable_tableCode Ra0655.cycles } 122735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0656.table, code := 9594005922832883334694888146565599297,
        encodes := Ra0656.tableCode_eq ▸ encodesTable_tableCode Ra0656.cycles } 122751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0657.table, code := 9591247517530128801076068095367581761,
        encodes := Ra0657.tableCode_eq ▸ encodesTable_tableCode Ra0657.cycles } 122782
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0658.table, code := 9591247517530128801076068097515065409,
        encodes := Ra0658.tableCode_eq ▸ encodesTable_tableCode Ra0658.cycles } 122783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0659.table, code := 9591247517609917976795884422470832193,
        encodes := Ra0659.tableCode_eq ▸ encodesTable_tableCode Ra0659.cycles } 122794
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0660.table, code := 9591247517609917976795884424618315841,
        encodes := Ra0660.tableCode_eq ▸ encodesTable_tableCode Ra0660.cycles } 122795
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0661.table, code := 9591247517612335828435115888433434689,
        encodes := Ra0661.tableCode_eq ▸ encodesTable_tableCode Ra0661.cycles } 122798
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0662.table, code := 9591247517612335828435115890580918337,
        encodes := Ra0662.tableCode_eq ▸ encodesTable_tableCode Ra0662.cycles } 122799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0663.table, code := 9591247517609917979173785092294447169,
        encodes := Ra0663.tableCode_eq ▸ encodesTable_tableCode Ra0663.cycles } 122809
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0664.table, code := 9591247517609917979245842757199335489,
        encodes := Ra0664.tableCode_eq ▸ encodesTable_tableCode Ra0664.cycles } 122810
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0665.table, code := 9591247517609917979245842759346819137,
        encodes := Ra0665.tableCode_eq ▸ encodesTable_tableCode Ra0665.cycles } 122811
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0666.table, code := 9591247517612335830813016558257049665,
        encodes := Ra0666.tableCode_eq ▸ encodesTable_tableCode Ra0666.cycles } 122813
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0667.table, code := 9591247517612335830885074223161937985,
        encodes := Ra0667.tableCode_eq ▸ encodesTable_tableCode Ra0667.cycles } 122814
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0668.table, code := 9591247517612335830885074225309421633,
        encodes := Ra0668.tableCode_eq ▸ encodesTable_tableCode Ra0668.cycles } 122815
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0669.table, code := 9593924795597813180881843886254985281,
        encodes := Ra0669.tableCode_eq ▸ encodesTable_tableCode Ra0669.cycles } 122822
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0670.table, code := 9593924795597813180881843888402468929,
        encodes := Ra0670.tableCode_eq ▸ encodesTable_tableCode Ra0670.cycles } 122823
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0671.table, code := 9594005925236227787563610061184176193,
        encodes := Ra0671.tableCode_eq ▸ encodesTable_tableCode Ra0671.cycles } 122830
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0672.table, code := 9594005925236227787563610063331659841,
        encodes := Ra0672.tableCode_eq ▸ encodesTable_tableCode Ra0672.cycles } 122831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0673.table, code := 9593924795597813183331802220983488577,
        encodes := Ra0673.tableCode_eq ▸ encodesTable_tableCode Ra0673.cycles } 122838
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0674.table, code := 9593924795597813183331802223130972225,
        encodes := Ra0674.tableCode_eq ▸ encodesTable_tableCode Ra0674.cycles } 122839
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0675.table, code := 9594005925236227790013568395912679489,
        encodes := Ra0675.tableCode_eq ▸ encodesTable_tableCode Ra0675.cycles } 122846
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0676.table, code := 9594005925236227790013568398060163137,
        encodes := Ra0676.tableCode_eq ▸ encodesTable_tableCode Ra0676.cycles } 122847
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0677.table, code := 9593924795677602359051618548086739009,
        encodes := Ra0677.tableCode_eq ▸ encodesTable_tableCode Ra0677.cycles } 122850
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0678.table, code := 9593924795677602359051618550234222657,
        encodes := Ra0678.tableCode_eq ▸ encodesTable_tableCode Ra0678.cycles } 122851
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0679.table, code := 9593924795680020210690850014049341505,
        encodes := Ra0679.tableCode_eq ▸ encodesTable_tableCode Ra0679.cycles } 122854
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0680.table, code := 9593924795680020210690850016196825153,
        encodes := Ra0680.tableCode_eq ▸ encodesTable_tableCode Ra0680.cycles } 122855
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0681.table, code := 9594005925316016965733384723015929921,
        encodes := Ra0681.tableCode_eq ▸ encodesTable_tableCode Ra0681.cycles } 122858
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0682.table, code := 9594005925316016965733384725163413569,
        encodes := Ra0682.tableCode_eq ▸ encodesTable_tableCode Ra0682.cycles } 122859
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0683.table, code := 9594005925318434817372616188978532417,
        encodes := Ra0683.tableCode_eq ▸ encodesTable_tableCode Ra0683.cycles } 122862
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0684.table, code := 9594005925318434817372616191126016065,
        encodes := Ra0684.tableCode_eq ▸ encodesTable_tableCode Ra0684.cycles } 122863
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0685.table, code := 9593924795677602361429519217910353985,
        encodes := Ra0685.tableCode_eq ▸ encodesTable_tableCode Ra0685.cycles } 122865
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0686.table, code := 9593924795677602361501576882815242305,
        encodes := Ra0686.tableCode_eq ▸ encodesTable_tableCode Ra0686.cycles } 122866
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0687.table, code := 9593924795677602361501576884962725953,
        encodes := Ra0687.tableCode_eq ▸ encodesTable_tableCode Ra0687.cycles } 122867
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0688.table, code := 9593924795680020213068750683872956481,
        encodes := Ra0688.tableCode_eq ▸ encodesTable_tableCode Ra0688.cycles } 122869
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0689.table, code := 9593924795680020213140808348777844801,
        encodes := Ra0689.tableCode_eq ▸ encodesTable_tableCode Ra0689.cycles } 122870
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0690.table, code := 9593924795680020213140808350925328449,
        encodes := Ra0690.tableCode_eq ▸ encodesTable_tableCode Ra0690.cycles } 122871
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0691.table, code := 9594005925316016968111285392839544897,
        encodes := Ra0691.tableCode_eq ▸ encodesTable_tableCode Ra0691.cycles } 122873
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0692.table, code := 9594005925316016968183343057744433217,
        encodes := Ra0692.tableCode_eq ▸ encodesTable_tableCode Ra0692.cycles } 122874
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0693.table, code := 9594005925316016968183343059891916865,
        encodes := Ra0693.tableCode_eq ▸ encodesTable_tableCode Ra0693.cycles } 122875
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0694.table, code := 9594005925318434819750516858802147393,
        encodes := Ra0694.tableCode_eq ▸ encodesTable_tableCode Ra0694.cycles } 122877
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0695.table, code := 9594005925318434819822574523707035713,
        encodes := Ra0695.tableCode_eq ▸ encodesTable_tableCode Ra0695.cycles } 122878
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0696.table, code := 9594005925318434819822574525854519361,
        encodes := Ra0696.tableCode_eq ▸ encodesTable_tableCode Ra0696.cycles } 122879
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0697.table, code := 9588813633566398047099847587471298625,
        encodes := Ra0697.tableCode_eq ▸ encodesTable_tableCode Ra0697.cycles } 123901
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0698.table, code := 9588813633566398047171905252376186945,
        encodes := Ra0698.tableCode_eq ▸ encodesTable_tableCode Ra0698.cycles } 123902
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0699.table, code := 9588813633566398047171905254523670593,
        encodes := Ra0699.tableCode_eq ▸ encodesTable_tableCode Ra0699.cycles } 123903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0700.table, code := 9588732503925565591012635297330761793,
        encodes := Ra0700.tableCode_eq ▸ encodesTable_tableCode Ra0700.cycles } 124899
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0701.table, code := 9588732503927983442651866761145880641,
        encodes := Ra0701.tableCode_eq ▸ encodesTable_tableCode Ra0701.cycles } 124902
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0702.table, code := 9588732503927983442651866763293364289,
        encodes := Ra0702.tableCode_eq ▸ encodesTable_tableCode Ra0702.cycles } 124903
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0703.table, code := 9588813633563980197694401470112469057,
        encodes := Ra0703.tableCode_eq ▸ encodesTable_tableCode Ra0703.cycles } 124906
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0704.table, code := 9588813633563980197694401472259952705,
        encodes := Ra0704.tableCode_eq ▸ encodesTable_tableCode Ra0704.cycles } 124907
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (640 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (640 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
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

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models010
