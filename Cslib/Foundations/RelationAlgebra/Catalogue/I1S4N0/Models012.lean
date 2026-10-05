/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0769
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0770
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0771
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0772
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0773
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0774
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0775
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0776
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0777
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0778
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0779
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0780
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0781
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0782
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0783
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0784
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0785
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0786
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0787
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0788
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0789
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0790
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0791
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0792
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0793
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0794
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0795
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0796
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0797
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0798
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0799
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0800
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0801
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0802
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0803
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0804
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0805
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0806
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0807
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0808
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0809
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0810
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0811
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0812
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0813
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0814
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0815
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0816
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0817
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0818
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0819
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0820
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0821
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0822
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0823
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0824
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0825
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0826
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0827
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0828
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0829
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0830
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0831
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0832

/-!
# Certified models 769–832 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models012

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0769.table, code := 9591247522718838631287848412089946177,
        encodes := Ra0769.tableCode_eq ▸ encodesTable_tableCode Ra0769.cycles } 128959
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0770.table, code := 9594005930422519766136158911943938113,
        encodes := Ra0770.tableCode_eq ▸ encodesTable_tableCode Ra0770.cycles } 129003
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0771.table, code := 9594005930424937617775390375759056961,
        encodes := Ra0771.tableCode_eq ▸ encodesTable_tableCode Ra0771.cycles } 129006
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0772.table, code := 9594005930424937617775390377906540609,
        encodes := Ra0772.tableCode_eq ▸ encodesTable_tableCode Ra0772.cycles } 129007
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0773.table, code := 9594005930422519768586117246672441409,
        encodes := Ra0773.tableCode_eq ▸ encodesTable_tableCode Ra0773.cycles } 129019
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0774.table, code := 9594005930424937620153291045582671937,
        encodes := Ra0774.tableCode_eq ▸ encodesTable_tableCode Ra0774.cycles } 129021
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0775.table, code := 9594005930424937620225348710487560257,
        encodes := Ra0775.tableCode_eq ▸ encodesTable_tableCode Ra0775.cycles } 129022
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0776.table, code := 9594005930424937620225348712635043905,
        encodes := Ra0776.tableCode_eq ▸ encodesTable_tableCode Ra0776.cycles } 129023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0777.table, code := 9591247522791374258575153424614297665,
        encodes := Ra0777.tableCode_eq ▸ encodesTable_tableCode Ra0777.cycles } 129950
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0778.table, code := 9591247522791374258575153426761781313,
        encodes := Ra0778.tableCode_eq ▸ encodesTable_tableCode Ra0778.cycles } 129951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0779.table, code := 9591247522873581288312101887503765569,
        encodes := Ra0779.tableCode_eq ▸ encodesTable_tableCode Ra0779.cycles } 129981
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0780.table, code := 9591247522873581288384159552408653889,
        encodes := Ra0780.tableCode_eq ▸ encodesTable_tableCode Ra0780.cycles } 129982
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0781.table, code := 9591247522873581288384159554556137537,
        encodes := Ra0781.tableCode_eq ▸ encodesTable_tableCode Ra0781.cycles } 129983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0782.table, code := 9594005930497473247440596060254507073,
        encodes := Ra0782.tableCode_eq ▸ encodesTable_tableCode Ra0782.cycles } 130013
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0783.table, code := 9594005930497473247512653725159395393,
        encodes := Ra0783.tableCode_eq ▸ encodesTable_tableCode Ra0783.cycles } 130014
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0784.table, code := 9594005930497473247512653727306879041,
        encodes := Ra0784.tableCode_eq ▸ encodesTable_tableCode Ra0784.cycles } 130015
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0785.table, code := 9594005930579680277249602188048863297,
        encodes := Ra0785.tableCode_eq ▸ encodesTable_tableCode Ra0785.cycles } 130045
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0786.table, code := 9594005930579680277321659852953751617,
        encodes := Ra0786.tableCode_eq ▸ encodesTable_tableCode Ra0786.cycles } 130046
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0787.table, code := 9594005930579680277321659855101235265,
        encodes := Ra0787.tableCode_eq ▸ encodesTable_tableCode Ra0787.cycles } 130047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0788.table, code := 9591247522791374263186839445189169217,
        encodes := Ra0788.tableCode_eq ▸ encodesTable_tableCode Ra0788.cycles } 130975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0789.table, code := 9591247522873581290545887238255022145,
        encodes := Ra0789.tableCode_eq ▸ encodesTable_tableCode Ra0789.cycles } 130991
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0790.table, code := 9591247522873581292995845572983525441,
        encodes := Ra0790.tableCode_eq ▸ encodesTable_tableCode Ra0790.cycles } 131007
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0791.table, code := 9594005930497473249674381411005763649,
        encodes := Ra0791.tableCode_eq ▸ encodesTable_tableCode Ra0791.cycles } 131023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0792.table, code := 9594005930497473252124339745734266945,
        encodes := Ra0792.tableCode_eq ▸ encodesTable_tableCode Ra0792.cycles } 131039
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0793.table, code := 9594005930579680279483387538800119873,
        encodes := Ra0793.tableCode_eq ▸ encodesTable_tableCode Ra0793.cycles } 131055
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0794.table, code := 9594005930579680281933345873528623169,
        encodes := Ra0794.tableCode_eq ▸ encodesTable_tableCode Ra0794.cycles } 131071
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0795.table, code := 1666829041752796138864136491270148161,
        encodes := Ra0795.tableCode_eq ▸ encodesTable_tableCode Ra0795.cycles } 137230
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0796.table, code := 1666829041752796138864136493417631809,
        encodes := Ra0796.tableCode_eq ▸ encodesTable_tableCode Ra0796.cycles } 137231
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0797.table, code := 1666829041752796141242037161093763137,
        encodes := Ra0797.tableCode_eq ▸ encodesTable_tableCode Ra0797.cycles } 137245
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0798.table, code := 1666829041752796141314094825998651457,
        encodes := Ra0798.tableCode_eq ▸ encodesTable_tableCode Ra0798.cycles } 137246
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0799.table, code := 1666829041752796141314094828146135105,
        encodes := Ra0799.tableCode_eq ▸ encodesTable_tableCode Ra0799.cycles } 137247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0800.table, code := 1666829044235929774730492074420080705,
        encodes := Ra0800.tableCode_eq ▸ encodesTable_tableCode Ra0800.cycles } 137369
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0801.table, code := 1666829044238347626369723538235199553,
        encodes := Ra0801.tableCode_eq ▸ encodesTable_tableCode Ra0801.cycles } 137372
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0802.table, code := 1666829044238347626369723540382683201,
        encodes := Ra0802.tableCode_eq ▸ encodesTable_tableCode Ra0802.cycles } 137373
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0803.table, code := 1666829044318136802161597532390821953,
        encodes := Ra0803.tableCode_eq ▸ encodesTable_tableCode Ra0803.cycles } 137386
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0804.table, code := 1666829044318136802161597534538305601,
        encodes := Ra0804.tableCode_eq ▸ encodesTable_tableCode Ra0804.cycles } 137387
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0805.table, code := 1666829044320554653800828998353424449,
        encodes := Ra0805.tableCode_eq ▸ encodesTable_tableCode Ra0805.cycles } 137390
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0806.table, code := 1666829044320554653800829000500908097,
        encodes := Ra0806.tableCode_eq ▸ encodesTable_tableCode Ra0806.cycles } 137391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0807.table, code := 1666829044318136804611555869266808897,
        encodes := Ra0807.tableCode_eq ▸ encodesTable_tableCode Ra0807.cycles } 137403
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0808.table, code := 1666829044320554656250787333081927745,
        encodes := Ra0808.tableCode_eq ▸ encodesTable_tableCode Ra0808.cycles } 137406
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0809.table, code := 1666829044320554656250787335229411393,
        encodes := Ra0809.tableCode_eq ▸ encodesTable_tableCode Ra0809.cycles } 137407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0810.table, code := 4325852943274663767310469282046152769,
        encodes := Ra0810.tableCode_eq ▸ encodesTable_tableCode Ra0810.cycles } 137873
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0811.table, code := 4325934072913078373992235454827860033,
        encodes := Ra0811.tableCode_eq ▸ encodesTable_tableCode Ra0811.cycles } 137880
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0812.table, code := 4325934072913078373992235456975343681,
        encodes := Ra0812.tableCode_eq ▸ encodesTable_tableCode Ra0812.cycles } 137881
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0813.table, code := 4409254288329251129983756191362453569,
        encodes := Ra0813.tableCode_eq ▸ encodesTable_tableCode Ra0813.cycles } 138004
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0814.table, code := 4409254288329251129983756193509937217,
        encodes := Ra0814.tableCode_eq ▸ encodesTable_tableCode Ra0814.cycles } 138005
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0815.table, code := 4409335417967665736665522366291644481,
        encodes := Ra0815.tableCode_eq ▸ encodesTable_tableCode Ra0815.cycles } 138012
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0816.table, code := 4409335417967665736665522368439128129,
        encodes := Ra0816.tableCode_eq ▸ encodesTable_tableCode Ra0816.cycles } 138013
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0817.table, code := 4409254290814802615111442572798857281,
        encodes := Ra0817.tableCode_eq ▸ encodesTable_tableCode Ra0817.cycles } 138133
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0818.table, code := 4409335420453217221793208745580564545,
        encodes := Ra0818.tableCode_eq ▸ encodesTable_tableCode Ra0818.cycles } 138140
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0819.table, code := 4409335420453217221793208747728048193,
        encodes := Ra0819.tableCode_eq ▸ encodesTable_tableCode Ra0819.cycles } 138141
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0820.table, code := 4412012698603108631480048331314696257,
        encodes := Ra0820.tableCode_eq ▸ encodesTable_tableCode Ra0820.cycles } 138214
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0821.table, code := 4412012698603108631480048333462179905,
        encodes := Ra0821.tableCode_eq ▸ encodesTable_tableCode Ra0821.cycles } 138215
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0822.table, code := 4412093828241523238161814506243887169,
        encodes := Ra0822.tableCode_eq ▸ encodesTable_tableCode Ra0822.cycles } 138222
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0823.table, code := 4412093828241523238161814508391370817,
        encodes := Ra0823.tableCode_eq ▸ encodesTable_tableCode Ra0823.cycles } 138223
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0824.table, code := 4412012698603108633930006666043199553,
        encodes := Ra0824.tableCode_eq ▸ encodesTable_tableCode Ra0824.cycles } 138230
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0825.table, code := 4412012698603108633930006668190683201,
        encodes := Ra0825.tableCode_eq ▸ encodesTable_tableCode Ra0825.cycles } 138231
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0826.table, code := 4412093828241523240611772840972390465,
        encodes := Ra0826.tableCode_eq ▸ encodesTable_tableCode Ra0826.cycles } 138238
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0827.table, code := 4412093828241523240611772843119874113,
        encodes := Ra0827.tableCode_eq ▸ encodesTable_tableCode Ra0827.cycles } 138239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0828.table, code := 1666829041752796143475822511845019713,
        encodes := Ra0828.tableCode_eq ▸ encodesTable_tableCode Ra0828.cycles } 138255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0829.table, code := 1666829041752796145925780846573523009,
        encodes := Ra0829.tableCode_eq ▸ encodesTable_tableCode Ra0829.cycles } 138271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0830.table, code := 1666829044235929779342178092847468609,
        encodes := Ra0830.tableCode_eq ▸ encodesTable_tableCode Ra0830.cycles } 138393
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0831.table, code := 1666829044238347630981409556662587457,
        encodes := Ra0831.tableCode_eq ▸ encodesTable_tableCode Ra0831.cycles } 138396
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0832.table, code := 1666829044238347630981409558810071105,
        encodes := Ra0832.tableCode_eq ▸ encodesTable_tableCode Ra0832.cycles } 138397
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (768 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (768 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (768 + i.val) 0 ≤ Data.profiles (768 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (768 + i.val) 0 = Data.canonicalMask (768 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (768 + i.val) < Data.canonicalMask (768 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (768 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models012
