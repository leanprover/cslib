/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0769
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0770
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0771
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0772
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0773
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0774
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0775
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0776
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0777
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0778
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0779
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0780
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0781
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0782
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0783
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0784
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0785
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0786
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0787
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0788
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0789
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0790
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0791
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0792
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0793
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0794
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0795
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0796
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0797
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0798
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0799
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0800
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0801
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0802
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0803
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0804
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0805
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0806
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0807
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0808
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0809
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0810
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0811
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0812
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0813
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0814
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0815
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0816
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0817
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0818
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0819
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0820
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0821
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0822
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0823
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0824
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0825
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0826
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0827
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0828
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0829
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0830
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0831
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0832

/-!
# Certified models 769–832 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models012

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0769.table, code := 35604655628625751853691482179748761665,
        encodes := Ra0769.tableCode_eq ▸ encodesTable_tableCode Ra0769.cycles } 50381
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0770.table, code := 33028870736112434979765161500990509121,
        encodes := Ra0770.tableCode_eq ▸ encodesTable_tableCode Ra0770.cycles } 50504
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0771.table, code := 33028870736112434979765161503137992769,
        encodes := Ra0771.tableCode_eq ▸ encodesTable_tableCode Ra0771.cycles } 50505
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0772.table, code := 33028951865753267438086159141882302529,
        encodes := Ra0772.tableCode_eq ▸ encodesTable_tableCode Ra0772.cycles } 50508
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0773.table, code := 33028951865753267438086159144029786177,
        encodes := Ra0773.tableCode_eq ▸ encodesTable_tableCode Ra0773.cycles } 50509
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0774.table, code := 35687651248731148043984452463475560513,
        encodes := Ra0774.tableCode_eq ▸ encodesTable_tableCode Ra0774.cycles } 50633
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0775.table, code := 35687732378371980502305450102219870273,
        encodes := Ra0775.tableCode_eq ▸ encodesTable_tableCode Ra0775.cycles } 50636
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0776.table, code := 35687732378371980502305450104367353921,
        encodes := Ra0776.tableCode_eq ▸ encodesTable_tableCode Ra0776.cycles } 50637
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0777.table, code := 35690409656519454060353058224138883137,
        encodes := Ra0777.tableCode_eq ▸ encodesTable_tableCode Ra0777.cycles } 50675
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0778.table, code := 35690490786160286518674055862883192897,
        encodes := Ra0778.tableCode_eq ▸ encodesTable_tableCode Ra0778.cycles } 50678
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0779.table, code := 35690490786160286518674055865030676545,
        encodes := Ra0779.tableCode_eq ▸ encodesTable_tableCode Ra0779.cycles } 50679
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0780.table, code := 35690409656519454062730958891815014465,
        encodes := Ra0780.tableCode_eq ▸ encodesTable_tableCode Ra0780.cycles } 50681
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0781.table, code := 35690409656519454062803016558867386433,
        encodes := Ra0781.tableCode_eq ▸ encodesTable_tableCode Ra0781.cycles } 50683
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0782.table, code := 35690490786160286521051956532706807873,
        encodes := Ra0782.tableCode_eq ▸ encodesTable_tableCode Ra0782.cycles } 50685
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0783.table, code := 35690490786160286521124014197611696193,
        encodes := Ra0783.tableCode_eq ▸ encodesTable_tableCode Ra0783.cycles } 50686
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0784.table, code := 35690490786160286521124014199759179841,
        encodes := Ra0784.tableCode_eq ▸ encodesTable_tableCode Ra0784.cycles } 50687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0785.table, code := 32945225999671559423988063868484325441,
        encodes := Ra0785.tableCode_eq ▸ encodesTable_tableCode Ra0785.cycles } 50695
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0786.table, code := 32945225999671559426438022203212828737,
        encodes := Ra0786.tableCode_eq ▸ encodesTable_tableCode Ra0786.cycles } 50703
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0787.table, code := 32947984407459865442734570296823779393,
        encodes := Ra0787.tableCode_eq ▸ encodesTable_tableCode Ra0787.cycles } 50743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0788.table, code := 32947984407459865445184528631552282689,
        encodes := Ra0788.tableCode_eq ▸ encodesTable_tableCode Ra0788.cycles } 50751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0789.table, code := 35603925382649440032264257853458747457,
        encodes := Ra0789.tableCode_eq ▸ encodesTable_tableCode Ra0789.cycles } 50824
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0790.table, code := 35604006512290272490585255494350540865,
        encodes := Ra0790.tableCode_eq ▸ encodesTable_tableCode Ra0790.cycles } 50828
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0791.table, code := 35604006512290272490585255496498024513,
        encodes := Ra0791.tableCode_eq ▸ encodesTable_tableCode Ra0791.cycles } 50829
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0792.table, code := 35604655628625751858303168196028665921,
        encodes := Ra0792.tableCode_eq ▸ encodesTable_tableCode Ra0792.cycles } 50892
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0793.table, code := 35604655628625751858303168198176149569,
        encodes := Ra0793.tableCode_eq ▸ encodesTable_tableCode Ra0793.cycles } 50893
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0794.table, code := 33028870736112434984376847519417897025,
        encodes := Ra0794.tableCode_eq ▸ encodesTable_tableCode Ra0794.cycles } 51016
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0795.table, code := 33028870736112434984376847521565380673,
        encodes := Ra0795.tableCode_eq ▸ encodesTable_tableCode Ra0795.cycles } 51017
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0796.table, code := 33028951865753267442697845160309690433,
        encodes := Ra0796.tableCode_eq ▸ encodesTable_tableCode Ra0796.cycles } 51020
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0797.table, code := 33028951865753267442697845162457174081,
        encodes := Ra0797.tableCode_eq ▸ encodesTable_tableCode Ra0797.cycles } 51021
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0798.table, code := 35687651248731148048596138481902948417,
        encodes := Ra0798.tableCode_eq ▸ encodesTable_tableCode Ra0798.cycles } 51145
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0799.table, code := 35687732378371980506917136120647258177,
        encodes := Ra0799.tableCode_eq ▸ encodesTable_tableCode Ra0799.cycles } 51148
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0800.table, code := 35687732378371980506917136122794741825,
        encodes := Ra0800.tableCode_eq ▸ encodesTable_tableCode Ra0800.cycles } 51149
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0801.table, code := 35690409656519454064964744242566271041,
        encodes := Ra0801.tableCode_eq ▸ encodesTable_tableCode Ra0801.cycles } 51187
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0802.table, code := 35690490786160286523285741881310580801,
        encodes := Ra0802.tableCode_eq ▸ encodesTable_tableCode Ra0802.cycles } 51190
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0803.table, code := 35690490786160286523285741883458064449,
        encodes := Ra0803.tableCode_eq ▸ encodesTable_tableCode Ra0803.cycles } 51191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0804.table, code := 35690409656519454067342644910242402369,
        encodes := Ra0804.tableCode_eq ▸ encodesTable_tableCode Ra0804.cycles } 51193
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0805.table, code := 35690409656519454067414702577294774337,
        encodes := Ra0805.tableCode_eq ▸ encodesTable_tableCode Ra0805.cycles } 51195
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0806.table, code := 35690490786160286525663642551134195777,
        encodes := Ra0806.tableCode_eq ▸ encodesTable_tableCode Ra0806.cycles } 51197
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0807.table, code := 35690490786160286525735700216039084097,
        encodes := Ra0807.tableCode_eq ▸ encodesTable_tableCode Ra0807.cycles } 51198
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0808.table, code := 35690490786160286525735700218186567745,
        encodes := Ra0808.tableCode_eq ▸ encodesTable_tableCode Ra0808.cycles } 51199
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0809.table, code := 35706067835037468925164961950939222081,
        encodes := Ra0809.tableCode_eq ▸ encodesTable_tableCode Ra0809.cycles } 51711
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0810.table, code := 35706067835037468929776647969366609985,
        encodes := Ra0810.tableCode_eq ▸ encodesTable_tableCode Ra0810.cycles } 52223
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0811.table, code := 35708014867281168596356674459688767553,
        encodes := Ra0811.tableCode_eq ▸ encodesTable_tableCode Ra0811.cycles } 52637
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0812.table, code := 35708014867281168596428732124593655873,
        encodes := Ra0812.tableCode_eq ▸ encodesTable_tableCode Ra0812.cycles } 52638
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0813.table, code := 35708014867281168596428732126741139521,
        encodes := Ra0813.tableCode_eq ▸ encodesTable_tableCode Ra0813.cycles } 52639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0814.table, code := 35710529886074439329203748541894496321,
        encodes := Ra0814.tableCode_eq ▸ encodesTable_tableCode Ra0814.cycles } 52665
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0815.table, code := 35710529886074439329275806208946868289,
        encodes := Ra0815.tableCode_eq ▸ encodesTable_tableCode Ra0815.cycles } 52667
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0816.table, code := 35710611015715271787524746182786289729,
        encodes := Ra0816.tableCode_eq ▸ encodesTable_tableCode Ra0816.cycles } 52669
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0817.table, code := 35710611015715271787596803847691178049,
        encodes := Ra0817.tableCode_eq ▸ encodesTable_tableCode Ra0817.cycles } 52670
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0818.table, code := 35710611015715271787596803849838661697,
        encodes := Ra0818.tableCode_eq ▸ encodesTable_tableCode Ra0818.cycles } 52671
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0819.table, code := 35708663983616647964074587161366892609,
        encodes := Ra0819.tableCode_eq ▸ encodesTable_tableCode Ra0819.cycles } 52701
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0820.table, code := 35708663983616647964146644826271780929,
        encodes := Ra0820.tableCode_eq ▸ encodesTable_tableCode Ra0820.cycles } 52702
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0821.table, code := 35708663983616647964146644828419264577,
        encodes := Ra0821.tableCode_eq ▸ encodesTable_tableCode Ra0821.cycles } 52703
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0822.table, code := 35711179002409918696921661243572621377,
        encodes := Ra0822.tableCode_eq ▸ encodesTable_tableCode Ra0822.cycles } 52729
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0823.table, code := 35711179002409918696993718910624993345,
        encodes := Ra0823.tableCode_eq ▸ encodesTable_tableCode Ra0823.cycles } 52731
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0824.table, code := 35711260132050751155242658884464414785,
        encodes := Ra0824.tableCode_eq ▸ encodesTable_tableCode Ra0824.cycles } 52733
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0825.table, code := 35711260132050751155314716549369303105,
        encodes := Ra0825.tableCode_eq ▸ encodesTable_tableCode Ra0825.cycles } 52734
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0826.table, code := 35711260132050751155314716551516786753,
        encodes := Ra0826.tableCode_eq ▸ encodesTable_tableCode Ra0826.cycles } 52735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0827.table, code := 35708014867281168600968360478116155457,
        encodes := Ra0827.tableCode_eq ▸ encodesTable_tableCode Ra0827.cycles } 53149
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0828.table, code := 35708014867281168601040418143021043777,
        encodes := Ra0828.tableCode_eq ▸ encodesTable_tableCode Ra0828.cycles } 53150
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0829.table, code := 35708014867281168601040418145168527425,
        encodes := Ra0829.tableCode_eq ▸ encodesTable_tableCode Ra0829.cycles } 53151
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0830.table, code := 35710529886074439331437533892645752897,
        encodes := Ra0830.tableCode_eq ▸ encodesTable_tableCode Ra0830.cycles } 53171
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0831.table, code := 35710611015715271789758531531390062657,
        encodes := Ra0831.tableCode_eq ▸ encodesTable_tableCode Ra0831.cycles } 53174
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0832.table, code := 35710611015715271789758531533537546305,
        encodes := Ra0832.tableCode_eq ▸ encodesTable_tableCode Ra0832.cycles } 53175
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (768 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (768 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
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

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models012
