/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0577
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0578
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0579
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0580
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0581
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0582
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0583
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0584
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0585
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0586
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0587
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0588
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0589
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0590
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0591
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0592
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0593
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0594
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0595
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0596
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0597
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0598
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0599
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0600
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0601
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0602
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0603
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0604
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0605
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0606
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0607
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0608
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0609
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0610
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0611
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0612
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0613
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0614
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0615
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0616
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0617
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0618
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0619
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0620
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0621
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0622
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0623
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0624
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0625
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0626
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0627
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0628
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0629
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0630
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0631
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0632
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0633
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0634
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0635
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0636
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0637
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0638
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0639
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0640

/-!
# Certified models 577–640 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models009

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0577.table, code := 30562935523372887038869171324332544065,
        encodes := Ra0577.tableCode_eq ▸ encodesTable_tableCode Ra0577.cycles } 31687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0578.table, code := 30562854393732054582998132018169253953,
        encodes := Ra0578.tableCode_eq ▸ encodesTable_tableCode Ra0578.cycles } 31691
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0579.table, code := 30565612801520360599222622444727832641,
        encodes := Ra0579.tableCode_eq ▸ encodesTable_tableCode Ra0579.cycles } 31729
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0580.table, code := 30565612801520360599294680111780204609,
        encodes := Ra0580.tableCode_eq ▸ encodesTable_tableCode Ra0580.cycles } 31731
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0581.table, code := 30565693931161193057543620083472142401,
        encodes := Ra0581.tableCode_eq ▸ encodesTable_tableCode Ra0581.cycles } 31732
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0582.table, code := 30565693931161193057543620085619626049,
        encodes := Ra0582.tableCode_eq ▸ encodesTable_tableCode Ra0582.cycles } 31733
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0583.table, code := 30565693931161193057615677750524514369,
        encodes := Ra0583.tableCode_eq ▸ encodesTable_tableCode Ra0583.cycles } 31734
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0584.table, code := 30565693931161193057615677752671998017,
        encodes := Ra0584.tableCode_eq ▸ encodesTable_tableCode Ra0584.cycles } 31735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0585.table, code := 30565612801520360601744638446508707905,
        encodes := Ra0585.tableCode_eq ▸ encodesTable_tableCode Ra0585.cycles } 31739
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0586.table, code := 30565693931161193059993578418200645697,
        encodes := Ra0586.tableCode_eq ▸ encodesTable_tableCode Ra0586.cycles } 31740
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0587.table, code := 30565693931161193059993578420348129345,
        encodes := Ra0587.tableCode_eq ▸ encodesTable_tableCode Ra0587.cycles } 31741
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0588.table, code := 30565693931161193060065636085253017665,
        encodes := Ra0588.tableCode_eq ▸ encodesTable_tableCode Ra0588.cycles } 31742
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0589.table, code := 30565693931161193060065636087400501313,
        encodes := Ra0589.tableCode_eq ▸ encodesTable_tableCode Ra0589.cycles } 31743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0590.table, code := 30568127820386169266857198239063740481,
        encodes := Ra0590.tableCode_eq ▸ encodesTable_tableCode Ra0590.cycles } 32206
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0591.table, code := 30568127820386169266857198241211224129,
        encodes := Ra0591.tableCode_eq ▸ encodesTable_tableCode Ra0591.cycles } 32207
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0592.table, code := 30568290079740372091985674609577168961,
        encodes := Ra0592.tableCode_eq ▸ encodesTable_tableCode Ra0592.cycles } 32214
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0593.table, code := 30568290079740372091985674611724652609,
        encodes := Ra0593.tableCode_eq ▸ encodesTable_tableCode Ra0593.cycles } 32215
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0594.table, code := 30568290079740372094363575279400783937,
        encodes := Ra0594.tableCode_eq ▸ encodesTable_tableCode Ra0594.cycles } 32221
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0595.table, code := 30568290079740372094435632944305672257,
        encodes := Ra0595.tableCode_eq ▸ encodesTable_tableCode Ra0595.cycles } 32222
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0596.table, code := 30568290079740372094435632946453155905,
        encodes := Ra0596.tableCode_eq ▸ encodesTable_tableCode Ra0596.cycles } 32223
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0597.table, code := 30570886228174475283081688665622319169,
        encodes := Ra0597.tableCode_eq ▸ encodesTable_tableCode Ra0597.cycles } 32244
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0598.table, code := 30570886228174475283081688667769802817,
        encodes := Ra0598.tableCode_eq ▸ encodesTable_tableCode Ra0598.cycles } 32245
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0599.table, code := 30570886228174475283153746332674691137,
        encodes := Ra0599.tableCode_eq ▸ encodesTable_tableCode Ra0599.cycles } 32246
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0600.table, code := 30570886228174475283153746334822174785,
        encodes := Ra0600.tableCode_eq ▸ encodesTable_tableCode Ra0600.cycles } 32247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0601.table, code := 30570886228174475285531647002498306113,
        encodes := Ra0601.tableCode_eq ▸ encodesTable_tableCode Ra0601.cycles } 32253
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0602.table, code := 30570886228174475285603704667403194433,
        encodes := Ra0602.tableCode_eq ▸ encodesTable_tableCode Ra0602.cycles } 32254
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0603.table, code := 30570886228174475285603704669550678081,
        encodes := Ra0603.tableCode_eq ▸ encodesTable_tableCode Ra0603.cycles } 32255
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0604.table, code := 30568127820386169271468884259638612033,
        encodes := Ra0604.tableCode_eq ▸ encodesTable_tableCode Ra0604.cycles } 32719
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0605.table, code := 30568290079740372096597360630152040513,
        encodes := Ra0605.tableCode_eq ▸ encodesTable_tableCode Ra0605.cycles } 32727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0606.table, code := 30568290079740372099047318964880543809,
        encodes := Ra0606.tableCode_eq ▸ encodesTable_tableCode Ra0606.cycles } 32735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0607.table, code := 30570886228174475287693374686197190721,
        encodes := Ra0607.tableCode_eq ▸ encodesTable_tableCode Ra0607.cycles } 32757
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0608.table, code := 30570886228174475287765432353249562689,
        encodes := Ra0608.tableCode_eq ▸ encodesTable_tableCode Ra0608.cycles } 32759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0609.table, code := 30570886228174475290215390687978065985,
        encodes := Ra0609.tableCode_eq ▸ encodesTable_tableCode Ra0609.cycles } 32767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0610.table, code := 13420728599108192934380398017765445697,
        encodes := Ra0610.tableCode_eq ▸ encodesTable_tableCode Ra0610.cycles } 33279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0611.table, code := 13420728599108192938992084036192833601,
        encodes := Ra0611.tableCode_eq ▸ encodesTable_tableCode Ra0611.cycles } 33791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0612.table, code := 10680656109632748062782516266493284417,
        encodes := Ra0612.tableCode_eq ▸ encodesTable_tableCode Ra0612.cycles } 33798
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0613.table, code := 10680656109632748062782516268640768065,
        encodes := Ra0613.tableCode_eq ▸ encodesTable_tableCode Ra0613.cycles } 33799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0614.table, code := 10680656109632748065160416936316899393,
        encodes := Ra0614.tableCode_eq ▸ encodesTable_tableCode Ra0614.cycles } 33805
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0615.table, code := 10680656109632748065232474601221787713,
        encodes := Ra0615.tableCode_eq ▸ encodesTable_tableCode Ra0615.cycles } 33806
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0616.table, code := 10680656109632748065232474603369271361,
        encodes := Ra0616.tableCode_eq ▸ encodesTable_tableCode Ra0616.cycles } 33807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0617.table, code := 10764300846073623623171299919574339649,
        encodes := Ra0617.tableCode_eq ▸ encodesTable_tableCode Ra0617.cycles } 34120
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0618.table, code := 10764300846073623623171299921721823297,
        encodes := Ra0618.tableCode_eq ▸ encodesTable_tableCode Ra0618.cycles } 34121
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0619.table, code := 13423162488333169145711588520803700801,
        encodes := Ra0619.tableCode_eq ▸ encodesTable_tableCode Ra0619.cycles } 34252
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0620.table, code := 13423162488333169145711588522951184449,
        encodes := Ra0620.tableCode_eq ▸ encodesTable_tableCode Ra0620.cycles } 34253
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0621.table, code := 13425920896121475162080194281467023425,
        encodes := Ra0621.tableCode_eq ▸ encodesTable_tableCode Ra0621.cycles } 34294
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0622.table, code := 13425920896121475162080194283614507073,
        encodes := Ra0622.tableCode_eq ▸ encodesTable_tableCode Ra0622.cycles } 34295
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0623.table, code := 13425920896121475164530152616195526721,
        encodes := Ra0623.tableCode_eq ▸ encodesTable_tableCode Ra0623.cycles } 34302
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0624.table, code := 13425920896121475164530152618343010369,
        encodes := Ra0624.tableCode_eq ▸ encodesTable_tableCode Ra0624.cycles } 34303
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0625.table, code := 10680656109632748067394202287068155969,
        encodes := Ra0625.tableCode_eq ▸ encodesTable_tableCode Ra0625.cycles } 34311
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0626.table, code := 10680656109632748069844160621796659265,
        encodes := Ra0626.tableCode_eq ▸ encodesTable_tableCode Ra0626.cycles } 34319
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0627.table, code := 10764300846073623627782985938001727553,
        encodes := Ra0627.tableCode_eq ▸ encodesTable_tableCode Ra0627.cycles } 34632
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0628.table, code := 10764300846073623627782985940149211201,
        encodes := Ra0628.tableCode_eq ▸ encodesTable_tableCode Ra0628.cycles } 34633
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0629.table, code := 13423162488333169150323274539231088705,
        encodes := Ra0629.tableCode_eq ▸ encodesTable_tableCode Ra0629.cycles } 34764
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0630.table, code := 13423162488333169150323274541378572353,
        encodes := Ra0630.tableCode_eq ▸ encodesTable_tableCode Ra0630.cycles } 34765
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0631.table, code := 13425920896121475166691880299894411329,
        encodes := Ra0631.tableCode_eq ▸ encodesTable_tableCode Ra0631.cycles } 34806
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0632.table, code := 13425920896121475166691880302041894977,
        encodes := Ra0632.tableCode_eq ▸ encodesTable_tableCode Ra0632.cycles } 34807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0633.table, code := 13425920896121475169141838634622914625,
        encodes := Ra0633.tableCode_eq ▸ encodesTable_tableCode Ra0633.cycles } 34814
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0634.table, code := 13425920896121475169141838636770398273,
        encodes := Ra0634.tableCode_eq ▸ encodesTable_tableCode Ra0634.cycles } 34815
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0635.table, code := 13441497944998657568571100369523052609,
        encodes := Ra0635.tableCode_eq ▸ encodesTable_tableCode Ra0635.cycles } 35327
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0636.table, code := 13441497944998657573182786387950440513,
        encodes := Ra0636.tableCode_eq ▸ encodesTable_tableCode Ra0636.cycles } 35839
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0637.table, code := 13446690242011939798720854967953133633,
        encodes := Ra0637.tableCode_eq ▸ encodesTable_tableCode Ra0637.cycles } 36350
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0638.table, code := 13446690242011939798720854970100617281,
        encodes := Ra0638.tableCode_eq ▸ encodesTable_tableCode Ra0638.cycles } 36351
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0639.table, code := 13446690242011939800882582651652018241,
        encodes := Ra0639.tableCode_eq ▸ encodesTable_tableCode Ra0639.cycles } 36854
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0640.table, code := 13446690242011939800882582653799501889,
        encodes := Ra0640.tableCode_eq ▸ encodesTable_tableCode Ra0640.cycles } 36855
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (576 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (576 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (576 + i.val) 0 ≤ Data.profiles (576 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (576 + i.val) 0 = Data.canonicalMask (576 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (576 + i.val) < Data.canonicalMask (576 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (576 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models009
