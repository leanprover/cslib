/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0705
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0706
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0707
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0708
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0709
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0710
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0711
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0712
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0713
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0714
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0715
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0716
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0717
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0718
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0719
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0720
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0721
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0722
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0723
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0724
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0725
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0726
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0727
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0728
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0729
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0730
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0731
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0732
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0733
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0734
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0735
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0736
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0737
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0738
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0739
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0740
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0741
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0742
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0743
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0744
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0745
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0746
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0747
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0748
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0749
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0750
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0751
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0752
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0753
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0754
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0755
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0756
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0757
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0758
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0759
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0760
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0761
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0762
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0763
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0764
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0765
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0766
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0767
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0768

/-!
# Certified models 705–768 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models011

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0705.table, code := 13607651444781275956583038815643635777,
        encodes := Ra0705.tableCode_eq ▸ encodesTable_tableCode Ra0705.cycles } 44030
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0706.table, code := 13607651444781275956583038817791119425,
        encodes := Ra0706.tableCode_eq ▸ encodesTable_tableCode Ra0706.cycles } 44031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0707.table, code := 13612762612153725721350151424320999489,
        encodes := Ra0707.tableCode_eq ▸ encodesTable_tableCode Ra0707.cycles } 44531
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0708.table, code := 13612843741794558179671149063065309249,
        encodes := Ra0708.tableCode_eq ▸ encodesTable_tableCode Ra0708.cycles } 44534
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0709.table, code := 13612843741794558179671149065212792897,
        encodes := Ra0709.tableCode_eq ▸ encodesTable_tableCode Ra0709.cycles } 44535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0710.table, code := 13612762612153725723728052091997130817,
        encodes := Ra0710.tableCode_eq ▸ encodesTable_tableCode Ra0710.cycles } 44537
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0711.table, code := 13612762612153725723800109759049502785,
        encodes := Ra0711.tableCode_eq ▸ encodesTable_tableCode Ra0711.cycles } 44539
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0712.table, code := 13612843741794558182049049730741440577,
        encodes := Ra0712.tableCode_eq ▸ encodesTable_tableCode Ra0712.cycles } 44540
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0713.table, code := 13612843741794558182049049732888924225,
        encodes := Ra0713.tableCode_eq ▸ encodesTable_tableCode Ra0713.cycles } 44541
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0714.table, code := 13612843741794558182121107397793812545,
        encodes := Ra0714.tableCode_eq ▸ encodesTable_tableCode Ra0714.cycles } 44542
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0715.table, code := 13612843741794558182121107399941296193,
        encodes := Ra0715.tableCode_eq ▸ encodesTable_tableCode Ra0715.cycles } 44543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0716.table, code := 13612762612153725725961837442748387393,
        encodes := Ra0716.tableCode_eq ▸ encodesTable_tableCode Ra0716.cycles } 45043
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0717.table, code := 13612843741794558184282835081492697153,
        encodes := Ra0717.tableCode_eq ▸ encodesTable_tableCode Ra0717.cycles } 45046
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0718.table, code := 13612843741794558184282835083640180801,
        encodes := Ra0718.tableCode_eq ▸ encodesTable_tableCode Ra0718.cycles } 45047
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0719.table, code := 13612762612153725728339738110424518721,
        encodes := Ra0719.tableCode_eq ▸ encodesTable_tableCode Ra0719.cycles } 45049
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0720.table, code := 13612762612153725728411795777476890689,
        encodes := Ra0720.tableCode_eq ▸ encodesTable_tableCode Ra0720.cycles } 45051
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0721.table, code := 13612843741794558186660735749168828481,
        encodes := Ra0721.tableCode_eq ▸ encodesTable_tableCode Ra0721.cycles } 45052
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0722.table, code := 13612843741794558186660735751316312129,
        encodes := Ra0722.tableCode_eq ▸ encodesTable_tableCode Ra0722.cycles } 45053
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0723.table, code := 13612843741794558186732793416221200449,
        encodes := Ra0723.tableCode_eq ▸ encodesTable_tableCode Ra0723.cycles } 45054
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0724.table, code := 13612843741794558186732793418368684097,
        encodes := Ra0724.tableCode_eq ▸ encodesTable_tableCode Ra0724.cycles } 45055
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0725.table, code := 18934948027208749310584571698985832513,
        encodes := Ra0725.tableCode_eq ▸ encodesTable_tableCode Ra0725.cycles } 47612
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0726.table, code := 18934948027208749310584571701133316161,
        encodes := Ra0726.tableCode_eq ▸ encodesTable_tableCode Ra0726.cycles } 47613
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0727.table, code := 18934948027208749310656629366038204481,
        encodes := Ra0727.tableCode_eq ▸ encodesTable_tableCode Ra0727.cycles } 47614
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0728.table, code := 18934948027208749310656629368185688129,
        encodes := Ra0728.tableCode_eq ▸ encodesTable_tableCode Ra0728.cycles } 47615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0729.table, code := 18934866897567916854497359410992779329,
        encodes := Ra0729.tableCode_eq ▸ encodesTable_tableCode Ra0729.cycles } 48115
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0730.table, code := 18934948027208749312818357049737089089,
        encodes := Ra0730.tableCode_eq ▸ encodesTable_tableCode Ra0730.cycles } 48118
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0731.table, code := 18934948027208749312818357051884572737,
        encodes := Ra0731.tableCode_eq ▸ encodesTable_tableCode Ra0731.cycles } 48119
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0732.table, code := 18934866897567916856947317745721282625,
        encodes := Ra0732.tableCode_eq ▸ encodesTable_tableCode Ra0732.cycles } 48123
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0733.table, code := 18934948027208749315196257717413220417,
        encodes := Ra0733.tableCode_eq ▸ encodesTable_tableCode Ra0733.cycles } 48124
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0734.table, code := 18934948027208749315196257719560704065,
        encodes := Ra0734.tableCode_eq ▸ encodesTable_tableCode Ra0734.cycles } 48125
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0735.table, code := 18934948027208749315268315384465592385,
        encodes := Ra0735.tableCode_eq ▸ encodesTable_tableCode Ra0735.cycles } 48126
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0736.table, code := 18934948027208749315268315386613076033,
        encodes := Ra0736.tableCode_eq ▸ encodesTable_tableCode Ra0736.cycles } 48127
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0737.table, code := 18937381916433725522059877538276315201,
        encodes := Ra0737.tableCode_eq ▸ encodesTable_tableCode Ra0737.cycles } 48590
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0738.table, code := 18937381916433725522059877540423798849,
        encodes := Ra0738.tableCode_eq ▸ encodesTable_tableCode Ra0738.cycles } 48591
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0739.table, code := 18937544175787928347188353908789743681,
        encodes := Ra0739.tableCode_eq ▸ encodesTable_tableCode Ra0739.cycles } 48598
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0740.table, code := 18937544175787928347188353910937227329,
        encodes := Ra0740.tableCode_eq ▸ encodesTable_tableCode Ra0740.cycles } 48599
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0741.table, code := 18937544175787928349566254578613358657,
        encodes := Ra0741.tableCode_eq ▸ encodesTable_tableCode Ra0741.cycles } 48605
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0742.table, code := 18937544175787928349638312243518246977,
        encodes := Ra0742.tableCode_eq ▸ encodesTable_tableCode Ra0742.cycles } 48606
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0743.table, code := 18937544175787928349638312245665730625,
        encodes := Ra0743.tableCode_eq ▸ encodesTable_tableCode Ra0743.cycles } 48607
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0744.table, code := 18940140324222031538356425631887265857,
        encodes := Ra0744.tableCode_eq ▸ encodesTable_tableCode Ra0744.cycles } 48630
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0745.table, code := 18940140324222031538356425634034749505,
        encodes := Ra0745.tableCode_eq ▸ encodesTable_tableCode Ra0745.cycles } 48631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0746.table, code := 18940140324222031540734326301710880833,
        encodes := Ra0746.tableCode_eq ▸ encodesTable_tableCode Ra0746.cycles } 48637
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0747.table, code := 18940140324222031540806383966615769153,
        encodes := Ra0747.tableCode_eq ▸ encodesTable_tableCode Ra0747.cycles } 48638
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0748.table, code := 18940140324222031540806383968763252801,
        encodes := Ra0748.tableCode_eq ▸ encodesTable_tableCode Ra0748.cycles } 48639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0749.table, code := 18937381916433725526671563558851186753,
        encodes := Ra0749.tableCode_eq ▸ encodesTable_tableCode Ra0749.cycles } 49103
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0750.table, code := 18937544175787928351800039929364615233,
        encodes := Ra0750.tableCode_eq ▸ encodesTable_tableCode Ra0750.cycles } 49111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0751.table, code := 18937544175787928354249998264093118529,
        encodes := Ra0751.tableCode_eq ▸ encodesTable_tableCode Ra0751.cycles } 49119
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0752.table, code := 18940140324222031542968111652462137409,
        encodes := Ra0752.tableCode_eq ▸ encodesTable_tableCode Ra0752.cycles } 49143
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0753.table, code := 18940140324222031545418069987190640705,
        encodes := Ra0753.tableCode_eq ▸ encodesTable_tableCode Ra0753.cycles } 49151
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0754.table, code := 35685298489147004290974259599181615169,
        encodes := Ra0754.tableCode_eq ▸ encodesTable_tableCode Ra0754.cycles } 49663
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0755.table, code := 35685298489147004295585945617609003073,
        encodes := Ra0755.tableCode_eq ▸ encodesTable_tableCode Ra0755.cycles } 50175
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0756.table, code := 32945225999671559419376377847909453889,
        encodes := Ra0756.tableCode_eq ▸ encodesTable_tableCode Ra0756.cycles } 50182
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0757.table, code := 32945225999671559419376377850056937537,
        encodes := Ra0757.tableCode_eq ▸ encodesTable_tableCode Ra0757.cycles } 50183
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0758.table, code := 32945225999671559421754278517733068865,
        encodes := Ra0758.tableCode_eq ▸ encodesTable_tableCode Ra0758.cycles } 50189
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0759.table, code := 32945225999671559421826336182637957185,
        encodes := Ra0759.tableCode_eq ▸ encodesTable_tableCode Ra0759.cycles } 50190
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0760.table, code := 32945225999671559421826336184785440833,
        encodes := Ra0760.tableCode_eq ▸ encodesTable_tableCode Ra0760.cycles } 50191
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0761.table, code := 32947984407459865438050826609196535873,
        encodes := Ra0761.tableCode_eq ▸ encodesTable_tableCode Ra0761.cycles } 50228
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0762.table, code := 32947984407459865440500784946072522817,
        encodes := Ra0762.tableCode_eq ▸ encodesTable_tableCode Ra0762.cycles } 50237
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0763.table, code := 32947984407459865440572842610977411137,
        encodes := Ra0763.tableCode_eq ▸ encodesTable_tableCode Ra0763.cycles } 50238
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0764.table, code := 32947984407459865440572842613124894785,
        encodes := Ra0764.tableCode_eq ▸ encodesTable_tableCode Ra0764.cycles } 50239
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0765.table, code := 35603925382649440027652571835031359553,
        encodes := Ra0765.tableCode_eq ▸ encodesTable_tableCode Ra0765.cycles } 50312
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0766.table, code := 35604006512290272485973569475923152961,
        encodes := Ra0766.tableCode_eq ▸ encodesTable_tableCode Ra0766.cycles } 50316
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0767.table, code := 35604006512290272485973569478070636609,
        encodes := Ra0767.tableCode_eq ▸ encodesTable_tableCode Ra0767.cycles } 50317
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0768.table, code := 35604655628625751853691482177601278017,
        encodes := Ra0768.tableCode_eq ▸ encodesTable_tableCode Ra0768.cycles } 50380
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (704 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (704 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (704 + i.val) 0 ≤ Data.profiles (704 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (704 + i.val) 0 = Data.canonicalMask (704 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (704 + i.val) < Data.canonicalMask (704 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (704 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models011
