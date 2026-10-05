/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0705
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0706
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0707
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0708
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0709
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0710
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0711
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0712
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0713
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0714
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0715
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0716
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0717
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0718
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0719
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0720
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0721
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0722
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0723
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0724
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0725
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0726
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0727
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0728
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0729
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0730
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0731
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0732
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0733
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0734
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0735
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0736
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0737
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0738
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0739
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0740
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0741
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0742
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0743
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0744
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0745
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0746
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0747
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0748
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0749
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0750
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0751
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0752
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0753
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0754
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0755
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0756
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0757
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0758
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0759
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0760
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0761
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0762
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0763
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0764
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0765
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0766
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0767
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0768

/-!
# Certified models 705–768 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models011

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0705.table, code := 9588813633566398049333632936075071553,
        encodes := Ra0705.tableCode_eq ▸ encodesTable_tableCode Ra0705.cycles } 124910
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0706.table, code := 9588813633566398049333632938222555201,
        encodes := Ra0706.tableCode_eq ▸ encodesTable_tableCode Ra0706.cycles } 124911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0707.table, code := 9588732503925565593462593632059265089,
        encodes := Ra0707.tableCode_eq ▸ encodesTable_tableCode Ra0707.cycles } 124915
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0708.table, code := 9588732503927983445029767430969495617,
        encodes := Ra0708.tableCode_eq ▸ encodesTable_tableCode Ra0708.cycles } 124917
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0709.table, code := 9588732503927983445101825095874383937,
        encodes := Ra0709.tableCode_eq ▸ encodesTable_tableCode Ra0709.cycles } 124918
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0710.table, code := 9588732503927983445101825098021867585,
        encodes := Ra0710.tableCode_eq ▸ encodesTable_tableCode Ra0710.cycles } 124919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0711.table, code := 9588813633563980200072302139936084033,
        encodes := Ra0711.tableCode_eq ▸ encodesTable_tableCode Ra0711.cycles } 124921
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0712.table, code := 9588813633563980200144359804840972353,
        encodes := Ra0712.tableCode_eq ▸ encodesTable_tableCode Ra0712.cycles } 124922
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0713.table, code := 9588813633563980200144359806988456001,
        encodes := Ra0713.tableCode_eq ▸ encodesTable_tableCode Ra0713.cycles } 124923
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0714.table, code := 9588813633566398051711533605898686529,
        encodes := Ra0714.tableCode_eq ▸ encodesTable_tableCode Ra0714.cycles } 124925
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0715.table, code := 9588813633566398051783591270803574849,
        encodes := Ra0715.tableCode_eq ▸ encodesTable_tableCode Ra0715.cycles } 124926
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0716.table, code := 9588813633566398051783591272951058497,
        encodes := Ra0716.tableCode_eq ▸ encodesTable_tableCode Ra0716.cycles } 124927
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0717.table, code := 9588732504000519072317072445641330753,
        encodes := Ra0717.tableCode_eq ▸ encodesTable_tableCode Ra0717.cycles } 125909
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0718.table, code := 9588732504000519072389130110546219073,
        encodes := Ra0718.tableCode_eq ▸ encodesTable_tableCode Ra0718.cycles } 125910
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0719.table, code := 9588732504000519072389130112693702721,
        encodes := Ra0719.tableCode_eq ▸ encodesTable_tableCode Ra0719.cycles } 125911
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0720.table, code := 9588813633638933678998838620570521665,
        encodes := Ra0720.tableCode_eq ▸ encodesTable_tableCode Ra0720.cycles } 125917
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0721.table, code := 9588813633638933679070896285475409985,
        encodes := Ra0721.tableCode_eq ▸ encodesTable_tableCode Ra0721.cycles } 125918
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0722.table, code := 9588813633638933679070896287622893633,
        encodes := Ra0722.tableCode_eq ▸ encodesTable_tableCode Ra0722.cycles } 125919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0723.table, code := 9588732504082726102126078573435686977,
        encodes := Ra0723.tableCode_eq ▸ encodesTable_tableCode Ra0723.cycles } 125941
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0724.table, code := 9588732504082726102198136238340575297,
        encodes := Ra0724.tableCode_eq ▸ encodesTable_tableCode Ra0724.cycles } 125942
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0725.table, code := 9588732504082726102198136240488058945,
        encodes := Ra0725.tableCode_eq ▸ encodesTable_tableCode Ra0725.cycles } 125943
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0726.table, code := 9588813633718722857168613282402275393,
        encodes := Ra0726.tableCode_eq ▸ encodesTable_tableCode Ra0726.cycles } 125945
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0727.table, code := 9588813633718722857240670947307163713,
        encodes := Ra0727.tableCode_eq ▸ encodesTable_tableCode Ra0727.cycles } 125946
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0728.table, code := 9588813633718722857240670949454647361,
        encodes := Ra0728.tableCode_eq ▸ encodesTable_tableCode Ra0728.cycles } 125947
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0729.table, code := 9588813633721140708807844748364877889,
        encodes := Ra0729.tableCode_eq ▸ encodesTable_tableCode Ra0729.cycles } 125949
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0730.table, code := 9588813633721140708879902413269766209,
        encodes := Ra0730.tableCode_eq ▸ encodesTable_tableCode Ra0730.cycles } 125950
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0731.table, code := 9588813633721140708879902415417249857,
        encodes := Ra0731.tableCode_eq ▸ encodesTable_tableCode Ra0731.cycles } 125951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0732.table, code := 9588732504000519074550857796392587329,
        encodes := Ra0732.tableCode_eq ▸ encodesTable_tableCode Ra0732.cycles } 126919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0733.table, code := 9588813633638933681232623969174294593,
        encodes := Ra0733.tableCode_eq ▸ encodesTable_tableCode Ra0733.cycles } 126926
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0734.table, code := 9588813633638933681232623971321778241,
        encodes := Ra0734.tableCode_eq ▸ encodesTable_tableCode Ra0734.cycles } 126927
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0735.table, code := 9588732504000519077000816131121090625,
        encodes := Ra0735.tableCode_eq ▸ encodesTable_tableCode Ra0735.cycles } 126935
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0736.table, code := 9588813633638933683610524638997909569,
        encodes := Ra0736.tableCode_eq ▸ encodesTable_tableCode Ra0736.cycles } 126941
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0737.table, code := 9588813633638933683682582303902797889,
        encodes := Ra0737.tableCode_eq ▸ encodesTable_tableCode Ra0737.cycles } 126942
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0738.table, code := 9588813633638933683682582306050281537,
        encodes := Ra0738.tableCode_eq ▸ encodesTable_tableCode Ra0738.cycles } 126943
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0739.table, code := 9588732504082726104359863924186943553,
        encodes := Ra0739.tableCode_eq ▸ encodesTable_tableCode Ra0739.cycles } 126951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0740.table, code := 9588813633718722859402398631006048321,
        encodes := Ra0740.tableCode_eq ▸ encodesTable_tableCode Ra0740.cycles } 126954
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0741.table, code := 9588813633718722859402398633153531969,
        encodes := Ra0741.tableCode_eq ▸ encodesTable_tableCode Ra0741.cycles } 126955
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0742.table, code := 9588813633721140711041630096968650817,
        encodes := Ra0742.tableCode_eq ▸ encodesTable_tableCode Ra0742.cycles } 126958
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0743.table, code := 9588813633721140711041630099116134465,
        encodes := Ra0743.tableCode_eq ▸ encodesTable_tableCode Ra0743.cycles } 126959
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0744.table, code := 9588732504082726106809822258915446849,
        encodes := Ra0744.tableCode_eq ▸ encodesTable_tableCode Ra0744.cycles } 126967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0745.table, code := 9588813633718722861780299300829663297,
        encodes := Ra0745.tableCode_eq ▸ encodesTable_tableCode Ra0745.cycles } 126969
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0746.table, code := 9588813633718722861852356965734551617,
        encodes := Ra0746.tableCode_eq ▸ encodesTable_tableCode Ra0746.cycles } 126970
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0747.table, code := 9588813633718722861852356967882035265,
        encodes := Ra0747.tableCode_eq ▸ encodesTable_tableCode Ra0747.cycles } 126971
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0748.table, code := 9588813633721140713419530766792265793,
        encodes := Ra0748.tableCode_eq ▸ encodesTable_tableCode Ra0748.cycles } 126973
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0749.table, code := 9588813633721140713491588431697154113,
        encodes := Ra0749.tableCode_eq ▸ encodesTable_tableCode Ra0749.cycles } 126974
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0750.table, code := 9588813633721140713491588433844637761,
        encodes := Ra0750.tableCode_eq ▸ encodesTable_tableCode Ra0750.cycles } 126975
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0751.table, code := 9591247522716420774964873260647583809,
        encodes := Ra0751.tableCode_eq ▸ encodesTable_tableCode Ra0751.cycles } 127929
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0752.table, code := 9591247522716420775036930925552472129,
        encodes := Ra0752.tableCode_eq ▸ encodesTable_tableCode Ra0752.cycles } 127930
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0753.table, code := 9591247522716420775036930927699955777,
        encodes := Ra0753.tableCode_eq ▸ encodesTable_tableCode Ra0753.cycles } 127931
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0754.table, code := 9591247522718838626604104726610186305,
        encodes := Ra0754.tableCode_eq ▸ encodesTable_tableCode Ra0754.cycles } 127933
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0755.table, code := 9591247522718838626676162391515074625,
        encodes := Ra0755.tableCode_eq ▸ encodesTable_tableCode Ra0755.cycles } 127934
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0756.table, code := 9591247522718838626676162393662558273,
        encodes := Ra0756.tableCode_eq ▸ encodesTable_tableCode Ra0756.cycles } 127935
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0757.table, code := 9594005930422519763902373561192681537,
        encodes := Ra0757.tableCode_eq ▸ encodesTable_tableCode Ra0757.cycles } 127993
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0758.table, code := 9594005930422519763974431226097569857,
        encodes := Ra0758.tableCode_eq ▸ encodesTable_tableCode Ra0758.cycles } 127994
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0759.table, code := 9594005930422519763974431228245053505,
        encodes := Ra0759.tableCode_eq ▸ encodesTable_tableCode Ra0759.cycles } 127995
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0760.table, code := 9594005930424937615541605027155284033,
        encodes := Ra0760.tableCode_eq ▸ encodesTable_tableCode Ra0760.cycles } 127997
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0761.table, code := 9594005930424937615613662692060172353,
        encodes := Ra0761.tableCode_eq ▸ encodesTable_tableCode Ra0761.cycles } 127998
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0762.table, code := 9594005930424937615613662694207656001,
        encodes := Ra0762.tableCode_eq ▸ encodesTable_tableCode Ra0762.cycles } 127999
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0763.table, code := 9591247522716420777198658611398840385,
        encodes := Ra0763.tableCode_eq ▸ encodesTable_tableCode Ra0763.cycles } 128939
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0764.table, code := 9591247522718838628837890075213959233,
        encodes := Ra0764.tableCode_eq ▸ encodesTable_tableCode Ra0764.cycles } 128942
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0765.table, code := 9591247522718838628837890077361442881,
        encodes := Ra0765.tableCode_eq ▸ encodesTable_tableCode Ra0765.cycles } 128943
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0766.table, code := 9591247522716420779648616946127343681,
        encodes := Ra0766.tableCode_eq ▸ encodesTable_tableCode Ra0766.cycles } 128955
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0767.table, code := 9591247522718838631215790745037574209,
        encodes := Ra0767.tableCode_eq ▸ encodesTable_tableCode Ra0767.cycles } 128957
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0768.table, code := 9591247522718838631287848409942462529,
        encodes := Ra0768.tableCode_eq ▸ encodesTable_tableCode Ra0768.cycles } 128958
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (704 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (704 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
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

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models011
