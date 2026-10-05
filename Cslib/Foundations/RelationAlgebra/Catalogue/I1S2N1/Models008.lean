/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0513
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0514
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0515
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0516
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0517
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0518
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0519
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0520
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0521
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0522
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0523
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0524
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0525
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0526
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0527
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0528
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0529
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0530
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0531
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0532
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0533
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0534
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0535
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0536
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0537
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0538
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0539
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0540
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0541
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0542
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0543
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0544
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0545
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0546
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0547
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0548
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0549
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0550
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0551
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0552
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0553
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0554
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0555
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0556
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0557
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0558
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0559
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0560
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0561
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0562
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0563
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0564
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0565
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0566
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0567
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0568
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0569
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0570
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0571
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0572
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0573
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0574
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0575
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0576

/-!
# Certified models 513–576 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models008

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0513.table, code := 22576858428326700615964603795173019713,
        encodes := Ra0513.tableCode_eq ▸ encodesTable_tableCode Ra0513.cycles } 27463
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0514.table, code := 22576777298685868160093564489009729601,
        encodes := Ra0514.tableCode_eq ▸ encodesTable_tableCode Ra0514.cycles } 27467
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0515.table, code := 25235557811304581221862897114618794049,
        encodes := Ra0515.tableCode_eq ▸ encodesTable_tableCode Ra0515.cycles } 27587
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0516.table, code := 25235638940945413680183894753363103809,
        encodes := Ra0516.tableCode_eq ▸ encodesTable_tableCode Ra0516.cycles } 27590
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0517.table, code := 25235638940945413680183894755510587457,
        encodes := Ra0517.tableCode_eq ▸ encodesTable_tableCode Ra0517.cycles } 27591
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0518.table, code := 25238316219092887242987304210634379329,
        encodes := Ra0518.tableCode_eq ▸ encodesTable_tableCode Ra0518.cycles } 27641
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0519.table, code := 25238316219092887243059361877686751297,
        encodes := Ra0519.tableCode_eq ▸ encodesTable_tableCode Ra0519.cycles } 27643
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0520.table, code := 25238397348733719701308301849378689089,
        encodes := Ra0520.tableCode_eq ▸ encodesTable_tableCode Ra0520.cycles } 27644
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0521.table, code := 25238397348733719701308301851526172737,
        encodes := Ra0521.tableCode_eq ▸ encodesTable_tableCode Ra0521.cycles } 27645
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0522.table, code := 25238397348733719701380359516431061057,
        encodes := Ra0522.tableCode_eq ▸ encodesTable_tableCode Ra0522.cycles } 27646
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0523.table, code := 25238397348733719701380359518578544705,
        encodes := Ra0523.tableCode_eq ▸ encodesTable_tableCode Ra0523.cycles } 27647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0524.table, code := 22582050725339982843952630709904216129,
        encodes := Ra0524.tableCode_eq ▸ encodesTable_tableCode Ra0524.cycles } 27982
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0525.table, code := 22582050725339982843952630712051699777,
        encodes := Ra0525.tableCode_eq ▸ encodesTable_tableCode Ra0525.cycles } 27983
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0526.table, code := 22582212984694185671531065415146147905,
        encodes := Ra0526.tableCode_eq ▸ encodesTable_tableCode Ra0526.cycles } 27998
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0527.table, code := 22582212984694185671531065417293631553,
        encodes := Ra0527.tableCode_eq ▸ encodesTable_tableCode Ra0527.cycles } 27999
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0528.table, code := 22584809133128288860177121136462794817,
        encodes := Ra0528.tableCode_eq ▸ encodesTable_tableCode Ra0528.cycles } 28020
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0529.table, code := 22584809133128288860177121138610278465,
        encodes := Ra0529.tableCode_eq ▸ encodesTable_tableCode Ra0529.cycles } 28021
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0530.table, code := 22584809133128288860249178803515166785,
        encodes := Ra0530.tableCode_eq ▸ encodesTable_tableCode Ra0530.cycles } 28022
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0531.table, code := 22584809133128288860249178805662650433,
        encodes := Ra0531.tableCode_eq ▸ encodesTable_tableCode Ra0531.cycles } 28023
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0532.table, code := 22584809133128288862627079473338781761,
        encodes := Ra0532.tableCode_eq ▸ encodesTable_tableCode Ra0532.cycles } 28029
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0533.table, code := 22584809133128288862699137138243670081,
        encodes := Ra0533.tableCode_eq ▸ encodesTable_tableCode Ra0533.cycles } 28030
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0534.table, code := 22584809133128288862699137140391153729,
        encodes := Ra0534.tableCode_eq ▸ encodesTable_tableCode Ra0534.cycles } 28031
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0535.table, code := 25240831237958695908171921670241783873,
        encodes := Ra0535.tableCode_eq ▸ encodesTable_tableCode Ra0535.cycles } 28110
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0536.table, code := 25240831237958695908171921672389267521,
        encodes := Ra0536.tableCode_eq ▸ encodesTable_tableCode Ra0536.cycles } 28111
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0537.table, code := 25243508516106169466075414458056052801,
        encodes := Ra0537.tableCode_eq ▸ encodesTable_tableCode Ra0537.cycles } 28145
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0538.table, code := 25243508516106169466147472125108424769,
        encodes := Ra0538.tableCode_eq ▸ encodesTable_tableCode Ra0538.cycles } 28147
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0539.table, code := 25243589645747001924396412096800362561,
        encodes := Ra0539.tableCode_eq ▸ encodesTable_tableCode Ra0539.cycles } 28148
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0540.table, code := 25243589645747001924396412098947846209,
        encodes := Ra0540.tableCode_eq ▸ encodesTable_tableCode Ra0540.cycles } 28149
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0541.table, code := 25243589645747001924468469763852734529,
        encodes := Ra0541.tableCode_eq ▸ encodesTable_tableCode Ra0541.cycles } 28150
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0542.table, code := 25243589645747001924468469766000218177,
        encodes := Ra0542.tableCode_eq ▸ encodesTable_tableCode Ra0542.cycles } 28151
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0543.table, code := 25243508516106169468525372792784556097,
        encodes := Ra0543.tableCode_eq ▸ encodesTable_tableCode Ra0543.cycles } 28153
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0544.table, code := 25243508516106169468597430459836928065,
        encodes := Ra0544.tableCode_eq ▸ encodesTable_tableCode Ra0544.cycles } 28155
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0545.table, code := 25243589645747001926846370431528865857,
        encodes := Ra0545.tableCode_eq ▸ encodesTable_tableCode Ra0545.cycles } 28156
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0546.table, code := 25243589645747001926846370433676349505,
        encodes := Ra0546.tableCode_eq ▸ encodesTable_tableCode Ra0546.cycles } 28157
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0547.table, code := 25243589645747001926918428098581237825,
        encodes := Ra0547.tableCode_eq ▸ encodesTable_tableCode Ra0547.cycles } 28158
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0548.table, code := 25243589645747001926918428100728721473,
        encodes := Ra0548.tableCode_eq ▸ encodesTable_tableCode Ra0548.cycles } 28159
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0549.table, code := 22582050725339982848564316730479087681,
        encodes := Ra0549.tableCode_eq ▸ encodesTable_tableCode Ra0549.cycles } 28495
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0550.table, code := 22582212984694185676142751435721019457,
        encodes := Ra0550.tableCode_eq ▸ encodesTable_tableCode Ra0550.cycles } 28511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0551.table, code := 22584809133128288864788807157037666369,
        encodes := Ra0551.tableCode_eq ▸ encodesTable_tableCode Ra0551.cycles } 28533
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0552.table, code := 22584809133128288864860864824090038337,
        encodes := Ra0552.tableCode_eq ▸ encodesTable_tableCode Ra0552.cycles } 28535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0553.table, code := 22584809133128288867310823158818541633,
        encodes := Ra0553.tableCode_eq ▸ encodesTable_tableCode Ra0553.cycles } 28543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0554.table, code := 25240831237958695912783607688669171777,
        encodes := Ra0554.tableCode_eq ▸ encodesTable_tableCode Ra0554.cycles } 28622
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0555.table, code := 25240831237958695912783607690816655425,
        encodes := Ra0555.tableCode_eq ▸ encodesTable_tableCode Ra0555.cycles } 28623
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0556.table, code := 25243508516106169470687100476483440705,
        encodes := Ra0556.tableCode_eq ▸ encodesTable_tableCode Ra0556.cycles } 28657
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0557.table, code := 25243508516106169470759158143535812673,
        encodes := Ra0557.tableCode_eq ▸ encodesTable_tableCode Ra0557.cycles } 28659
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0558.table, code := 25243589645747001929008098115227750465,
        encodes := Ra0558.tableCode_eq ▸ encodesTable_tableCode Ra0558.cycles } 28660
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0559.table, code := 25243589645747001929008098117375234113,
        encodes := Ra0559.tableCode_eq ▸ encodesTable_tableCode Ra0559.cycles } 28661
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0560.table, code := 25243589645747001929080155782280122433,
        encodes := Ra0560.tableCode_eq ▸ encodesTable_tableCode Ra0560.cycles } 28662
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0561.table, code := 25243589645747001929080155784427606081,
        encodes := Ra0561.tableCode_eq ▸ encodesTable_tableCode Ra0561.cycles } 28663
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0562.table, code := 25243508516106169473137058811211944001,
        encodes := Ra0562.tableCode_eq ▸ encodesTable_tableCode Ra0562.cycles } 28665
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0563.table, code := 25243508516106169473209116478264315969,
        encodes := Ra0563.tableCode_eq ▸ encodesTable_tableCode Ra0563.cycles } 28667
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0564.table, code := 25243589645747001931458056449956253761,
        encodes := Ra0564.tableCode_eq ▸ encodesTable_tableCode Ra0564.cycles } 28668
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0565.table, code := 25243589645747001931458056452103737409,
        encodes := Ra0565.tableCode_eq ▸ encodesTable_tableCode Ra0565.cycles } 28669
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0566.table, code := 25243589645747001931530114117008625729,
        encodes := Ra0566.tableCode_eq ▸ encodesTable_tableCode Ra0566.cycles } 28670
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0567.table, code := 25243589645747001931530114119156109377,
        encodes := Ra0567.tableCode_eq ▸ encodesTable_tableCode Ra0567.cycles } 28671
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0568.table, code := 30562854393732054578314388332689494081,
        encodes := Ra0568.tableCode_eq ▸ encodesTable_tableCode Ra0568.cycles } 31177
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0569.table, code := 30562854393732054578386445997594382401,
        encodes := Ra0569.tableCode_eq ▸ encodesTable_tableCode Ra0569.cycles } 31178
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0570.table, code := 30562854393732054578386445999741866049,
        encodes := Ra0570.tableCode_eq ▸ encodesTable_tableCode Ra0570.cycles } 31179
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0571.table, code := 30565693931161193055381892399773257793,
        encodes := Ra0571.tableCode_eq ▸ encodesTable_tableCode Ra0571.cycles } 31228
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0572.table, code := 30565693931161193055381892401920741441,
        encodes := Ra0572.tableCode_eq ▸ encodesTable_tableCode Ra0572.cycles } 31229
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0573.table, code := 30565693931161193055453950066825629761,
        encodes := Ra0573.tableCode_eq ▸ encodesTable_tableCode Ra0573.cycles } 31230
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0574.table, code := 30565693931161193055453950068973113409,
        encodes := Ra0574.tableCode_eq ▸ encodesTable_tableCode Ra0574.cycles } 31231
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0575.table, code := 30562854393732054580548173683440750657,
        encodes := Ra0575.tableCode_eq ▸ encodesTable_tableCode Ra0575.cycles } 31683
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0576.table, code := 30562935523372887038869171322185060417,
        encodes := Ra0576.tableCode_eq ▸ encodesTable_tableCode Ra0576.cycles } 31686
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (512 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (512 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (512 + i.val) 0 ≤ Data.profiles (512 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (512 + i.val) 0 = Data.canonicalMask (512 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (512 + i.val) < Data.canonicalMask (512 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (512 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models008
