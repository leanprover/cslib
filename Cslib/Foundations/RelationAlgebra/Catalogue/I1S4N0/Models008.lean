/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0513
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0514
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0515
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0516
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0517
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0518
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0519
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0520
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0521
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0522
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0523
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0524
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0525
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0526
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0527
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0528
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0529
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0530
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0531
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0532
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0533
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0534
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0535
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0536
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0537
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0538
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0539
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0540
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0541
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0542
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0543
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0544
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0545
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0546
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0547
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0548
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0549
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0550
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0551
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0552
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0553
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0554
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0555
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0556
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0557
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0558
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0559
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0560
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0561
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0562
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0563
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0564
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0565
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0566
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0567
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0568
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0569
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0570
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0571
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0572
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0573
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0574
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0575
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0576

/-!
# Certified models 513–576 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models008

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0513.table, code := 9588813625974343761641444688454225985,
        encodes := Ra0513.tableCode_eq ▸ encodesTable_tableCode Ra0513.cycles } 117631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0514.table, code := 9588732498739273610278358762872115265,
        encodes := Ra0514.tableCode_eq ▸ encodesTable_tableCode Ra0514.cycles } 117718
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0515.table, code := 9588732498739273610278358765019598913,
        encodes := Ra0515.tableCode_eq ▸ encodesTable_tableCode Ra0515.cycles } 117719
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0516.table, code := 9588813628377688216960124937801306177,
        encodes := Ra0516.tableCode_eq ▸ encodesTable_tableCode Ra0516.cycles } 117726
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0517.table, code := 9588813628377688216960124939948789825,
        encodes := Ra0517.tableCode_eq ▸ encodesTable_tableCode Ra0517.cycles } 117727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0518.table, code := 9588732498819062788376075759798980673,
        encodes := Ra0518.tableCode_eq ▸ encodesTable_tableCode Ra0518.cycles } 117745
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0519.table, code := 9588732498819062788448133426851352641,
        encodes := Ra0519.tableCode_eq ▸ encodesTable_tableCode Ra0519.cycles } 117747
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0520.table, code := 9588732498821480640015307225761583169,
        encodes := Ra0520.tableCode_eq ▸ encodesTable_tableCode Ra0520.cycles } 117749
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0521.table, code := 9588732498821480640087364890666471489,
        encodes := Ra0521.tableCode_eq ▸ encodesTable_tableCode Ra0521.cycles } 117750
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0522.table, code := 9588732498821480640087364892813955137,
        encodes := Ra0522.tableCode_eq ▸ encodesTable_tableCode Ra0522.cycles } 117751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0523.table, code := 9588813628457477395057841934728171585,
        encodes := Ra0523.tableCode_eq ▸ encodesTable_tableCode Ra0523.cycles } 117753
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0524.table, code := 9588813628457477395129899599633059905,
        encodes := Ra0524.tableCode_eq ▸ encodesTable_tableCode Ra0524.cycles } 117754
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0525.table, code := 9588813628457477395129899601780543553,
        encodes := Ra0525.tableCode_eq ▸ encodesTable_tableCode Ra0525.cycles } 117755
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0526.table, code := 9588813628459895246697073400690774081,
        encodes := Ra0526.tableCode_eq ▸ encodesTable_tableCode Ra0526.cycles } 117757
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0527.table, code := 9588813628459895246769131065595662401,
        encodes := Ra0527.tableCode_eq ▸ encodesTable_tableCode Ra0527.cycles } 117758
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0528.table, code := 9588813628459895246769131067743146049,
        encodes := Ra0528.tableCode_eq ▸ encodesTable_tableCode Ra0528.cycles } 117759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0529.table, code := 9588732496335929157121406197223919681,
        encodes := Ra0529.tableCode_eq ▸ encodesTable_tableCode Ra0529.cycles } 118631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0530.table, code := 9588813625971925912163940904043024449,
        encodes := Ra0530.tableCode_eq ▸ encodesTable_tableCode Ra0530.cycles } 118634
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0531.table, code := 9588813625971925912163940906190508097,
        encodes := Ra0531.tableCode_eq ▸ encodesTable_tableCode Ra0531.cycles } 118635
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0532.table, code := 9588813625974343763803172370005626945,
        encodes := Ra0532.tableCode_eq ▸ encodesTable_tableCode Ra0532.cycles } 118638
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0533.table, code := 9588813625974343763803172372153110593,
        encodes := Ra0533.tableCode_eq ▸ encodesTable_tableCode Ra0533.cycles } 118639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0534.table, code := 9588732496335929159571364531952422977,
        encodes := Ra0534.tableCode_eq ▸ encodesTable_tableCode Ra0534.cycles } 118647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0535.table, code := 9588813625971925914541841573866639425,
        encodes := Ra0535.tableCode_eq ▸ encodesTable_tableCode Ra0535.cycles } 118649
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0536.table, code := 9588813625971925914613899238771527745,
        encodes := Ra0536.tableCode_eq ▸ encodesTable_tableCode Ra0536.cycles } 118650
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0537.table, code := 9588813625971925914613899240919011393,
        encodes := Ra0537.tableCode_eq ▸ encodesTable_tableCode Ra0537.cycles } 118651
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0538.table, code := 9588813625974343766181073039829241921,
        encodes := Ra0538.tableCode_eq ▸ encodesTable_tableCode Ra0538.cycles } 118653
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0539.table, code := 9588813625974343766253130704734130241,
        encodes := Ra0539.tableCode_eq ▸ encodesTable_tableCode Ra0539.cycles } 118654
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0540.table, code := 9588813625974343766253130706881613889,
        encodes := Ra0540.tableCode_eq ▸ encodesTable_tableCode Ra0540.cycles } 118655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0541.table, code := 9588732498739273612440086446570999873,
        encodes := Ra0541.tableCode_eq ▸ encodesTable_tableCode Ra0541.cycles } 118726
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0542.table, code := 9588732498739273612440086448718483521,
        encodes := Ra0542.tableCode_eq ▸ encodesTable_tableCode Ra0542.cycles } 118727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0543.table, code := 9588813628377688219121852621500190785,
        encodes := Ra0543.tableCode_eq ▸ encodesTable_tableCode Ra0543.cycles } 118734
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0544.table, code := 9588813628377688219121852623647674433,
        encodes := Ra0544.tableCode_eq ▸ encodesTable_tableCode Ra0544.cycles } 118735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0545.table, code := 9588732498739273614890044781299503169,
        encodes := Ra0545.tableCode_eq ▸ encodesTable_tableCode Ra0545.cycles } 118742
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0546.table, code := 9588732498739273614890044783446986817,
        encodes := Ra0546.tableCode_eq ▸ encodesTable_tableCode Ra0546.cycles } 118743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0547.table, code := 9588813628377688221571810956228694081,
        encodes := Ra0547.tableCode_eq ▸ encodesTable_tableCode Ra0547.cycles } 118750
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0548.table, code := 9588813628377688221571810958376177729,
        encodes := Ra0548.tableCode_eq ▸ encodesTable_tableCode Ra0548.cycles } 118751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0549.table, code := 9588732498819062790609861110550237249,
        encodes := Ra0549.tableCode_eq ▸ encodesTable_tableCode Ra0549.cycles } 118755
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0550.table, code := 9588732498821480642249092574365356097,
        encodes := Ra0550.tableCode_eq ▸ encodesTable_tableCode Ra0550.cycles } 118758
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0551.table, code := 9588732498821480642249092576512839745,
        encodes := Ra0551.tableCode_eq ▸ encodesTable_tableCode Ra0551.cycles } 118759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0552.table, code := 9588813628457477397291627283331944513,
        encodes := Ra0552.tableCode_eq ▸ encodesTable_tableCode Ra0552.cycles } 118762
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0553.table, code := 9588813628457477397291627285479428161,
        encodes := Ra0553.tableCode_eq ▸ encodesTable_tableCode Ra0553.cycles } 118763
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0554.table, code := 9588813628459895248930858749294547009,
        encodes := Ra0554.tableCode_eq ▸ encodesTable_tableCode Ra0554.cycles } 118766
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0555.table, code := 9588813628459895248930858751442030657,
        encodes := Ra0555.tableCode_eq ▸ encodesTable_tableCode Ra0555.cycles } 118767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0556.table, code := 9588732498819062792987761778226368577,
        encodes := Ra0556.tableCode_eq ▸ encodesTable_tableCode Ra0556.cycles } 118769
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0557.table, code := 9588732498819062793059819445278740545,
        encodes := Ra0557.tableCode_eq ▸ encodesTable_tableCode Ra0557.cycles } 118771
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0558.table, code := 9588732498821480644626993244188971073,
        encodes := Ra0558.tableCode_eq ▸ encodesTable_tableCode Ra0558.cycles } 118773
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0559.table, code := 9588732498821480644699050909093859393,
        encodes := Ra0559.tableCode_eq ▸ encodesTable_tableCode Ra0559.cycles } 118774
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0560.table, code := 9588732498821480644699050911241343041,
        encodes := Ra0560.tableCode_eq ▸ encodesTable_tableCode Ra0560.cycles } 118775
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0561.table, code := 9588813628457477399669527953155559489,
        encodes := Ra0561.tableCode_eq ▸ encodesTable_tableCode Ra0561.cycles } 118777
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0562.table, code := 9588813628457477399741585618060447809,
        encodes := Ra0562.tableCode_eq ▸ encodesTable_tableCode Ra0562.cycles } 118778
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0563.table, code := 9588813628457477399741585620207931457,
        encodes := Ra0563.tableCode_eq ▸ encodesTable_tableCode Ra0563.cycles } 118779
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0564.table, code := 9588813628459895251308759419118161985,
        encodes := Ra0564.tableCode_eq ▸ encodesTable_tableCode Ra0564.cycles } 118781
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0565.table, code := 9588813628459895251380817084023050305,
        encodes := Ra0565.tableCode_eq ▸ encodesTable_tableCode Ra0565.cycles } 118782
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0566.table, code := 9588813628459895251380817086170533953,
        encodes := Ra0566.tableCode_eq ▸ encodesTable_tableCode Ra0566.cycles } 118783
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0567.table, code := 9591247514969623827798473198589448257,
        encodes := Ra0567.tableCode_eq ▸ encodesTable_tableCode Ra0567.cycles } 119610
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0568.table, code := 9591247514969623827798473200736931905,
        encodes := Ra0568.tableCode_eq ▸ encodesTable_tableCode Ra0568.cycles } 119611
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0569.table, code := 9591247514972041679437704664552050753,
        encodes := Ra0569.tableCode_eq ▸ encodesTable_tableCode Ra0569.cycles } 119614
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0570.table, code := 9591247514972041679437704666699534401,
        encodes := Ra0570.tableCode_eq ▸ encodesTable_tableCode Ra0570.cycles } 119615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0571.table, code := 9594005922675722816735973499134545985,
        encodes := Ra0571.tableCode_eq ▸ encodesTable_tableCode Ra0571.cycles } 119674
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0572.table, code := 9594005922675722816735973501282029633,
        encodes := Ra0572.tableCode_eq ▸ encodesTable_tableCode Ra0572.cycles } 119675
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0573.table, code := 9594005922678140668375204965097148481,
        encodes := Ra0573.tableCode_eq ▸ encodesTable_tableCode Ra0573.cycles } 119678
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0574.table, code := 9594005922678140668375204967244632129,
        encodes := Ra0574.tableCode_eq ▸ encodesTable_tableCode Ra0574.cycles } 119679
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0575.table, code := 9591247517455175312926159577878368321,
        encodes := Ra0575.tableCode_eq ▸ encodesTable_tableCode Ra0575.cycles } 119738
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0576.table, code := 9591247517455175312926159580025851969,
        encodes := Ra0576.tableCode_eq ▸ encodesTable_tableCode Ra0576.cycles } 119739
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (512 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (512 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
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

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models008
