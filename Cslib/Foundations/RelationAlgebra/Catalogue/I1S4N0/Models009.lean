/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0577
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0578
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0579
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0580
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0581
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0582
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0583
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0584
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0585
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0586
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0587
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0588
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0589
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0590
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0591
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0592
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0593
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0594
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0595
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0596
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0597
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0598
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0599
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0600
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0601
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0602
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0603
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0604
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0605
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0606
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0607
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0608
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0609
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0610
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0611
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0612
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0613
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0614
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0615
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0616
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0617
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0618
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0619
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0620
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0621
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0622
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0623
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0624
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0625
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0626
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0627
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0628
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0629
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0630
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0631
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0632
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0633
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0634
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0635
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0636
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0637
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0638
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0639
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0640

/-!
# Certified models 577–640 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models009

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0577.table, code := 9591247517457593164565391043840970817,
        encodes := Ra0577.tableCode_eq ▸ encodesTable_tableCode Ra0577.cycles } 119742
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0578.table, code := 9591247517457593164565391045988454465,
        encodes := Ra0578.tableCode_eq ▸ encodesTable_tableCode Ra0578.cycles } 119743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0579.table, code := 9593924795522859695109836038589386817,
        encodes := Ra0579.tableCode_eq ▸ encodesTable_tableCode Ra0579.cycles } 119793
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0580.table, code := 9593924795522859695181893705641758785,
        encodes := Ra0580.tableCode_eq ▸ encodesTable_tableCode Ra0580.cycles } 119795
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0581.table, code := 9593924795525277546749067504551989313,
        encodes := Ra0581.tableCode_eq ▸ encodesTable_tableCode Ra0581.cycles } 119797
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0582.table, code := 9593924795525277546821125171604361281,
        encodes := Ra0582.tableCode_eq ▸ encodesTable_tableCode Ra0582.cycles } 119799
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0583.table, code := 9594005925161274301863659878423466049,
        encodes := Ra0583.tableCode_eq ▸ encodesTable_tableCode Ra0583.cycles } 119802
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0584.table, code := 9594005925161274301863659880570949697,
        encodes := Ra0584.tableCode_eq ▸ encodesTable_tableCode Ra0584.cycles } 119803
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0585.table, code := 9594005925163692153502891344386068545,
        encodes := Ra0585.tableCode_eq ▸ encodesTable_tableCode Ra0585.cycles } 119806
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0586.table, code := 9594005925163692153502891346533552193,
        encodes := Ra0586.tableCode_eq ▸ encodesTable_tableCode Ra0586.cycles } 119807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0587.table, code := 9591247514972041681599432348250935361,
        encodes := Ra0587.tableCode_eq ▸ encodesTable_tableCode Ra0587.cycles } 120622
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0588.table, code := 9591247514972041681599432350398419009,
        encodes := Ra0588.tableCode_eq ▸ encodesTable_tableCode Ra0588.cycles } 120623
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0589.table, code := 9591247514969623832410159219164319809,
        encodes := Ra0589.tableCode_eq ▸ encodesTable_tableCode Ra0589.cycles } 120635
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0590.table, code := 9591247514972041684049390682979438657,
        encodes := Ra0590.tableCode_eq ▸ encodesTable_tableCode Ra0590.cycles } 120638
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0591.table, code := 9591247514972041684049390685126922305,
        encodes := Ra0591.tableCode_eq ▸ encodesTable_tableCode Ra0591.cycles } 120639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0592.table, code := 9594005922675722818897701184980914241,
        encodes := Ra0592.tableCode_eq ▸ encodesTable_tableCode Ra0592.cycles } 120683
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0593.table, code := 9594005922678140670536932648796033089,
        encodes := Ra0593.tableCode_eq ▸ encodesTable_tableCode Ra0593.cycles } 120686
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0594.table, code := 9594005922678140670536932650943516737,
        encodes := Ra0594.tableCode_eq ▸ encodesTable_tableCode Ra0594.cycles } 120687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0595.table, code := 9594005922675722821347659519709417537,
        encodes := Ra0595.tableCode_eq ▸ encodesTable_tableCode Ra0595.cycles } 120699
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0596.table, code := 9594005922678140672914833318619648065,
        encodes := Ra0596.tableCode_eq ▸ encodesTable_tableCode Ra0596.cycles } 120701
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0597.table, code := 9594005922678140672986890983524536385,
        encodes := Ra0597.tableCode_eq ▸ encodesTable_tableCode Ra0597.cycles } 120702
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0598.table, code := 9594005922678140672986890985672020033,
        encodes := Ra0598.tableCode_eq ▸ encodesTable_tableCode Ra0598.cycles } 120703
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0599.table, code := 9591247517455175315087887261577252929,
        encodes := Ra0599.tableCode_eq ▸ encodesTable_tableCode Ra0599.cycles } 120746
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0600.table, code := 9591247517455175315087887263724736577,
        encodes := Ra0600.tableCode_eq ▸ encodesTable_tableCode Ra0600.cycles } 120747
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0601.table, code := 9591247517457593166727118727539855425,
        encodes := Ra0601.tableCode_eq ▸ encodesTable_tableCode Ra0601.cycles } 120750
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0602.table, code := 9591247517457593166727118729687339073,
        encodes := Ra0602.tableCode_eq ▸ encodesTable_tableCode Ra0602.cycles } 120751
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0603.table, code := 9591247517455175317537845596305756225,
        encodes := Ra0603.tableCode_eq ▸ encodesTable_tableCode Ra0603.cycles } 120762
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0604.table, code := 9591247517455175317537845598453239873,
        encodes := Ra0604.tableCode_eq ▸ encodesTable_tableCode Ra0604.cycles } 120763
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0605.table, code := 9591247517457593169177077062268358721,
        encodes := Ra0605.tableCode_eq ▸ encodesTable_tableCode Ra0605.cycles } 120766
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0606.table, code := 9591247517457593169177077064415842369,
        encodes := Ra0606.tableCode_eq ▸ encodesTable_tableCode Ra0606.cycles } 120767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0607.table, code := 9593924795522859697343621389340643393,
        encodes := Ra0607.tableCode_eq ▸ encodesTable_tableCode Ra0607.cycles } 120803
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0608.table, code := 9593924795525277548982852855303245889,
        encodes := Ra0608.tableCode_eq ▸ encodesTable_tableCode Ra0608.cycles } 120807
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0609.table, code := 9594005925161274304025387562122350657,
        encodes := Ra0609.tableCode_eq ▸ encodesTable_tableCode Ra0609.cycles } 120810
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0610.table, code := 9594005925161274304025387564269834305,
        encodes := Ra0610.tableCode_eq ▸ encodesTable_tableCode Ra0610.cycles } 120811
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0611.table, code := 9594005925163692155664619028084953153,
        encodes := Ra0611.tableCode_eq ▸ encodesTable_tableCode Ra0611.cycles } 120814
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0612.table, code := 9594005925163692155664619030232436801,
        encodes := Ra0612.tableCode_eq ▸ encodesTable_tableCode Ra0612.cycles } 120815
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0613.table, code := 9593924795522859699721522057016774721,
        encodes := Ra0613.tableCode_eq ▸ encodesTable_tableCode Ra0613.cycles } 120817
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0614.table, code := 9593924795522859699793579724069146689,
        encodes := Ra0614.tableCode_eq ▸ encodesTable_tableCode Ra0614.cycles } 120819
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0615.table, code := 9593924795525277551360753522979377217,
        encodes := Ra0615.tableCode_eq ▸ encodesTable_tableCode Ra0615.cycles } 120821
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0616.table, code := 9593924795525277551432811190031749185,
        encodes := Ra0616.tableCode_eq ▸ encodesTable_tableCode Ra0616.cycles } 120823
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0617.table, code := 9594005925161274306403288231945965633,
        encodes := Ra0617.tableCode_eq ▸ encodesTable_tableCode Ra0617.cycles } 120825
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0618.table, code := 9594005925161274306475345896850853953,
        encodes := Ra0618.tableCode_eq ▸ encodesTable_tableCode Ra0618.cycles } 120826
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0619.table, code := 9594005925161274306475345898998337601,
        encodes := Ra0619.tableCode_eq ▸ encodesTable_tableCode Ra0619.cycles } 120827
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0620.table, code := 9594005925163692158042519697908568129,
        encodes := Ra0620.tableCode_eq ▸ encodesTable_tableCode Ra0620.cycles } 120829
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0621.table, code := 9594005925163692158114577362813456449,
        encodes := Ra0621.tableCode_eq ▸ encodesTable_tableCode Ra0621.cycles } 120830
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0622.table, code := 9594005925163692158114577364960940097,
        encodes := Ra0622.tableCode_eq ▸ encodesTable_tableCode Ra0622.cycles } 120831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0623.table, code := 9591247515126784341073644160540741697,
        encodes := Ra0623.tableCode_eq ▸ encodesTable_tableCode Ra0623.cycles } 121661
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0624.table, code := 9591247515126784341145701825445630017,
        encodes := Ra0624.tableCode_eq ▸ encodesTable_tableCode Ra0624.cycles } 121662
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0625.table, code := 9591247515126784341145701827593113665,
        encodes := Ra0625.tableCode_eq ▸ encodesTable_tableCode Ra0625.cycles } 121663
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0626.table, code := 9594005922832883330011144461085839425,
        encodes := Ra0626.tableCode_eq ▸ encodesTable_tableCode Ra0626.cycles } 121725
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0627.table, code := 9594005922832883330083202125990727745,
        encodes := Ra0627.tableCode_eq ▸ encodesTable_tableCode Ra0627.cycles } 121726
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0628.table, code := 9594005922832883330083202128138211393,
        encodes := Ra0628.tableCode_eq ▸ encodesTable_tableCode Ra0628.cycles } 121727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0629.table, code := 9591247517530128796464382076940193857,
        encodes := Ra0629.tableCode_eq ▸ encodesTable_tableCode Ra0629.cycles } 121758
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0630.table, code := 9591247517530128796464382079087677505,
        encodes := Ra0630.tableCode_eq ▸ encodesTable_tableCode Ra0630.cycles } 121759
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0631.table, code := 9591247517609917974562099073867059265,
        encodes := Ra0631.tableCode_eq ▸ encodesTable_tableCode Ra0631.cycles } 121785
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0632.table, code := 9591247517609917974634156738771947585,
        encodes := Ra0632.tableCode_eq ▸ encodesTable_tableCode Ra0632.cycles } 121786
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0633.table, code := 9591247517609917974634156740919431233,
        encodes := Ra0633.tableCode_eq ▸ encodesTable_tableCode Ra0633.cycles } 121787
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0634.table, code := 9591247517612335826201330539829661761,
        encodes := Ra0634.tableCode_eq ▸ encodesTable_tableCode Ra0634.cycles } 121789
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0635.table, code := 9591247517612335826273388204734550081,
        encodes := Ra0635.tableCode_eq ▸ encodesTable_tableCode Ra0635.cycles } 121790
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0636.table, code := 9591247517612335826273388206882033729,
        encodes := Ra0636.tableCode_eq ▸ encodesTable_tableCode Ra0636.cycles } 121791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0637.table, code := 9593924795597813178720116202556100673,
        encodes := Ra0637.tableCode_eq ▸ encodesTable_tableCode Ra0637.cycles } 121814
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0638.table, code := 9593924795597813178720116204703584321,
        encodes := Ra0638.tableCode_eq ▸ encodesTable_tableCode Ra0638.cycles } 121815
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0639.table, code := 9594005925236227785401882377485291585,
        encodes := Ra0639.tableCode_eq ▸ encodesTable_tableCode Ra0639.cycles } 121822
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0640.table, code := 9594005925236227785401882379632775233,
        encodes := Ra0640.tableCode_eq ▸ encodesTable_tableCode Ra0640.cycles } 121823
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (576 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (576 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
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

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models009
