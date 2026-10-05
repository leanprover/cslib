/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0449
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0450
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0451
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0452
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0453
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0454
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0455
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0456
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0457
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0458
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0459
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0460
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0461
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0462
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0463
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0464
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0465
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0466
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0467
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0468
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0469
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0470
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0471
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0472
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0473
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0474
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0475
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0476
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0477
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0478
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0479
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0480
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0481
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0482
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0483
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0484
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0485
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0486
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0487
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0488
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0489
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0490
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0491
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0492
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0493
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0494
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0495
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0496
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0497
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0498
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0499
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0500
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0501
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0502
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0503
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0504
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0505
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0506
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0507
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0508
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0509
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0510
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0511
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0512

/-!
# Certified models 449–512 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models007

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0449.table, code := 9412275373626647506812301928204341313,
        encodes := Ra0449.tableCode_eq ▸ encodesTable_tableCode Ra0449.cycles } 101199
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0450.table, code := 9412275376194406024198952770016120897,
        encodes := Ra0450.tableCode_eq ▸ encodesTable_tableCode Ra0450.cycles } 101375
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0451.table, code := 9412275373626647511423987946631729217,
        encodes := Ra0451.tableCode_eq ▸ encodesTable_tableCode Ra0451.cycles } 102223
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0452.table, code := 9412275376194406028810638788443508801,
        encodes := Ra0452.tableCode_eq ▸ encodesTable_tableCode Ra0452.cycles } 102399
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0453.table, code := 9417467672898202930932713048806527041,
        encodes := Ra0453.tableCode_eq ▸ encodesTable_tableCode Ra0453.cycles } 103423
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0454.table, code := 9417467672898202935544399067233914945,
        encodes := Ra0454.tableCode_eq ▸ encodesTable_tableCode Ra0454.cycles } 104447
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0455.table, code := 9417467670485187077704017702616830017,
        encodes := Ra0455.tableCode_eq ▸ encodesTable_tableCode Ra0455.cycles } 105311
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0456.table, code := 9417467673052945592640710209700106305,
        encodes := Ra0456.tableCode_eq ▸ encodesTable_tableCode Ra0456.cycles } 105471
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0457.table, code := 9417467670485187082315703721044217921,
        encodes := Ra0457.tableCode_eq ▸ encodesTable_tableCode Ra0457.cycles } 106335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0458.table, code := 9417467673052945597252396228127494209,
        encodes := Ra0458.tableCode_eq ▸ encodesTable_tableCode Ra0458.cycles } 106495
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0459.table, code := 9409516971027051318277575814439768129,
        encodes := Ra0459.tableCode_eq ▸ encodesTable_tableCode Ra0459.cycles } 107279
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0460.table, code := 9409516973512602803405262193728688193,
        encodes := Ra0460.tableCode_eq ▸ encodesTable_tableCode Ra0460.cycles } 107407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0461.table, code := 9412275381300908824601726956796645441,
        encodes := Ra0461.tableCode_eq ▸ encodesTable_tableCode Ra0461.cycles } 107519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0462.table, code := 9409516971027051322889261832867156033,
        encodes := Ra0462.tableCode_eq ▸ encodesTable_tableCode Ra0462.cycles } 108303
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0463.table, code := 9409516973512602808016948212156076097,
        encodes := Ra0463.tableCode_eq ▸ encodesTable_tableCode Ra0463.cycles } 108431
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0464.table, code := 9412275381300908829213412975224033345,
        encodes := Ra0464.tableCode_eq ▸ encodesTable_tableCode Ra0464.cycles } 108543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0465.table, code := 9412275378887892968923073275878445121,
        encodes := Ra0465.tableCode_eq ▸ encodesTable_tableCode Ra0465.cycles } 109391
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0466.table, code := 9412275381455651486309724117690224705,
        encodes := Ra0466.tableCode_eq ▸ encodesTable_tableCode Ra0466.cycles } 109567
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0467.table, code := 9412275378887892973534759294305833025,
        encodes := Ra0467.tableCode_eq ▸ encodesTable_tableCode Ra0467.cycles } 110415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0468.table, code := 9412275381455651490921410136117612609,
        encodes := Ra0468.tableCode_eq ▸ encodesTable_tableCode Ra0468.cycles } 110591
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0469.table, code := 9417467675673896907915798017191710785,
        encodes := Ra0469.tableCode_eq ▸ encodesTable_tableCode Ra0469.cycles } 111487
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0470.table, code := 9417467678159448393043484396480630849,
        encodes := Ra0470.tableCode_eq ▸ encodesTable_tableCode Ra0470.cycles } 111615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0471.table, code := 9417467675673896912527484035619098689,
        encodes := Ra0471.tableCode_eq ▸ encodesTable_tableCode Ra0471.cycles } 112511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0472.table, code := 9417467678159448397655170414908018753,
        encodes := Ra0472.tableCode_eq ▸ encodesTable_tableCode Ra0472.cycles } 112639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0473.table, code := 9417467675828639569623795178085290049,
        encodes := Ra0473.tableCode_eq ▸ encodesTable_tableCode Ra0473.cycles } 113535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0474.table, code := 9417467678314191054751481557374210113,
        encodes := Ra0474.tableCode_eq ▸ encodesTable_tableCode Ra0474.cycles } 113663
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0475.table, code := 9417467675828639574235481196512677953,
        encodes := Ra0475.tableCode_eq ▸ encodesTable_tableCode Ra0475.cycles } 114559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0476.table, code := 9417467678314191059363167575801598017,
        encodes := Ra0476.tableCode_eq ▸ encodesTable_tableCode Ra0476.cycles } 114687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0477.table, code := 9588732496178768643774177570367737921,
        encodes := Ra0477.tableCode_eq ▸ encodesTable_tableCode Ra0477.cycles } 116579
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0478.table, code := 9588732496181186495413409036330340417,
        encodes := Ra0478.tableCode_eq ▸ encodesTable_tableCode Ra0478.cycles } 116583
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0479.table, code := 9588813625817183250455943743149445185,
        encodes := Ra0479.tableCode_eq ▸ encodesTable_tableCode Ra0479.cycles } 116586
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0480.table, code := 9588813625817183250455943745296928833,
        encodes := Ra0480.tableCode_eq ▸ encodesTable_tableCode Ra0480.cycles } 116587
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0481.table, code := 9588813625819601102095175209112047681,
        encodes := Ra0481.tableCode_eq ▸ encodesTable_tableCode Ra0481.cycles } 116590
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0482.table, code := 9588813625819601102095175211259531329,
        encodes := Ra0482.tableCode_eq ▸ encodesTable_tableCode Ra0482.cycles } 116591
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0483.table, code := 9588732496178768646224135905096241217,
        encodes := Ra0483.tableCode_eq ▸ encodesTable_tableCode Ra0483.cycles } 116595
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0484.table, code := 9588732496181186497791309704006471745,
        encodes := Ra0484.tableCode_eq ▸ encodesTable_tableCode Ra0484.cycles } 116597
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0485.table, code := 9588732496181186497863367371058843713,
        encodes := Ra0485.tableCode_eq ▸ encodesTable_tableCode Ra0485.cycles } 116599
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0486.table, code := 9588813625817183252833844412973060161,
        encodes := Ra0486.tableCode_eq ▸ encodesTable_tableCode Ra0486.cycles } 116601
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0487.table, code := 9588813625817183252905902077877948481,
        encodes := Ra0487.tableCode_eq ▸ encodesTable_tableCode Ra0487.cycles } 116602
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0488.table, code := 9588813625817183252905902080025432129,
        encodes := Ra0488.tableCode_eq ▸ encodesTable_tableCode Ra0488.cycles } 116603
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0489.table, code := 9588813625819601104473075878935662657,
        encodes := Ra0489.tableCode_eq ▸ encodesTable_tableCode Ra0489.cycles } 116605
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0490.table, code := 9588813625819601104545133543840550977,
        encodes := Ra0490.tableCode_eq ▸ encodesTable_tableCode Ra0490.cycles } 116606
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0491.table, code := 9588813625819601104545133545988034625,
        encodes := Ra0491.tableCode_eq ▸ encodesTable_tableCode Ra0491.cycles } 116607
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0492.table, code := 9588732498664320128901863949656657985,
        encodes := Ra0492.tableCode_eq ▸ encodesTable_tableCode Ra0492.cycles } 116707
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0493.table, code := 9588732498666737980541095415619260481,
        encodes := Ra0493.tableCode_eq ▸ encodesTable_tableCode Ra0493.cycles } 116711
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0494.table, code := 9588813628302734735583630122438365249,
        encodes := Ra0494.tableCode_eq ▸ encodesTable_tableCode Ra0494.cycles } 116714
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0495.table, code := 9588813628302734735583630124585848897,
        encodes := Ra0495.tableCode_eq ▸ encodesTable_tableCode Ra0495.cycles } 116715
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0496.table, code := 9588813628305152587222861588400967745,
        encodes := Ra0496.tableCode_eq ▸ encodesTable_tableCode Ra0496.cycles } 116718
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0497.table, code := 9588813628305152587222861590548451393,
        encodes := Ra0497.tableCode_eq ▸ encodesTable_tableCode Ra0497.cycles } 116719
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0498.table, code := 9588732498664320131279764617332789313,
        encodes := Ra0498.tableCode_eq ▸ encodesTable_tableCode Ra0498.cycles } 116721
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0499.table, code := 9588732498664320131351822284385161281,
        encodes := Ra0499.tableCode_eq ▸ encodesTable_tableCode Ra0499.cycles } 116723
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0500.table, code := 9588732498666737982918996083295391809,
        encodes := Ra0500.tableCode_eq ▸ encodesTable_tableCode Ra0500.cycles } 116725
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0501.table, code := 9588732498666737982991053750347763777,
        encodes := Ra0501.tableCode_eq ▸ encodesTable_tableCode Ra0501.cycles } 116727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0502.table, code := 9588813628302734737961530792261980225,
        encodes := Ra0502.tableCode_eq ▸ encodesTable_tableCode Ra0502.cycles } 116729
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0503.table, code := 9588813628302734738033588457166868545,
        encodes := Ra0503.tableCode_eq ▸ encodesTable_tableCode Ra0503.cycles } 116730
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0504.table, code := 9588813628302734738033588459314352193,
        encodes := Ra0504.tableCode_eq ▸ encodesTable_tableCode Ra0504.cycles } 116731
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0505.table, code := 9588813628305152589600762258224582721,
        encodes := Ra0505.tableCode_eq ▸ encodesTable_tableCode Ra0505.cycles } 116733
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0506.table, code := 9588813628305152589672819923129471041,
        encodes := Ra0506.tableCode_eq ▸ encodesTable_tableCode Ra0506.cycles } 116734
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0507.table, code := 9588813628305152589672819925276954689,
        encodes := Ra0507.tableCode_eq ▸ encodesTable_tableCode Ra0507.cycles } 116735
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0508.table, code := 9588732496335929154887620846472663105,
        encodes := Ra0508.tableCode_eq ▸ encodesTable_tableCode Ra0508.cycles } 117621
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0509.table, code := 9588732496335929154959678511377551425,
        encodes := Ra0509.tableCode_eq ▸ encodesTable_tableCode Ra0509.cycles } 117622
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0510.table, code := 9588732496335929154959678513525035073,
        encodes := Ra0510.tableCode_eq ▸ encodesTable_tableCode Ra0510.cycles } 117623
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0511.table, code := 9588813625974343761569387021401854017,
        encodes := Ra0511.tableCode_eq ▸ encodesTable_tableCode Ra0511.cycles } 117629
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0512.table, code := 9588813625974343761641444686306742337,
        encodes := Ra0512.tableCode_eq ▸ encodesTable_tableCode Ra0512.cycles } 117630
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (448 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (448 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (448 + i.val) 0 ≤ Data.profiles (448 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (448 + i.val) 0 = Data.canonicalMask (448 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (448 + i.val) < Data.canonicalMask (448 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (448 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models007
