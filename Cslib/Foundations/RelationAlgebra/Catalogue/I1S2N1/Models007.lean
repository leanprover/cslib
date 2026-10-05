/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0449
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0450
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0451
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0452
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0453
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0454
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0455
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0456
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0457
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0458
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0459
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0460
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0461
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0462
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0463
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0464
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0465
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0466
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0467
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0468
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0469
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0470
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0471
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0472
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0473
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0474
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0475
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0476
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0477
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0478
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0479
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0480
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0481
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0482
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0483
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0484
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0485
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0486
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0487
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0488
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0489
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0490
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0491
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0492
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0493
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0494
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0495
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0496
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0497
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0498
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0499
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0500
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0501
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0502
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0503
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0504
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0505
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0506
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0507
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0508
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0509
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0510
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0511
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S2N1.Ra0512

/-!
# Certified models 449–512 of the ⟨1, 2, 1⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S2N1.Models007

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0449.table, code := 30321655978645628255679154331737919553,
        encodes := Ra0449.tableCode_eq ▸ encodesTable_tableCode Ra0449.cycles } 24309
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0450.table, code := 30321655978645628255751211998790291521,
        encodes := Ra0450.tableCode_eq ▸ encodesTable_tableCode Ra0450.cycles } 24311
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0451.table, code := 30321655978645628258201170333518794817,
        encodes := Ra0451.tableCode_eq ▸ encodesTable_tableCode Ra0451.cycles } 24319
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0452.table, code := 27743112678344005365456285559368716353,
        encodes := Ra0452.tableCode_eq ▸ encodesTable_tableCode Ra0452.cycles } 24392
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0453.table, code := 27743112678344005365456285561516200001,
        encodes := Ra0453.tableCode_eq ▸ encodesTable_tableCode Ra0453.cycles } 24393
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0454.table, code := 27745871086132311381824891320032038977,
        encodes := Ra0454.tableCode_eq ▸ encodesTable_tableCode Ra0454.cycles } 24434
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0455.table, code := 27745871086132311381824891322179522625,
        encodes := Ra0455.tableCode_eq ▸ encodesTable_tableCode Ra0455.cycles } 24435
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0456.table, code := 27745952215773143840073831293871460417,
        encodes := Ra0456.tableCode_eq ▸ encodesTable_tableCode Ra0456.cycles } 24436
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0457.table, code := 27745952215773143840073831296018944065,
        encodes := Ra0457.tableCode_eq ▸ encodesTable_tableCode Ra0457.cycles } 24437
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0458.table, code := 27745952215773143840145888960923832385,
        encodes := Ra0458.tableCode_eq ▸ encodesTable_tableCode Ra0458.cycles } 24438
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0459.table, code := 27745952215773143840145888963071316033,
        encodes := Ra0459.tableCode_eq ▸ encodesTable_tableCode Ra0459.cycles } 24439
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0460.table, code := 27745871086132311384274849654760542273,
        encodes := Ra0460.tableCode_eq ▸ encodesTable_tableCode Ra0460.cycles } 24442
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0461.table, code := 27745871086132311384274849656908025921,
        encodes := Ra0461.tableCode_eq ▸ encodesTable_tableCode Ra0461.cycles } 24443
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0462.table, code := 27745952215773143842523789628599963713,
        encodes := Ra0462.tableCode_eq ▸ encodesTable_tableCode Ra0462.cycles } 24444
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0463.table, code := 27745952215773143842523789630747447361,
        encodes := Ra0463.tableCode_eq ▸ encodesTable_tableCode Ra0463.cycles } 24445
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0464.table, code := 27745952215773143842595847295652335681,
        encodes := Ra0464.tableCode_eq ▸ encodesTable_tableCode Ra0464.cycles } 24446
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0465.table, code := 27745952215773143842595847297799819329,
        encodes := Ra0465.tableCode_eq ▸ encodesTable_tableCode Ra0465.cycles } 24447
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0466.table, code := 30401487463622274345479195498633236545,
        encodes := Ra0466.tableCode_eq ▸ encodesTable_tableCode Ra0466.cycles } 24471
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0467.table, code := 30401487463622274347929153833361739841,
        encodes := Ra0467.tableCode_eq ▸ encodesTable_tableCode Ra0467.cycles } 24479
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0468.table, code := 30404083612056377536575209554678386753,
        encodes := Ra0468.tableCode_eq ▸ encodesTable_tableCode Ra0468.cycles } 24501
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0469.table, code := 30404083612056377536647267221730758721,
        encodes := Ra0469.tableCode_eq ▸ encodesTable_tableCode Ra0469.cycles } 24503
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0470.table, code := 30404083612056377539097225556459262017,
        encodes := Ra0470.tableCode_eq ▸ encodesTable_tableCode Ra0470.cycles } 24511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0471.table, code := 30401974320603550888068631827650449473,
        encodes := Ra0471.tableCode_eq ▸ encodesTable_tableCode Ra0471.cycles } 24526
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0472.table, code := 30401974320603550888068631829797933121,
        encodes := Ra0472.tableCode_eq ▸ encodesTable_tableCode Ra0472.cycles } 24527
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0473.table, code := 30402136579957753713197108198163877953,
        encodes := Ra0473.tableCode_eq ▸ encodesTable_tableCode Ra0473.cycles } 24534
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0474.table, code := 30402136579957753713197108200311361601,
        encodes := Ra0474.tableCode_eq ▸ encodesTable_tableCode Ra0474.cycles } 24535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0475.table, code := 30402136579957753715575008865840009281,
        encodes := Ra0475.tableCode_eq ▸ encodesTable_tableCode Ra0475.cycles } 24540
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0476.table, code := 30402136579957753715575008867987492929,
        encodes := Ra0476.tableCode_eq ▸ encodesTable_tableCode Ra0476.cycles } 24541
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0477.table, code := 30402136579957753715647066532892381249,
        encodes := Ra0477.tableCode_eq ▸ encodesTable_tableCode Ra0477.cycles } 24542
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0478.table, code := 30402136579957753715647066535039864897,
        encodes := Ra0478.tableCode_eq ▸ encodesTable_tableCode Ra0478.cycles } 24543
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0479.table, code := 30404570469037654079164645883695599681,
        encodes := Ra0479.tableCode_eq ▸ encodesTable_tableCode Ra0479.cycles } 24556
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0480.table, code := 30404570469037654079164645885843083329,
        encodes := Ra0480.tableCode_eq ▸ encodesTable_tableCode Ra0480.cycles } 24557
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0481.table, code := 30404570469037654079236703550747971649,
        encodes := Ra0481.tableCode_eq ▸ encodesTable_tableCode Ra0481.cycles } 24558
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0482.table, code := 30404570469037654079236703552895455297,
        encodes := Ra0482.tableCode_eq ▸ encodesTable_tableCode Ra0482.cycles } 24559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0483.table, code := 30404651598751024445972124615464718401,
        encodes := Ra0483.tableCode_eq ▸ encodesTable_tableCode Ra0483.cycles } 24561
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0484.table, code := 30404651598751024446044182280369606721,
        encodes := Ra0484.tableCode_eq ▸ encodesTable_tableCode Ra0484.cycles } 24562
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0485.table, code := 30404651598751024446044182282517090369,
        encodes := Ra0485.tableCode_eq ▸ encodesTable_tableCode Ra0485.cycles } 24563
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0486.table, code := 30404732728391856904293122254209028161,
        encodes := Ra0486.tableCode_eq ▸ encodesTable_tableCode Ra0486.cycles } 24564
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0487.table, code := 30404732728391856904293122256356511809,
        encodes := Ra0487.tableCode_eq ▸ encodesTable_tableCode Ra0487.cycles } 24565
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0488.table, code := 30404732728391856904365179921261400129,
        encodes := Ra0488.tableCode_eq ▸ encodesTable_tableCode Ra0488.cycles } 24566
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0489.table, code := 30404732728391856904365179923408883777,
        encodes := Ra0489.tableCode_eq ▸ encodesTable_tableCode Ra0489.cycles } 24567
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0490.table, code := 30404651598751024448422082950193221697,
        encodes := Ra0490.tableCode_eq ▸ encodesTable_tableCode Ra0490.cycles } 24569
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0491.table, code := 30404651598751024448494140615098110017,
        encodes := Ra0491.tableCode_eq ▸ encodesTable_tableCode Ra0491.cycles } 24570
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0492.table, code := 30404651598751024448494140617245593665,
        encodes := Ra0492.tableCode_eq ▸ encodesTable_tableCode Ra0492.cycles } 24571
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0493.table, code := 30404732728391856906743080588937531457,
        encodes := Ra0493.tableCode_eq ▸ encodesTable_tableCode Ra0493.cycles } 24572
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0494.table, code := 30404732728391856906743080591085015105,
        encodes := Ra0494.tableCode_eq ▸ encodesTable_tableCode Ra0494.cycles } 24573
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0495.table, code := 30404732728391856906815138255989903425,
        encodes := Ra0495.tableCode_eq ▸ encodesTable_tableCode Ra0495.cycles } 24574
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0496.table, code := 30404732728391856906815138258137387073,
        encodes := Ra0496.tableCode_eq ▸ encodesTable_tableCode Ra0496.cycles } 24575
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0497.table, code := 22576777298685868153031920133706354753,
        encodes := Ra0497.tableCode_eq ▸ encodesTable_tableCode Ra0497.cycles } 26946
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0498.table, code := 22576777298685868153031920135853838401,
        encodes := Ra0498.tableCode_eq ▸ encodesTable_tableCode Ra0498.cycles } 26947
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0499.table, code := 22576858428326700611352917774598148161,
        encodes := Ra0499.tableCode_eq ▸ encodesTable_tableCode Ra0499.cycles } 26950
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0500.table, code := 22576858428326700611352917776745631809,
        encodes := Ra0500.tableCode_eq ▸ encodesTable_tableCode Ra0500.cycles } 26951
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0501.table, code := 22576777298685868155409820803529969729,
        encodes := Ra0501.tableCode_eq ▸ encodesTable_tableCode Ra0501.cycles } 26953
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0502.table, code := 22576777298685868155481878468434858049,
        encodes := Ra0502.tableCode_eq ▸ encodesTable_tableCode Ra0502.cycles } 26954
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0503.table, code := 22576777298685868155481878470582341697,
        encodes := Ra0503.tableCode_eq ▸ encodesTable_tableCode Ra0503.cycles } 26955
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0504.table, code := 25235557811304581217251211096191406145,
        encodes := Ra0504.tableCode_eq ▸ encodesTable_tableCode Ra0504.cycles } 27075
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0505.table, code := 25235638940945413675572208734935715905,
        encodes := Ra0505.tableCode_eq ▸ encodesTable_tableCode Ra0505.cycles } 27078
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0506.table, code := 25235638940945413675572208737083199553,
        encodes := Ra0506.tableCode_eq ▸ encodesTable_tableCode Ra0506.cycles } 27079
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0507.table, code := 25238397348733719696696615830951301185,
        encodes := Ra0507.tableCode_eq ▸ encodesTable_tableCode Ra0507.cycles } 27132
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0508.table, code := 25238397348733719696696615833098784833,
        encodes := Ra0508.tableCode_eq ▸ encodesTable_tableCode Ra0508.cycles } 27133
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0509.table, code := 25238397348733719696768673498003673153,
        encodes := Ra0509.tableCode_eq ▸ encodesTable_tableCode Ra0509.cycles } 27134
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0510.table, code := 25238397348733719696768673500151156801,
        encodes := Ra0510.tableCode_eq ▸ encodesTable_tableCode Ra0510.cycles } 27135
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0511.table, code := 22576777298685868157643606154281226305,
        encodes := Ra0511.tableCode_eq ▸ encodesTable_tableCode Ra0511.cycles } 27459
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0512.table, code := 22576858428326700615964603793025536065,
        encodes := Ra0512.tableCode_eq ▸ encodesTable_tableCode Ra0512.cycles } 27462
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 4,
    Data.profiles (448 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (448 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 4,
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

end Cslib.RelationAlgebra.Catalogue.I1S2N1.Models007
