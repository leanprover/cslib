/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0193
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0194
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0195
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0196
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0197
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0198
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0199
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0200
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0201
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0202
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0203
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0204
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0205
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0206
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0207
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0208
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0209
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0210
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0211
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0212
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0213
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0214
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0215
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0216
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0217
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0218
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0219
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0220
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0221
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0222
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0223
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0224
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0225
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0226
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0227
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0228
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0229
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0230
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0231
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0232
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0233
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0234
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0235
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0236
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0237
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0238
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0239
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0240
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0241
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0242
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0243
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0244
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0245
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0246
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0247
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0248
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0249
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0250
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0251
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0252
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0253
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0254
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0255
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra0256

/-!
# Certified models 193–256 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models003

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0193.table, code := 9588813623735413369399540104709804097,
        encodes := Ra0193.tableCode_eq ▸ encodesTable_tableCode Ra0193.cycles } 61406
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0194.table, code := 9588813623735413369399540106857287745,
        encodes := Ra0194.tableCode_eq ▸ encodesTable_tableCode Ra0194.cycles } 61407
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0195.table, code := 9588732494179205790076821724993949761,
        encodes := Ra0195.tableCode_eq ▸ encodesTable_tableCode Ra0195.cycles } 61415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0196.table, code := 9588813623815202545119356433960538177,
        encodes := Ra0196.tableCode_eq ▸ encodesTable_tableCode Ra0196.cycles } 61419
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0197.table, code := 9588813623817620396758587897775657025,
        encodes := Ra0197.tableCode_eq ▸ encodesTable_tableCode Ra0197.cycles } 61422
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0198.table, code := 9588813623817620396758587899923140673,
        encodes := Ra0198.tableCode_eq ▸ encodesTable_tableCode Ra0198.cycles } 61423
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0199.table, code := 9588732494179205792526780059722453057,
        encodes := Ra0199.tableCode_eq ▸ encodesTable_tableCode Ra0199.cycles } 61431
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0200.table, code := 9588813623815202547569314768689041473,
        encodes := Ra0200.tableCode_eq ▸ encodesTable_tableCode Ra0200.cycles } 61435
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0201.table, code := 9588813623817620399136488567599272001,
        encodes := Ra0201.tableCode_eq ▸ encodesTable_tableCode Ra0201.cycles } 61437
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0202.table, code := 9588813623817620399208546232504160321,
        encodes := Ra0202.tableCode_eq ▸ encodesTable_tableCode Ra0202.cycles } 61438
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0203.table, code := 9588813623817620399208546234651643969,
        encodes := Ra0203.tableCode_eq ▸ encodesTable_tableCode Ra0203.cycles } 61439
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0204.table, code := 9591247512887853944292111225421303873,
        encodes := Ra0204.tableCode_eq ▸ encodesTable_tableCode Ra0204.cycles } 64414
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0205.table, code := 9591247512887853944292111227568787521,
        encodes := Ra0205.tableCode_eq ▸ encodesTable_tableCode Ra0205.cycles } 64415
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0206.table, code := 9591247512970060974029059688310771777,
        encodes := Ra0206.tableCode_eq ▸ encodesTable_tableCode Ra0206.cycles } 64445
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0207.table, code := 9591247512970060974101117353215660097,
        encodes := Ra0207.tableCode_eq ▸ encodesTable_tableCode Ra0207.cycles } 64446
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0208.table, code := 9591247512970060974101117355363143745,
        encodes := Ra0208.tableCode_eq ▸ encodesTable_tableCode Ra0208.cycles } 64447
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0209.table, code := 9594005920676159962966559988855869505,
        encodes := Ra0209.tableCode_eq ▸ encodesTable_tableCode Ra0209.cycles } 64509
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0210.table, code := 9594005920676159963038617653760757825,
        encodes := Ra0210.tableCode_eq ▸ encodesTable_tableCode Ra0210.cycles } 64510
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0211.table, code := 9594005920676159963038617655908241473,
        encodes := Ra0211.tableCode_eq ▸ encodesTable_tableCode Ra0211.cycles } 64511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0212.table, code := 9591247512887853948903797245996175425,
        encodes := Ra0212.tableCode_eq ▸ encodesTable_tableCode Ra0212.cycles } 65439
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0213.table, code := 9591247512970060976262845039062028353,
        encodes := Ra0213.tableCode_eq ▸ encodesTable_tableCode Ra0213.cycles } 65455
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0214.table, code := 9591247512970060978712803373790531649,
        encodes := Ra0214.tableCode_eq ▸ encodesTable_tableCode Ra0214.cycles } 65471
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0215.table, code := 9594005920676159965200345339607126081,
        encodes := Ra0215.tableCode_eq ▸ encodesTable_tableCode Ra0215.cycles } 65519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0216.table, code := 9594005920676159967650303674335629377,
        encodes := Ra0216.tableCode_eq ▸ encodesTable_tableCode Ra0216.cycles } 65535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0217.table, code := 4074594205465841675507359922530816065,
        encodes := Ra0217.tableCode_eq ▸ encodesTable_tableCode Ra0217.cycles } 67583
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0218.table, code := 4074594205620584337215357083424395329,
        encodes := Ra0218.tableCode_eq ▸ encodesTable_tableCode Ra0218.cycles } 69631
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0219.table, code := 4079786502324381239337431343787413569,
        encodes := Ra0219.tableCode_eq ▸ encodesTable_tableCode Ra0219.cycles } 70655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0220.table, code := 4079786502324381243949117362214801473,
        encodes := Ra0220.tableCode_eq ▸ encodesTable_tableCode Ra0220.cycles } 71679
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0221.table, code := 1417841936375254676283354851804713025,
        encodes := Ra0221.tableCode_eq ▸ encodesTable_tableCode Ra0221.cycles } 72085
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0222.table, code := 4077028092205266397099178030000246849,
        encodes := Ra0222.tableCode_eq ▸ encodesTable_tableCode Ra0222.cycles } 72477
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0223.table, code := 4077028094690817882226864409289166913,
        encodes := Ra0223.tableCode_eq ▸ encodesTable_tableCode Ra0223.cycles } 72605
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0224.table, code := 4079786502479123901045428504680992833,
        encodes := Ra0224.tableCode_eq ▸ encodesTable_tableCode Ra0224.cycles } 72703
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0225.table, code := 1417841936375254680895040870232100929,
        encodes := Ra0225.tableCode_eq ▸ encodesTable_tableCode Ra0225.cycles } 73109
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0226.table, code := 4077028092205266401710864048427634753,
        encodes := Ra0226.tableCode_eq ▸ encodesTable_tableCode Ra0226.cycles } 73501
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0227.table, code := 4077028094690817886838550427716554817,
        encodes := Ra0227.tableCode_eq ▸ encodesTable_tableCode Ra0227.cycles } 73629
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0228.table, code := 4079786502479123905657114523108380737,
        encodes := Ra0228.tableCode_eq ▸ encodesTable_tableCode Ra0228.cycles } 73727
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0229.table, code := 4074594210881829799326128431098499137,
        encodes := Ra0229.tableCode_eq ▸ encodesTable_tableCode Ra0229.cycles } 77823
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0230.table, code := 1417841941563964504117234498703462465,
        encodes := Ra0230.tableCode_eq ▸ encodesTable_tableCode Ra0230.cycles } 78247
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0231.table, code := 4079786505100075216320516312172597313,
        encodes := Ra0231.tableCode_eq ▸ encodesTable_tableCode Ra0231.cycles } 78719
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0232.table, code := 4079786507585626701448202691461517377,
        encodes := Ra0232.tableCode_eq ▸ encodesTable_tableCode Ra0232.cycles } 78847
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0233.table, code := 1417841941563964508728920517130850369,
        encodes := Ra0233.tableCode_eq ▸ encodesTable_tableCode Ra0233.cycles } 79271
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0234.table, code := 4079786505100075220932202330599985217,
        encodes := Ra0234.tableCode_eq ▸ encodesTable_tableCode Ra0234.cycles } 79743
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0235.table, code := 4079786507585626706059888709888905281,
        encodes := Ra0235.tableCode_eq ▸ encodesTable_tableCode Ra0235.cycles } 79871
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0236.table, code := 1417841941718707168275189994325545025,
        encodes := Ra0236.tableCode_eq ▸ encodesTable_tableCode Ra0236.cycles } 80311
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0237.table, code := 4079786505254817878028513473066176577,
        encodes := Ra0237.tableCode_eq ▸ encodesTable_tableCode Ra0237.cycles } 80767
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0238.table, code := 4079786507740369363156199852355096641,
        encodes := Ra0238.tableCode_eq ▸ encodesTable_tableCode Ra0238.cycles } 80895
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0239.table, code := 1417841941718707172886876012752932929,
        encodes := Ra0239.tableCode_eq ▸ encodesTable_tableCode Ra0239.cycles } 81335
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0240.table, code := 4079786505254817882640199491493564481,
        encodes := Ra0240.tableCode_eq ▸ encodesTable_tableCode Ra0240.cycles } 81791
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0241.table, code := 4079786507740369367767885870782484545,
        encodes := Ra0241.tableCode_eq ▸ encodesTable_tableCode Ra0241.cycles } 81919
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0242.table, code := 4251051325607364803818127331311226945,
        encodes := Ra0242.tableCode_eq ▸ encodesTable_tableCode Ra0242.cycles } 83815
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0243.table, code := 4251132455245779410499893504092934209,
        encodes := Ra0243.tableCode_eq ▸ encodesTable_tableCode Ra0243.cycles } 83822
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0244.table, code := 4251132455245779410499893506240417857,
        encodes := Ra0244.tableCode_eq ▸ encodesTable_tableCode Ra0244.cycles } 83823
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0245.table, code := 4251051325607364806268085666039730241,
        encodes := Ra0245.tableCode_eq ▸ encodesTable_tableCode Ra0245.cycles } 83831
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0246.table, code := 4251132455245779412949851838821437505,
        encodes := Ra0246.tableCode_eq ▸ encodesTable_tableCode Ra0246.cycles } 83838
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0247.table, code := 4251132455245779412949851840968921153,
        encodes := Ra0247.tableCode_eq ▸ encodesTable_tableCode Ra0247.cycles } 83839
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0248.table, code := 4251051328092916291395772045328650305,
        encodes := Ra0248.tableCode_eq ▸ encodesTable_tableCode Ra0248.cycles } 83959
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0249.table, code := 4251132457731330898077538218110357569,
        encodes := Ra0249.tableCode_eq ▸ encodesTable_tableCode Ra0249.cycles } 83966
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0250.table, code := 4251132457731330898077538220257841217,
        encodes := Ra0250.tableCode_eq ▸ encodesTable_tableCode Ra0250.cycles } 83967
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0251.table, code := 4251051325762107465526124490057322561,
        encodes := Ra0251.tableCode_eq ▸ encodesTable_tableCode Ra0251.cycles } 85862
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0252.table, code := 4251051325762107465526124492204806209,
        encodes := Ra0252.tableCode_eq ▸ encodesTable_tableCode Ra0252.cycles } 85863
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0253.table, code := 4251132455400522072207890664986513473,
        encodes := Ra0253.tableCode_eq ▸ encodesTable_tableCode Ra0253.cycles } 85870
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0254.table, code := 4251132455400522072207890667133997121,
        encodes := Ra0254.tableCode_eq ▸ encodesTable_tableCode Ra0254.cycles } 85871
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0255.table, code := 4251051325762107467976082824785825857,
        encodes := Ra0255.tableCode_eq ▸ encodesTable_tableCode Ra0255.cycles } 85878
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra0256.table, code := 4251051325762107467976082826933309505,
        encodes := Ra0256.tableCode_eq ▸ encodesTable_tableCode Ra0256.cycles } 85879
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (192 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (192 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (192 + i.val) 0 ≤ Data.profiles (192 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (192 + i.val) 0 = Data.canonicalMask (192 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (192 + i.val) < Data.canonicalMask (192 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (192 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models003
