/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Mathlib.Tactic.FinCases
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1729
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1730
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1731
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1732
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1733
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1734
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1735
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1736
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1737
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1738
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1739
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1740
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1741
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1742
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1743
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1744
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1745
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1746
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1747
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1748
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1749
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1750
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1751
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1752
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1753
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1754
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1755
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1756
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1757
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1758
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1759
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1760
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1761
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1762
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1763
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1764
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1765
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1766
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1767
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1768
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1769
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1770
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1771
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1772
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1773
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1774
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1775
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1776
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1777
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1778
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1779
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1780
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1781
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1782
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1783
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1784
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1785
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1786
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1787
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1788
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1789
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1790
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1791
public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Ra1792

/-!
# Certified models 1729–1792 of the ⟨1, 4, 0⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Models027

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1729.table, code := 9741824309178522461866334747640467521,
        encodes := Ra1729.tableCode_eq ▸ encodesTable_tableCode Ra1729.cycles } 239502
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1730.table, code := 9741824309178522461866334749787951169,
        encodes := Ra1730.tableCode_eq ▸ encodesTable_tableCode Ra1730.cycles } 239503
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1731.table, code := 9744501587325996024669744204911743041,
        encodes := Ra1731.tableCode_eq ▸ encodesTable_tableCode Ra1731.cycles } 239601
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1732.table, code := 9744501587325996024741801871964115009,
        encodes := Ra1732.tableCode_eq ▸ encodesTable_tableCode Ra1732.cycles } 239603
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1733.table, code := 9744501587328413876308975670874345537,
        encodes := Ra1733.tableCode_eq ▸ encodesTable_tableCode Ra1733.cycles } 239605
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1734.table, code := 9744501587328413876381033337926717505,
        encodes := Ra1734.tableCode_eq ▸ encodesTable_tableCode Ra1734.cycles } 239607
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1735.table, code := 9744582716964410631351510379840933953,
        encodes := Ra1735.tableCode_eq ▸ encodesTable_tableCode Ra1735.cycles } 239609
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1736.table, code := 9744582716964410631423568046893305921,
        encodes := Ra1736.tableCode_eq ▸ encodesTable_tableCode Ra1736.cycles } 239611
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1737.table, code := 9744582716966828482990741843656052801,
        encodes := Ra1737.tableCode_eq ▸ encodesTable_tableCode Ra1737.cycles } 239612
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1738.table, code := 9744582716966828482990741845803536449,
        encodes := Ra1738.tableCode_eq ▸ encodesTable_tableCode Ra1738.cycles } 239613
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1739.table, code := 9744582716966828483062799510708424769,
        encodes := Ra1739.tableCode_eq ▸ encodesTable_tableCode Ra1739.cycles } 239614
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1740.table, code := 9744582716966828483062799512855908417,
        encodes := Ra1740.tableCode_eq ▸ encodesTable_tableCode Ra1740.cycles } 239615
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1741.table, code := 9744501584997605050511385784802873409,
        encodes := Ra1741.tableCode_eq ▸ encodesTable_tableCode Ra1741.cycles } 241511
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1742.table, code := 9744582714636019657193151957584580673,
        encodes := Ra1742.tableCode_eq ▸ encodesTable_tableCode Ra1742.cycles } 241518
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1743.table, code := 9744582714636019657193151959732064321,
        encodes := Ra1743.tableCode_eq ▸ encodesTable_tableCode Ra1743.cycles } 241519
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1744.table, code := 9744501584997605052889286452479004737,
        encodes := Ra1744.tableCode_eq ▸ encodesTable_tableCode Ra1744.cycles } 241525
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1745.table, code := 9744501584997605052961344119531376705,
        encodes := Ra1745.tableCode_eq ▸ encodesTable_tableCode Ra1745.cycles } 241527
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1746.table, code := 9744582714636019659571052625260712001,
        encodes := Ra1746.tableCode_eq ▸ encodesTable_tableCode Ra1746.cycles } 241532
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1747.table, code := 9744582714636019659571052627408195649,
        encodes := Ra1747.tableCode_eq ▸ encodesTable_tableCode Ra1747.cycles } 241533
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1748.table, code := 9744582714636019659643110292313083969,
        encodes := Ra1748.tableCode_eq ▸ encodesTable_tableCode Ra1748.cycles } 241534
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1749.table, code := 9744582714636019659643110294460567617,
        encodes := Ra1749.tableCode_eq ▸ encodesTable_tableCode Ra1749.cycles } 241535
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1750.table, code := 9744501587480738683999840698129190977,
        encodes := Ra1750.tableCode_eq ▸ encodesTable_tableCode Ra1750.cycles } 241635
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1751.table, code := 9744501587483156535639072164091793473,
        encodes := Ra1751.tableCode_eq ▸ encodesTable_tableCode Ra1751.cycles } 241639
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1752.table, code := 9744582717119153290681606873058381889,
        encodes := Ra1752.tableCode_eq ▸ encodesTable_tableCode Ra1752.cycles } 241643
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1753.table, code := 9744582717121571142320838336873500737,
        encodes := Ra1753.tableCode_eq ▸ encodesTable_tableCode Ra1753.cycles } 241646
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1754.table, code := 9744582717121571142320838339020984385,
        encodes := Ra1754.tableCode_eq ▸ encodesTable_tableCode Ra1754.cycles } 241647
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1755.table, code := 9744501587480738686377741365805322305,
        encodes := Ra1755.tableCode_eq ▸ encodesTable_tableCode Ra1755.cycles } 241649
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1756.table, code := 9744501587480738686449799032857694273,
        encodes := Ra1756.tableCode_eq ▸ encodesTable_tableCode Ra1756.cycles } 241651
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1757.table, code := 9744501587483156538016972831767924801,
        encodes := Ra1757.tableCode_eq ▸ encodesTable_tableCode Ra1757.cycles } 241653
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1758.table, code := 9744501587483156538089030498820296769,
        encodes := Ra1758.tableCode_eq ▸ encodesTable_tableCode Ra1758.cycles } 241655
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1759.table, code := 9744582717119153293059507540734513217,
        encodes := Ra1759.tableCode_eq ▸ encodesTable_tableCode Ra1759.cycles } 241657
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1760.table, code := 9744582717119153293131565207786885185,
        encodes := Ra1760.tableCode_eq ▸ encodesTable_tableCode Ra1760.cycles } 241659
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1761.table, code := 9744582717121571144698739004549632065,
        encodes := Ra1761.tableCode_eq ▸ encodesTable_tableCode Ra1761.cycles } 241660
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1762.table, code := 9744582717121571144698739006697115713,
        encodes := Ra1762.tableCode_eq ▸ encodesTable_tableCode Ra1762.cycles } 241661
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1763.table, code := 9744582717121571144770796671602004033,
        encodes := Ra1763.tableCode_eq ▸ encodesTable_tableCode Ra1763.cycles } 241662
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1764.table, code := 9744582717121571144770796673749487681,
        encodes := Ra1764.tableCode_eq ▸ encodesTable_tableCode Ra1764.cycles } 241663
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1765.table, code := 9663615258496923180345391212872863809,
        encodes := Ra1765.tableCode_eq ▸ encodesTable_tableCode Ra1765.cycles } 242330
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1766.table, code := 9663615258496923180345391215020347457,
        encodes := Ra1766.tableCode_eq ▸ encodesTable_tableCode Ra1766.cycles } 242331
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1767.table, code := 9666373666203022169282891513417961537,
        encodes := Ra1767.tableCode_eq ▸ encodesTable_tableCode Ra1767.cycles } 242394
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1768.table, code := 9666373666203022169282891515565445185,
        encodes := Ra1768.tableCode_eq ▸ encodesTable_tableCode Ra1768.cycles } 242395
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1769.table, code := 9749693881701401955011360712842022977,
        encodes := Ra1769.tableCode_eq ▸ encodesTable_tableCode Ra1769.cycles } 242549
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1770.table, code := 9749693881701401955083418379894394945,
        encodes := Ra1770.tableCode_eq ▸ encodesTable_tableCode Ra1770.cycles } 242551
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1771.table, code := 9749775011339816561765184552676102209,
        encodes := Ra1771.tableCode_eq ▸ encodesTable_tableCode Ra1771.cycles } 242558
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1772.table, code := 9749775011339816561765184554823585857,
        encodes := Ra1772.tableCode_eq ▸ encodesTable_tableCode Ra1772.cycles } 242559
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1773.table, code := 9749693884184535588499815626168340545,
        encodes := Ra1773.tableCode_eq ▸ encodesTable_tableCode Ra1773.cycles } 242673
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1774.table, code := 9749693884184535588571873293220712513,
        encodes := Ra1774.tableCode_eq ▸ encodesTable_tableCode Ra1774.cycles } 242675
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1775.table, code := 9749693884186953440139047092130943041,
        encodes := Ra1775.tableCode_eq ▸ encodesTable_tableCode Ra1775.cycles } 242677
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1776.table, code := 9749693884186953440211104759183315009,
        encodes := Ra1776.tableCode_eq ▸ encodesTable_tableCode Ra1776.cycles } 242679
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1777.table, code := 9749775013822950195253639468149903425,
        encodes := Ra1777.tableCode_eq ▸ encodesTable_tableCode Ra1777.cycles } 242683
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1778.table, code := 9749775013825368046892870931965022273,
        encodes := Ra1778.tableCode_eq ▸ encodesTable_tableCode Ra1778.cycles } 242686
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1779.table, code := 9749775013825368046892870934112505921,
        encodes := Ra1779.tableCode_eq ▸ encodesTable_tableCode Ra1779.cycles } 242687
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1780.table, code := 9663615258496923184957077233447735361,
        encodes := Ra1780.tableCode_eq ▸ encodesTable_tableCode Ra1780.cycles } 243355
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1781.table, code := 9666373666203022171444619199264329793,
        encodes := Ra1781.tableCode_eq ▸ encodesTable_tableCode Ra1781.cycles } 243403
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1782.table, code := 9666373666203022173894577533992833089,
        encodes := Ra1782.tableCode_eq ▸ encodesTable_tableCode Ra1782.cycles } 243419
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1783.table, code := 9749693881701401959623046731269410881,
        encodes := Ra1783.tableCode_eq ▸ encodesTable_tableCode Ra1783.cycles } 243573
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1784.table, code := 9749693881701401959695104398321782849,
        encodes := Ra1784.tableCode_eq ▸ encodesTable_tableCode Ra1784.cycles } 243575
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1785.table, code := 9749775011339816566304812904051118145,
        encodes := Ra1785.tableCode_eq ▸ encodesTable_tableCode Ra1785.cycles } 243580
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1786.table, code := 9749775011339816566304812906198601793,
        encodes := Ra1786.tableCode_eq ▸ encodesTable_tableCode Ra1786.cycles } 243581
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1787.table, code := 9749775011339816566376870571103490113,
        encodes := Ra1787.tableCode_eq ▸ encodesTable_tableCode Ra1787.cycles } 243582
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1788.table, code := 9749775011339816566376870573250973761,
        encodes := Ra1788.tableCode_eq ▸ encodesTable_tableCode Ra1788.cycles } 243583
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1789.table, code := 9749693884184535593111501644595728449,
        encodes := Ra1789.tableCode_eq ▸ encodesTable_tableCode Ra1789.cycles } 243697
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1790.table, code := 9749693884184535593183559311648100417,
        encodes := Ra1790.tableCode_eq ▸ encodesTable_tableCode Ra1790.cycles } 243699
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1791.table, code := 9749693884186953444750733110558330945,
        encodes := Ra1791.tableCode_eq ▸ encodesTable_tableCode Ra1791.cycles } 243701
      (by decide +kernel),
    ProfiledCycleTable.ofEncoded Data.cycleReps
      { table := Ra1792.table, code := 9749693884186953444822790777610702913,
        encodes := Ra1792.tableCode_eq ▸ encodesTable_tableCode Ra1792.cycles } 243703
      (by decide +kernel)]

/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1728 + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask (1728 + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin 64, ∀ p : Fin 24,
    Data.profiles (1728 + i.val) 0 ≤ Data.profiles (1728 + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin 64,
    Data.profiles (1728 + i.val) 0 = Data.canonicalMask (1728 + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin 64,
    Data.canonicalMask (1728 + i.val) < Data.canonicalMask (1728 + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin 64,
    (entries.getD i.val fallback).profile =
      Data.canonicalMask (1728 + i.val) := by
  intro i
  fin_cases i <;> rfl

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Models027
