/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/
module
public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.NetworkRefutation
/-!
# Catalogue algebra ⟨1, 3, 0⟩, number 53
Entry 53 in the ⟨1, 3, 0⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aac abb abc acc bbc bcc aaa bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
A checked finite-network obstruction proves that no representation exists.
-/
@[expose] public section
namespace Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra53
/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 3 0) :=
  let a : DiversityAtom 3 0 := Sum.inl 0
  let b : DiversityAtom 3 0 := Sum.inl 1
  let c : DiversityAtom 3 0 := Sum.inl 2
  {(a, a, c), (a, b, b), (a, b, c), (a, c, c), (b, b, c), (b, c, c), (a, a, a), (b, b, b)}
private theorem tableCode_eq : tableCode cycles = 9144822672439542817 := by decide +kernel

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 3 0 where
  cycles := cycles
  associative := atomCompositionAssociative_of_assocCheck (by
    rw [tableCode_eq]
    decide +kernel)
/-- The finite relation algebra determined by this table. -/
abbrev Algebra : Type := Complex table
/-- This algebra has the signature of its catalogue row. -/
theorem signature : HasSignature Algebra 1 3 0 :=
  Complex.hasSignature table
/-- Atomic multiplication is characterized exactly by the listed cycles and their closure. -/
theorem cycles_iff (x y z : Atom 3 0) :
    Complex.atom table z ≤ Complex.atom table x * Complex.atom table y ↔
      cycleClosure cycles x y z :=
  Complex.atom_le_mul_iff table x y z
private abbrev da : DiversityAtom 3 0 := .inl 0
private abbrev db : DiversityAtom 3 0 := .inl 1
private abbrev dc : DiversityAtom 3 0 := .inl 2
private abbrev a : Atom 3 0 := some da
private abbrev b : Atom 3 0 := some db
private abbrev c : Atom 3 0 := some dc
private def matrix0 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, b],
  [a, none, c, c, a, a, b, b],
  [b, c, none, a, c, b, b, b],
  [c, c, a, none, a, c, b, b],
  [a, a, c, a, none, c, b, c],
  [a, a, b, c, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, b, b, b, c, b, a, none]]
private def node0 : NetworkRefutation.Certificate 3 0 :=
  .node 4 7 a a [
    ]
private theorem checked0 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix0) node0 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix0) ⟨4, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix1 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, b],
  [a, none, c, c, a, a, b, b],
  [b, c, none, a, c, b, b, b],
  [c, c, a, none, a, c, b, c],
  [a, a, c, a, none, c, b, c],
  [a, a, b, c, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, b, b, c, c, b, a, none]]
private def node1 : NetworkRefutation.Certificate 3 0 :=
  .node 3 7 a a [
    ]
private theorem checked1 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix1) node1 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix1) ⟨3, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix2 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, b],
  [a, none, c, c, a, a, b, c],
  [b, c, none, a, c, b, b, b],
  [c, c, a, none, a, c, b, b],
  [a, a, c, a, none, c, b, c],
  [a, a, b, c, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, c, b, b, c, b, a, none]]
private def node2 : NetworkRefutation.Certificate 3 0 :=
  .node 1 7 a a [
    ]
private theorem checked2 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix2) node2 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix2) ⟨1, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix3 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, c],
  [a, none, c, c, a, a, b, b],
  [b, c, none, a, c, b, b, b],
  [c, c, a, none, a, c, b, b],
  [a, a, c, a, none, c, b, c],
  [a, a, b, c, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, b, b, b, c, b, a, none]]
private def node3 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked3 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix3) node3 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix3) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix4 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, c],
  [a, none, c, c, a, a, b, c],
  [b, c, none, a, c, b, b, b],
  [c, c, a, none, a, c, b, b],
  [a, a, c, a, none, c, b, c],
  [a, a, b, c, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, c, b, b, c, b, a, none]]
private def node4 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked4 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix4) node4 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix4) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix5 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b],
  [a, none, c, c, a, a, b],
  [b, c, none, a, c, b, b],
  [c, c, a, none, a, c, b],
  [a, a, c, a, none, c, b],
  [a, a, b, c, c, none, b],
  [b, b, b, b, b, b, none]]
private def node5 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 c a [
    .cache matrix0 node0,
    .cache matrix1 node1,
    .cache matrix2 node2,
    .cache matrix3 node3,
    .cache matrix4 node4]
private theorem checked5 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix5) node5 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix5) ⟨4, by decide⟩ ⟨6, by decide⟩ c a = [
        ![db, db, db, db, dc, db, da],
        ![db, db, db, dc, dc, db, da],
        ![db, dc, db, db, dc, db, da],
        ![dc, db, db, db, dc, db, da],
        ![dc, dc, db, db, dc, db, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked0, checked1, checked2, checked3, checked4]
  decide +kernel
private def matrix6 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b],
  [a, none, c, c, a, a, b],
  [b, c, none, a, c, b, b],
  [c, c, a, none, a, c, b],
  [a, a, c, a, none, c, c],
  [a, a, b, c, c, none, b],
  [b, b, b, b, c, b, none]]
private def node6 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked6 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix6) node6 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix6) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix7 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b],
  [a, none, c, c, a, a, b],
  [b, c, none, a, c, b, b],
  [c, c, a, none, a, c, c],
  [a, a, c, a, none, c, b],
  [a, a, b, c, c, none, b],
  [b, b, b, c, b, b, none]]
private def node7 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked7 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix7) node7 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix7) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix8 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b],
  [a, none, c, c, a, a, b],
  [b, c, none, a, c, b, b],
  [c, c, a, none, a, c, c],
  [a, a, c, a, none, c, c],
  [a, a, b, c, c, none, b],
  [b, b, b, c, c, b, none]]
private def node8 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked8 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix8) node8 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix8) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix9 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b],
  [a, none, c, c, a, a, c],
  [b, c, none, a, c, b, b],
  [c, c, a, none, a, c, b],
  [a, a, c, a, none, c, b],
  [a, a, b, c, c, none, b],
  [b, c, b, b, b, b, none]]
private def node9 : NetworkRefutation.Certificate 3 0 :=
  .node 1 6 a a [
    ]
private theorem checked9 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix9) node9 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix9) ⟨1, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix10 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b],
  [a, none, c, c, a, a, c],
  [b, c, none, a, c, b, b],
  [c, c, a, none, a, c, b],
  [a, a, c, a, none, c, c],
  [a, a, b, c, c, none, b],
  [b, c, b, b, c, b, none]]
private def node10 : NetworkRefutation.Certificate 3 0 :=
  .node 1 6 a a [
    ]
private theorem checked10 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix10) node10 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix10) ⟨1, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix11 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, c],
  [a, none, c, c, a, a, b],
  [b, c, none, a, c, b, b],
  [c, c, a, none, a, c, b],
  [a, a, c, a, none, c, b],
  [a, a, b, c, c, none, b],
  [c, b, b, b, b, b, none]]
private def node11 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked11 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix11) node11 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix11) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix12 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, c],
  [a, none, c, c, a, a, b],
  [b, c, none, a, c, b, b],
  [c, c, a, none, a, c, b],
  [a, a, c, a, none, c, c],
  [a, a, b, c, c, none, b],
  [c, b, b, b, c, b, none]]
private def node12 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked12 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix12) node12 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix12) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix13 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, c],
  [a, none, c, c, a, a, c],
  [b, c, none, a, c, b, b],
  [c, c, a, none, a, c, b],
  [a, a, c, a, none, c, b],
  [a, a, b, c, c, none, b],
  [c, c, b, b, b, b, none]]
private def node13 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked13 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix13) node13 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix13) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix14 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, c],
  [a, none, c, c, a, a, c],
  [b, c, none, a, c, b, b],
  [c, c, a, none, a, c, b],
  [a, a, c, a, none, c, c],
  [a, a, b, c, c, none, b],
  [c, c, b, b, c, b, none]]
private def node14 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked14 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix14) node14 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix14) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix15 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a],
  [a, none, c, c, a, a],
  [b, c, none, a, c, b],
  [c, c, a, none, a, c],
  [a, a, c, a, none, c],
  [a, a, b, c, c, none]]
private def node15 : NetworkRefutation.Certificate 3 0 :=
  .node 2 5 b b [
    .cache matrix5 node5,
    .cache matrix6 node6,
    .cache matrix7 node7,
    .cache matrix8 node8,
    .cache matrix9 node9,
    .cache matrix10 node10,
    .cache matrix11 node11,
    .cache matrix12 node12,
    .cache matrix13 node13,
    .cache matrix14 node14]
private theorem checked15 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix15) node15 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix15) ⟨2, by decide⟩ ⟨5, by decide⟩ b b = [
        ![db, db, db, db, db, db],
        ![db, db, db, db, dc, db],
        ![db, db, db, dc, db, db],
        ![db, db, db, dc, dc, db],
        ![db, dc, db, db, db, db],
        ![db, dc, db, db, dc, db],
        ![dc, db, db, db, db, db],
        ![dc, db, db, db, dc, db],
        ![dc, dc, db, db, db, db],
        ![dc, dc, db, db, dc, db]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13,
    checked14]
  decide +kernel
private def matrix16 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b, b, b],
  [a, none, c, c, a, b, b, b],
  [b, c, none, a, c, a, b, b],
  [c, c, a, none, a, c, b, c],
  [a, a, c, a, none, c, b, b],
  [b, b, a, c, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, b, b, c, b, b, a, none]]
private def node16 : NetworkRefutation.Certificate 3 0 :=
  .node 3 7 a a [
    ]
private theorem checked16 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix16) node16 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix16) ⟨3, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix17 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b, b, b],
  [a, none, c, c, a, b, b, b],
  [b, c, none, a, c, a, b, b],
  [c, c, a, none, a, c, b, c],
  [a, a, c, a, none, c, b, c],
  [b, b, a, c, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, b, b, c, c, b, a, none]]
private def node17 : NetworkRefutation.Certificate 3 0 :=
  .node 3 7 a a [
    ]
private theorem checked17 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix17) node17 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix17) ⟨3, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix18 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b, b, b],
  [a, none, c, c, a, b, b, b],
  [b, c, none, a, c, a, b, c],
  [c, c, a, none, a, c, b, c],
  [a, a, c, a, none, c, b, b],
  [b, b, a, c, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, b, c, c, b, b, a, none]]
private def node18 : NetworkRefutation.Certificate 3 0 :=
  .node 2 7 a a [
    ]
private theorem checked18 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix18) node18 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix18) ⟨2, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix19 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b, b],
  [a, none, c, c, a, b, b],
  [b, c, none, a, c, a, b],
  [c, c, a, none, a, c, b],
  [a, a, c, a, none, c, b],
  [b, b, a, c, c, none, b],
  [b, b, b, b, b, b, none]]
private def node19 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 c a [
    .cache matrix16 node16,
    .cache matrix17 node17,
    .cache matrix18 node18]
private theorem checked19 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix19) node19 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix19) ⟨3, by decide⟩ ⟨6, by decide⟩ c a = [
        ![db, db, db, dc, db, db, da],
        ![db, db, db, dc, dc, db, da],
        ![db, db, dc, dc, db, db, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked16, checked17, checked18]
  decide +kernel
private def matrix20 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b, b],
  [a, none, c, c, a, b, b],
  [b, c, none, a, c, a, b],
  [c, c, a, none, a, c, b],
  [a, a, c, a, none, c, c],
  [b, b, a, c, c, none, b],
  [b, b, b, b, c, b, none]]
private def node20 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked20 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix20) node20 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix20) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix21 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b, b],
  [a, none, c, c, a, b, b],
  [b, c, none, a, c, a, b],
  [c, c, a, none, a, c, c],
  [a, a, c, a, none, c, b],
  [b, b, a, c, c, none, b],
  [b, b, b, c, b, b, none]]
private def node21 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked21 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix21) node21 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix21) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix22 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b, b],
  [a, none, c, c, a, b, b],
  [b, c, none, a, c, a, b],
  [c, c, a, none, a, c, c],
  [a, a, c, a, none, c, c],
  [b, b, a, c, c, none, b],
  [b, b, b, c, c, b, none]]
private def node22 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked22 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix22) node22 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix22) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix23 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b, b],
  [a, none, c, c, a, b, b],
  [b, c, none, a, c, a, c],
  [c, c, a, none, a, c, b],
  [a, a, c, a, none, c, b],
  [b, b, a, c, c, none, b],
  [b, b, c, b, b, b, none]]
private def node23 : NetworkRefutation.Certificate 3 0 :=
  .node 2 6 a a [
    ]
private theorem checked23 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix23) node23 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix23) ⟨2, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix24 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b, b],
  [a, none, c, c, a, b, b],
  [b, c, none, a, c, a, c],
  [c, c, a, none, a, c, c],
  [a, a, c, a, none, c, b],
  [b, b, a, c, c, none, b],
  [b, b, c, c, b, b, none]]
private def node24 : NetworkRefutation.Certificate 3 0 :=
  .node 2 6 a a [
    ]
private theorem checked24 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix24) node24 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix24) ⟨2, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix25 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b, b, c],
  [a, none, c, c, a, b, c, a],
  [b, c, none, a, c, a, b, b],
  [c, c, a, none, a, c, b, b],
  [a, a, c, a, none, c, b, c],
  [b, b, a, c, c, none, b, b],
  [b, c, b, b, b, b, none, a],
  [c, a, b, b, c, b, a, none]]
private def node25 : NetworkRefutation.Certificate 3 0 :=
  .node 1 2 a a [
    ]
private theorem checked25 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix25) node25 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix25) ⟨1, by decide⟩ ⟨2, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix26 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b, b],
  [a, none, c, c, a, b, c],
  [b, c, none, a, c, a, b],
  [c, c, a, none, a, c, b],
  [a, a, c, a, none, c, b],
  [b, b, a, c, c, none, b],
  [b, c, b, b, b, b, none]]
private def node26 : NetworkRefutation.Certificate 3 0 :=
  .node 1 6 a a [
    .cache matrix25 node25]
private theorem checked26 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix26) node26 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix26) ⟨1, by decide⟩ ⟨6, by decide⟩ a a = [
        ![dc, da, db, db, dc, db, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked25]
  decide +kernel
private def matrix27 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b, b],
  [a, none, c, c, a, b, c],
  [b, c, none, a, c, a, b],
  [c, c, a, none, a, c, b],
  [a, a, c, a, none, c, c],
  [b, b, a, c, c, none, b],
  [b, c, b, b, c, b, none]]
private def node27 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked27 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix27) node27 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix27) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix28 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b],
  [a, none, c, c, a, b],
  [b, c, none, a, c, a],
  [c, c, a, none, a, c],
  [a, a, c, a, none, c],
  [b, b, a, c, c, none]]
private def node28 : NetworkRefutation.Certificate 3 0 :=
  .node 0 5 b b [
    .cache matrix19 node19,
    .cache matrix20 node20,
    .cache matrix21 node21,
    .cache matrix22 node22,
    .cache matrix23 node23,
    .cache matrix24 node24,
    .cache matrix26 node26,
    .cache matrix27 node27]
private theorem checked28 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix28) node28 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix28) ⟨0, by decide⟩ ⟨5, by decide⟩ b b = [
        ![db, db, db, db, db, db],
        ![db, db, db, db, dc, db],
        ![db, db, db, dc, db, db],
        ![db, db, db, dc, dc, db],
        ![db, db, dc, db, db, db],
        ![db, db, dc, dc, db, db],
        ![db, dc, db, db, db, db],
        ![db, dc, db, db, dc, db]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked19, checked20, checked21, checked22, checked23, checked24, checked26, checked27]
  decide +kernel
private def matrix29 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, b],
  [a, none, c, c, a, b],
  [b, c, none, a, c, b],
  [c, c, a, none, a, c],
  [a, a, c, a, none, c],
  [b, b, b, c, c, none]]
private def node29 : NetworkRefutation.Certificate 3 0 :=
  .node 3 5 a a [
    ]
private theorem checked29 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix29) node29 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix29) ⟨3, by decide⟩ ⟨5, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix30 : List (List (Atom 3 0)) := [
  [none, a, b, c, a],
  [a, none, c, c, a],
  [b, c, none, a, c],
  [c, c, a, none, a],
  [a, a, c, a, none]]
private def node30 : NetworkRefutation.Certificate 3 0 :=
  .node 3 4 c c [
    .cache matrix15 node15,
    .cache matrix28 node28,
    .cache matrix29 node29]
private theorem checked30 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 5) matrix30) node30 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 5) matrix30) ⟨3, by decide⟩ ⟨4, by decide⟩ c c = [
        ![da, da, db, dc, dc],
        ![db, db, da, dc, dc],
        ![db, db, db, dc, dc]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked15, checked28, checked29]
  decide +kernel
private def matrix31 : List (List (Atom 3 0)) := [
  [none, a, b, c],
  [a, none, c, c],
  [b, c, none, a],
  [c, c, a, none]]
private def node31 : NetworkRefutation.Certificate 3 0 :=
  .node 0 3 a a [
    .cache matrix30 node30]
private theorem checked31 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 4) matrix31) node31 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨3, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 4) matrix31) ⟨0, by decide⟩ ⟨3, by decide⟩ a a = [
        ![da, da, dc, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked30]
  decide +kernel
private def matrix51 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c],
  [a, none, c, c, c, a],
  [b, c, none, b, b, a],
  [c, c, b, none, a, b],
  [a, c, b, a, none, c],
  [c, a, a, b, c, none]]
private def node51 : NetworkRefutation.Certificate 3 0 :=
  .subnetwork [5, 1, 3, 4] matrix31 node31
private theorem checked51 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix51)
      node51 = true := by
  exact NetworkRefutation.check_subnetwork_of table _ _ _ _
    (by decide +kernel) (by decide +kernel) checked31
private def matrix52 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c],
  [a, none, c, c, c, a],
  [b, c, none, b, b, b],
  [c, c, b, none, a, a],
  [a, c, b, a, none, c],
  [c, a, b, a, c, none]]
private def node52 : NetworkRefutation.Certificate 3 0 :=
  .node 0 3 a b [
    ]
private theorem checked52 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix52) node52 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨3, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix52) ⟨0, by decide⟩ ⟨3, by decide⟩ a b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix53 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c],
  [a, none, c, c, c, a],
  [b, c, none, b, b, b],
  [c, c, b, none, a, b],
  [a, c, b, a, none, c],
  [c, a, b, b, c, none]]
private def node53 : NetworkRefutation.Certificate 3 0 :=
  .subnetwork [5, 1, 3, 4] matrix31 node31
private theorem checked53 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix53)
      node53 = true := by
  exact NetworkRefutation.check_subnetwork_of table _ _ _ _
    (by decide +kernel) (by decide +kernel) checked31
private def matrix54 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c],
  [a, none, c, c, c, a],
  [b, c, none, b, b, c],
  [c, c, b, none, a, a],
  [a, c, b, a, none, c],
  [c, a, c, a, c, none]]
private def node54 : NetworkRefutation.Certificate 3 0 :=
  .node 0 3 a b [
    ]
private theorem checked54 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix54) node54 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨3, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix54) ⟨0, by decide⟩ ⟨3, by decide⟩ a b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix88 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c],
  [a, none, c, c, c, a],
  [b, c, none, b, b, c],
  [c, c, b, none, a, b],
  [a, c, b, a, none, c],
  [c, a, c, b, c, none]]
private def node88 : NetworkRefutation.Certificate 3 0 :=
  .subnetwork [5, 1, 3, 4] matrix31 node31
private theorem checked88 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix88)
      node88 = true := by
  exact NetworkRefutation.check_subnetwork_of table _ _ _ _
    (by decide +kernel) (by decide +kernel) checked31
private def matrix89 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c],
  [a, none, c, c, c, b],
  [b, c, none, b, b, a],
  [c, c, b, none, a, b],
  [a, c, b, a, none, c],
  [c, b, a, b, c, none]]
private def node89 : NetworkRefutation.Certificate 3 0 :=
  .node 0 5 a a [
    ]
private theorem checked89 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix89) node89 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix89) ⟨0, by decide⟩ ⟨5, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix127 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c],
  [a, none, c, c, c, b],
  [b, c, none, b, b, b],
  [c, c, b, none, a, a],
  [a, c, b, a, none, c],
  [c, b, b, a, c, none]]
private def node127 : NetworkRefutation.Certificate 3 0 :=
  .subnetwork [1, 0, 5, 3] matrix31 node31
private theorem checked127 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix127)
      node127 = true := by
  exact NetworkRefutation.check_subnetwork_of table _ _ _ _
    (by decide +kernel) (by decide +kernel) checked31
private def matrix128 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c],
  [a, none, c, c, c, b],
  [b, c, none, b, b, b],
  [c, c, b, none, a, b],
  [a, c, b, a, none, c],
  [c, b, b, b, c, none]]
private def node128 : NetworkRefutation.Certificate 3 0 :=
  .node 0 5 a a [
    ]
private theorem checked128 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix128)
      node128 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix128) ⟨0, by decide⟩ ⟨5, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix162 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c],
  [a, none, c, c, c, b],
  [b, c, none, b, b, c],
  [c, c, b, none, a, a],
  [a, c, b, a, none, c],
  [c, b, c, a, c, none]]
private def node162 : NetworkRefutation.Certificate 3 0 :=
  .subnetwork [1, 0, 5, 3] matrix31 node31
private theorem checked162 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix162)
      node162 = true := by
  exact NetworkRefutation.check_subnetwork_of table _ _ _ _
    (by decide +kernel) (by decide +kernel) checked31
private def matrix163 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c],
  [a, none, c, c, c, b],
  [b, c, none, b, b, c],
  [c, c, b, none, a, b],
  [a, c, b, a, none, c],
  [c, b, c, b, c, none]]
private def node163 : NetworkRefutation.Certificate 3 0 :=
  .node 0 5 a a [
    ]
private theorem checked163 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix163)
      node163 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix163) ⟨0, by decide⟩ ⟨5, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix164 : List (List (Atom 3 0)) := [
  [none, a, b, c, a],
  [a, none, c, c, c],
  [b, c, none, b, b],
  [c, c, b, none, a],
  [a, c, b, a, none]]
private def node164 : NetworkRefutation.Certificate 3 0 :=
  .node 0 4 c c [
    .cache matrix51 node51,
    .cache matrix52 node52,
    .cache matrix53 node53,
    .cache matrix54 node54,
    .cache matrix88 node88,
    .cache matrix89 node89,
    .cache matrix127 node127,
    .cache matrix128 node128,
    .cache matrix162 node162,
    .cache matrix163 node163]
private theorem checked164 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 5) matrix164)
      node164 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 5) matrix164) ⟨0, by decide⟩ ⟨4, by decide⟩ c c = [
        ![dc, da, da, db, dc],
        ![dc, da, db, da, dc],
        ![dc, da, db, db, dc],
        ![dc, da, dc, da, dc],
        ![dc, da, dc, db, dc],
        ![dc, db, da, db, dc],
        ![dc, db, db, da, dc],
        ![dc, db, db, db, dc],
        ![dc, db, dc, da, dc],
        ![dc, db, dc, db, dc]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked51, checked52, checked53, checked54, checked88, checked89, checked127, checked128,
    checked162, checked163]
  decide +kernel
private def matrix165 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, b, a, a],
  [c, c, b, none, b, a, c, b],
  [a, c, b, b, none, c, b, b],
  [a, a, b, a, c, none, b, b],
  [b, b, a, c, b, b, none, a],
  [c, b, a, b, b, b, a, none]]
private def node165 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked165 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix165)
      node165 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix165) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix166 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, b, a, a],
  [c, c, b, none, b, a, c, b],
  [a, c, b, b, none, c, b, b],
  [a, a, b, a, c, none, b, c],
  [b, b, a, c, b, b, none, a],
  [c, b, a, b, b, c, a, none]]
private def node166 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked166 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix166)
      node166 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix166) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix167 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, b, a, a],
  [c, c, b, none, b, a, c, b],
  [a, c, b, b, none, c, b, c],
  [a, a, b, a, c, none, b, b],
  [b, b, a, c, b, b, none, a],
  [c, b, a, b, c, b, a, none]]
private def node167 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked167 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix167)
      node167 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix167) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix168 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, b, a, c],
  [c, c, b, none, b, a, c, a],
  [a, c, b, b, none, c, b, b],
  [a, a, b, a, c, none, b, c],
  [b, b, a, c, b, b, none, a],
  [c, b, c, a, b, c, a, none]]
private def node168 : NetworkRefutation.Certificate 3 0 :=
  .subnetwork [1, 0, 7, 3, 5] matrix30 node30
private theorem checked168 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix168)
      node168 = true := by
  exact NetworkRefutation.check_subnetwork_of table _ _ _ _
    (by decide +kernel) (by decide +kernel) checked30
private def matrix169 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, b, a, c],
  [c, c, b, none, b, a, c, b],
  [a, c, b, b, none, c, b, b],
  [a, a, b, a, c, none, b, b],
  [b, b, a, c, b, b, none, a],
  [c, b, c, b, b, b, a, none]]
private def node169 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked169 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix169)
      node169 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix169) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix170 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, b, a, c],
  [c, c, b, none, b, a, c, b],
  [a, c, b, b, none, c, b, b],
  [a, a, b, a, c, none, b, c],
  [b, b, a, c, b, b, none, a],
  [c, b, c, b, b, c, a, none]]
private def node170 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked170 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix170)
      node170 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix170) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix171 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, b, a, c],
  [c, c, b, none, b, a, c, b],
  [a, c, b, b, none, c, b, c],
  [a, a, b, a, c, none, b, b],
  [b, b, a, c, b, b, none, a],
  [c, b, c, b, c, b, a, none]]
private def node171 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked171 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix171)
      node171 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix171) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix172 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, c],
  [a, none, c, c, c, a, b, c],
  [b, c, none, b, b, b, a, a],
  [c, c, b, none, b, a, c, b],
  [a, c, b, b, none, c, b, b],
  [a, a, b, a, c, none, b, b],
  [b, b, a, c, b, b, none, a],
  [c, c, a, b, b, b, a, none]]
private def node172 : NetworkRefutation.Certificate 3 0 :=
  .subnetwork [0, 1, 2, 7] matrix31 node31
private theorem checked172 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix172)
      node172 = true := by
  exact NetworkRefutation.check_subnetwork_of table _ _ _ _
    (by decide +kernel) (by decide +kernel) checked31
private def matrix173 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, c],
  [a, none, c, c, c, a, b, c],
  [b, c, none, b, b, b, a, a],
  [c, c, b, none, b, a, c, b],
  [a, c, b, b, none, c, b, b],
  [a, a, b, a, c, none, b, c],
  [b, b, a, c, b, b, none, a],
  [c, c, a, b, b, c, a, none]]
private def node173 : NetworkRefutation.Certificate 3 0 :=
  .subnetwork [0, 1, 2, 7] matrix31 node31
private theorem checked173 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix173)
      node173 = true := by
  exact NetworkRefutation.check_subnetwork_of table _ _ _ _
    (by decide +kernel) (by decide +kernel) checked31
private def matrix174 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, b, a],
  [c, c, b, none, b, a, c],
  [a, c, b, b, none, c, b],
  [a, a, b, a, c, none, b],
  [b, b, a, c, b, b, none]]
private def node174 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 c a [
    .cache matrix165 node165,
    .cache matrix166 node166,
    .cache matrix167 node167,
    .cache matrix168 node168,
    .cache matrix169 node169,
    .cache matrix170 node170,
    .cache matrix171 node171,
    .cache matrix172 node172,
    .cache matrix173 node173]
private theorem checked174 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix174)
      node174 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix174) ⟨0, by decide⟩ ⟨6, by decide⟩ c a = [
        ![dc, db, da, db, db, db, da],
        ![dc, db, da, db, db, dc, da],
        ![dc, db, da, db, dc, db, da],
        ![dc, db, dc, da, db, dc, da],
        ![dc, db, dc, db, db, db, da],
        ![dc, db, dc, db, db, dc, da],
        ![dc, db, dc, db, dc, db, da],
        ![dc, dc, da, db, db, db, da],
        ![dc, dc, da, db, db, dc, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked165, checked166, checked167, checked168, checked169, checked170, checked171,
    checked172, checked173]
  decide +kernel
private def matrix175 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, b, a],
  [c, c, b, none, b, a, c],
  [a, c, b, b, none, c, b],
  [a, a, b, a, c, none, c],
  [b, b, a, c, b, c, none]]
private def node175 : NetworkRefutation.Certificate 3 0 :=
  .node 1 2 a a [
    ]
private theorem checked175 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix175)
      node175 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix175) ⟨1, by decide⟩ ⟨2, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix176 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, b],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, b, a, c],
  [c, c, b, none, b, a, c, a],
  [a, c, b, b, none, c, c, b],
  [a, a, b, a, c, none, b, c],
  [b, b, a, c, c, b, none, a],
  [b, b, c, a, b, c, a, none]]
private def node176 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked176 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix176)
      node176 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix176) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix177 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, b, a, c],
  [c, c, b, none, b, a, c, a],
  [a, c, b, b, none, c, c, b],
  [a, a, b, a, c, none, b, c],
  [b, b, a, c, c, b, none, a],
  [c, b, c, a, b, c, a, none]]
private def node177 : NetworkRefutation.Certificate 3 0 :=
  .subnetwork [1, 0, 7, 3, 5] matrix30 node30
private theorem checked177 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix177)
      node177 = true := by
  exact NetworkRefutation.check_subnetwork_of table _ _ _ _
    (by decide +kernel) (by decide +kernel) checked30
private def matrix178 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a, b],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, b, a],
  [c, c, b, none, b, a, c],
  [a, c, b, b, none, c, c],
  [a, a, b, a, c, none, b],
  [b, b, a, c, c, b, none]]
private def node178 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    .cache matrix176 node176,
    .cache matrix177 node177]
private theorem checked178 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix178)
      node178 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix178) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [
        ![db, db, dc, da, db, dc, da],
        ![dc, db, dc, da, db, dc, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked176, checked177]
  decide +kernel
private def matrix179 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a],
  [a, none, c, c, c, a],
  [b, c, none, b, b, b],
  [c, c, b, none, b, a],
  [a, c, b, b, none, c],
  [a, a, b, a, c, none]]
private def node179 : NetworkRefutation.Certificate 3 0 :=
  .node 2 3 a c [
    .cache matrix174 node174,
    .cache matrix175 node175,
    .cache matrix178 node178]
private theorem checked179 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix179)
      node179 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨3, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix179) ⟨2, by decide⟩ ⟨3, by decide⟩ a c = [
        ![db, db, da, dc, db, db],
        ![db, db, da, dc, db, dc],
        ![db, db, da, dc, dc, db]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked174, checked175, checked178]
  decide +kernel
private def matrix180 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, a],
  [a, none, c, c, c, a],
  [b, c, none, b, b, c],
  [c, c, b, none, b, a],
  [a, c, b, b, none, c],
  [a, a, c, a, c, none]]
private def node180 : NetworkRefutation.Certificate 3 0 :=
  .node 2 5 a a [
    ]
private theorem checked180 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix180)
      node180 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix180) ⟨2, by decide⟩ ⟨5, by decide⟩ a a = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix181 : List (List (Atom 3 0)) := [
  [none, a, b, c, a],
  [a, none, c, c, c],
  [b, c, none, b, b],
  [c, c, b, none, b],
  [a, c, b, b, none]]
private def node181 : NetworkRefutation.Certificate 3 0 :=
  .node 0 3 a a [
    .cache matrix179 node179,
    .cache matrix180 node180]
private theorem checked181 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 5) matrix181)
      node181 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨3, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 5) matrix181) ⟨0, by decide⟩ ⟨3, by decide⟩ a a = [
        ![da, da, db, da, dc],
        ![da, da, dc, da, dc]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked179, checked180]
  decide +kernel
private def matrix182 : List (List (Atom 3 0)) := [
  [none, a, b, c],
  [a, none, c, c],
  [b, c, none, b],
  [c, c, b, none]]
private def node182 : NetworkRefutation.Certificate 3 0 :=
  .node 0 1 a c [
    .cache matrix164 node164,
    .cache matrix181 node181]
private theorem checked182 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 4) matrix182)
      node182 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨1, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 4) matrix182) ⟨0, by decide⟩ ⟨1, by decide⟩ a c = [
        ![da, dc, db, da],
        ![da, dc, db, db]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked164, checked181]
  decide +kernel
private def matrix183 : List (List (Atom 3 0)) := [
  [none, a, b],
  [a, none, c],
  [b, c, none]]
private def node183 : NetworkRefutation.Certificate 3 0 :=
  .node 0 1 c c [
    .cache matrix31 node31,
    .cache matrix182 node182]
private theorem checked183 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 3) matrix183)
      node183 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨1, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 3) matrix183) ⟨0, by decide⟩ ⟨1, by decide⟩ c c = [
        ![dc, dc, da],
        ![dc, dc, db]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked31, checked182]
  decide +kernel
private def matrix184 : List (List (Atom 3 0)) := [
  [none, a],
  [a, none]]
private def node184 : NetworkRefutation.Certificate 3 0 :=
  .node 0 1 b c [
    .cache matrix183 node183]
private theorem checked184 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 2) matrix184)
      node184 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨1, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 2) matrix184) ⟨0, by decide⟩ ⟨1, by decide⟩ b c = [
        ![db, dc]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked183]
  decide +kernel
/-- A finite tree of impossible composition-witness extensions. -/
private def obstruction : NetworkRefutation.Certificate 3 0 := by exact node184
/-- This catalogue algebra has no representation by binary relations. -/
theorem not_representable : ¬ Representable Algebra := by
  apply NetworkRefutation.not_representable table (some (.inl 0)) obstruction
  have hi : NetworkRefutation.initial (some (.inl 0)) =
      NetworkRefutation.ofMatrix (n := 2) matrix184 := by decide +kernel
  rw [hi]
  exact checked184
end Cslib.RelationAlgebra.Catalogue.I1S3N0.Ra53
