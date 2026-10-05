/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/
module
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
/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 3 0 where
  cycles := cycles
  associative := by decide +kernel
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
        ![dc, dc, db, db, dc, db, da]] := by decide +kernel
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
        ![dc, dc, db, db, dc, db]] := by decide +kernel
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
        ![db, db, dc, dc, db, db, da]] := by decide +kernel
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
        ![dc, da, db, db, dc, db, da]] := by decide +kernel
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
        ![db, dc, db, db, dc, db]] := by decide +kernel
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
        ![db, db, db, dc, dc]] := by decide +kernel
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
        ![da, da, dc, da]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked30]
  decide +kernel
private def matrix32 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, a, b, b],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, b],
  [c, a, a, b, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, b, b, b, b, b, a, none]]
private def node32 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked32 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix32) node32 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix32) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix33 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, a, b, b],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, c],
  [c, a, a, b, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, b, b, b, c, b, a, none]]
private def node33 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked33 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix33) node33 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix33) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix34 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, a, b, c],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, b],
  [c, a, a, b, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, b, c, b, b, b, a, none]]
private def node34 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked34 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix34) node34 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix34) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix35 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, a, b, c],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, c],
  [c, a, a, b, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, b, c, b, c, b, a, none]]
private def node35 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked35 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix35) node35 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix35) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix36 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, c],
  [b, c, none, b, b, a, b, b],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, b],
  [c, a, a, b, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, c, b, b, b, b, a, none]]
private def node36 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked36 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix36) node36 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix36) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix37 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, a, b],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, a, b, c, none, b],
  [b, b, b, b, b, b, none]]
private def node37 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 c a [
    .cache matrix32 node32,
    .cache matrix33 node33,
    .cache matrix34 node34,
    .cache matrix35 node35,
    .cache matrix36 node36]
private theorem checked37 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix37) node37 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix37) ⟨0, by decide⟩ ⟨6, by decide⟩ c a = [
        ![dc, db, db, db, db, db, da],
        ![dc, db, db, db, dc, db, da],
        ![dc, db, dc, db, db, db, da],
        ![dc, db, dc, db, dc, db, da],
        ![dc, dc, db, db, db, db, da]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked32, checked33, checked34, checked35, checked36]
  decide +kernel
private def matrix38 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, a, b],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, c],
  [c, a, a, b, c, none, b],
  [b, b, b, b, c, b, none]]
private def node38 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked38 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix38) node38 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix38) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix39 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, a, b, a],
  [b, c, none, b, b, a, c, b],
  [c, c, b, none, a, b, b, a],
  [a, c, b, a, none, c, b, a],
  [c, a, a, b, c, none, b, c],
  [b, b, c, b, b, b, none, c],
  [a, a, b, a, a, c, c, none]]
private def node39 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked39 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix39) node39 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix39) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix40 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, a, b, a],
  [b, c, none, b, b, a, c, b],
  [c, c, b, none, a, b, b, c],
  [a, c, b, a, none, c, b, a],
  [c, a, a, b, c, none, b, c],
  [b, b, c, b, b, b, none, c],
  [a, a, b, c, a, c, c, none]]
private def node40 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked40 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix40) node40 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix40) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix41 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, a, b, c],
  [b, c, none, b, b, a, c, b],
  [c, c, b, none, a, b, b, a],
  [a, c, b, a, none, c, b, a],
  [c, a, a, b, c, none, b, b],
  [b, b, c, b, b, b, none, c],
  [a, c, b, a, a, b, c, none]]
private def node41 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked41 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix41) node41 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix41) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix42 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, a, b, c],
  [b, c, none, b, b, a, c, b],
  [c, c, b, none, a, b, b, a],
  [a, c, b, a, none, c, b, a],
  [c, a, a, b, c, none, b, c],
  [b, b, c, b, b, b, none, c],
  [a, c, b, a, a, c, c, none]]
private def node42 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked42 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix42) node42 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix42) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix43 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, a, c],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, a, b, c, none, b],
  [b, b, c, b, b, b, none]]
private def node43 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a c [
    .cache matrix39 node39,
    .cache matrix40 node40,
    .cache matrix41 node41,
    .cache matrix42 node42]
private theorem checked43 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix43) node43 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix43) ⟨0, by decide⟩ ⟨6, by decide⟩ a c = [
        ![da, da, db, da, da, dc, dc],
        ![da, da, db, dc, da, dc, dc],
        ![da, dc, db, da, da, db, dc],
        ![da, dc, db, da, da, dc, dc]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked39, checked40, checked41, checked42]
  decide +kernel
private def matrix44 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, a, c],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, c],
  [c, a, a, b, c, none, b],
  [b, b, c, b, c, b, none]]
private def node44 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked44 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix44) node44 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix44) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix45 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, a, c],
  [b, c, none, b, b, a, b],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, a, b, c, none, b],
  [b, c, b, b, b, b, none]]
private def node45 : NetworkRefutation.Certificate 3 0 :=
  .node 1 6 a a [
    ]
private theorem checked45 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix45) node45 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix45) ⟨1, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix46 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, a, b],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, a, b, c, none, b],
  [c, b, b, b, b, b, none]]
private def node46 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked46 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix46) node46 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix46) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix47 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, a, b],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, c],
  [c, a, a, b, c, none, b],
  [c, b, b, b, c, b, none]]
private def node47 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked47 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix47) node47 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix47) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix48 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, a, c],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, a, b, c, none, b],
  [c, b, c, b, b, b, none]]
private def node48 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked48 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix48) node48 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix48) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix49 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, a, c],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, c],
  [c, a, a, b, c, none, b],
  [c, b, c, b, c, b, none]]
private def node49 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked49 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix49) node49 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix49) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix50 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, a, c],
  [b, c, none, b, b, a, b],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, a, b, c, none, b],
  [c, c, b, b, b, b, none]]
private def node50 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked50 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix50) node50 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix50) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix51 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c],
  [a, none, c, c, c, a],
  [b, c, none, b, b, a],
  [c, c, b, none, a, b],
  [a, c, b, a, none, c],
  [c, a, a, b, c, none]]
private def node51 : NetworkRefutation.Certificate 3 0 :=
  .node 3 5 b b [
    .cache matrix37 node37,
    .cache matrix38 node38,
    .cache matrix43 node43,
    .cache matrix44 node44,
    .cache matrix45 node45,
    .cache matrix46 node46,
    .cache matrix47 node47,
    .cache matrix48 node48,
    .cache matrix49 node49,
    .cache matrix50 node50]
private theorem checked51 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix51) node51 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix51) ⟨3, by decide⟩ ⟨5, by decide⟩ b b = [
        ![db, db, db, db, db, db],
        ![db, db, db, db, dc, db],
        ![db, db, dc, db, db, db],
        ![db, db, dc, db, dc, db],
        ![db, dc, db, db, db, db],
        ![dc, db, db, db, db, db],
        ![dc, db, db, db, dc, db],
        ![dc, db, dc, db, db, db],
        ![dc, db, dc, db, dc, db],
        ![dc, dc, db, db, db, db]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked37, checked38, checked43, checked44, checked45, checked46, checked47, checked48,
    checked49, checked50]
  decide +kernel
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
  .node 1 2 a a [
    ]
private theorem checked53 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix53) node53 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix53) ⟨1, by decide⟩ ⟨2, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
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
    decide +kernel
  rw [hrows]
  rfl
private def matrix55 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, c, a, a],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, b],
  [c, a, c, b, c, none, b, b],
  [b, b, a, b, b, b, none, a],
  [c, b, a, b, b, b, a, none]]
private def node55 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked55 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix55) node55 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix55) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix56 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, c, a, a],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, c],
  [c, a, c, b, c, none, b, b],
  [b, b, a, b, b, b, none, a],
  [c, b, a, b, c, b, a, none]]
private def node56 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked56 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix56) node56 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix56) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix57 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, c, a, c],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, b],
  [c, a, c, b, c, none, b, b],
  [b, b, a, b, b, b, none, a],
  [c, b, c, b, b, b, a, none]]
private def node57 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked57 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix57) node57 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix57) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix58 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, c, a, c],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, c],
  [c, a, c, b, c, none, b, b],
  [b, b, a, b, b, b, none, a],
  [c, b, c, b, c, b, a, none]]
private def node58 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked58 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix58) node58 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix58) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix59 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, c],
  [b, c, none, b, b, c, a, a],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, b],
  [c, a, c, b, c, none, b, b],
  [b, b, a, b, b, b, none, a],
  [c, c, a, b, b, b, a, none]]
private def node59 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked59 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix59) node59 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix59) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix60 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, c, a],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, c, b, c, none, b],
  [b, b, a, b, b, b, none]]
private def node60 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 c a [
    .cache matrix55 node55,
    .cache matrix56 node56,
    .cache matrix57 node57,
    .cache matrix58 node58,
    .cache matrix59 node59]
private theorem checked60 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix60) node60 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix60) ⟨0, by decide⟩ ⟨6, by decide⟩ c a = [
        ![dc, db, da, db, db, db, da],
        ![dc, db, da, db, dc, db, da],
        ![dc, db, dc, db, db, db, da],
        ![dc, db, dc, db, dc, db, da],
        ![dc, dc, da, db, db, db, da]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked55, checked56, checked57, checked58, checked59]
  decide +kernel
private def matrix61 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, c, a],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, c],
  [c, a, c, b, c, none, b],
  [b, b, a, b, c, b, none]]
private def node61 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked61 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix61) node61 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix61) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix62 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, c, b, b],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, b],
  [c, a, c, b, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, b, b, b, b, b, a, none]]
private def node62 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked62 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix62) node62 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix62) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix63 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, c, b, b],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, c],
  [c, a, c, b, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, b, b, b, c, b, a, none]]
private def node63 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked63 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix63) node63 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix63) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix64 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, c, b, c],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, b],
  [c, a, c, b, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, b, c, b, b, b, a, none]]
private def node64 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked64 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix64) node64 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix64) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix65 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, b],
  [b, c, none, b, b, c, b, c],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, c],
  [c, a, c, b, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, b, c, b, c, b, a, none]]
private def node65 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked65 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix65) node65 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix65) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix66 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, a, b, c],
  [b, c, none, b, b, c, b, b],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, b],
  [c, a, c, b, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, c, b, b, b, b, a, none]]
private def node66 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked66 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix66) node66 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix66) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix67 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, c, b],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, c, b, c, none, b],
  [b, b, b, b, b, b, none]]
private def node67 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 c a [
    .cache matrix62 node62,
    .cache matrix63 node63,
    .cache matrix64 node64,
    .cache matrix65 node65,
    .cache matrix66 node66]
private theorem checked67 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix67) node67 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix67) ⟨0, by decide⟩ ⟨6, by decide⟩ c a = [
        ![dc, db, db, db, db, db, da],
        ![dc, db, db, db, dc, db, da],
        ![dc, db, dc, db, db, db, da],
        ![dc, db, dc, db, dc, db, da],
        ![dc, dc, db, db, db, db, da]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked62, checked63, checked64, checked65, checked66]
  decide +kernel
private def matrix68 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, c, b],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, c],
  [c, a, c, b, c, none, b],
  [b, b, b, b, c, b, none]]
private def node68 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked68 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix68) node68 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix68) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix69 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, a, b, a],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, b, b, a],
  [a, c, b, a, none, c, b, a],
  [c, a, c, b, c, none, b, c],
  [b, b, c, b, b, b, none, c],
  [a, a, b, a, a, c, c, none]]
private def node69 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked69 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix69) node69 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix69) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix70 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, a, b, a],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, b, b, b],
  [a, c, b, a, none, c, b, c],
  [c, a, c, b, c, none, b, a],
  [b, b, c, b, b, b, none, c],
  [a, a, b, b, c, a, c, none]]
private def node70 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked70 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix70) node70 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix70) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix71 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, a, b, a],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, b, b, c],
  [a, c, b, a, none, c, b, a],
  [c, a, c, b, c, none, b, a],
  [b, b, c, b, b, b, none, c],
  [a, a, b, c, a, a, c, none]]
private def node71 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked71 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix71) node71 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix71) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix72 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, a, b, a],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, b, b, c],
  [a, c, b, a, none, c, b, a],
  [c, a, c, b, c, none, b, c],
  [b, b, c, b, b, b, none, c],
  [a, a, b, c, a, c, c, none]]
private def node72 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked72 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix72) node72 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix72) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix73 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, a, b, a],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, b, b, c],
  [a, c, b, a, none, c, b, c],
  [c, a, c, b, c, none, b, a],
  [b, b, c, b, b, b, none, c],
  [a, a, b, c, c, a, c, none]]
private def node73 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked73 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix73) node73 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix73) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix74 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, a, b, c],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, b, b, a],
  [a, c, b, a, none, c, b, a],
  [c, a, c, b, c, none, b, b],
  [b, b, c, b, b, b, none, c],
  [a, c, b, a, a, b, c, none]]
private def node74 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked74 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix74) node74 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix74) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix75 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, a, b, c],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, b, b, a],
  [a, c, b, a, none, c, b, a],
  [c, a, c, b, c, none, b, c],
  [b, b, c, b, b, b, none, c],
  [a, c, b, a, a, c, c, none]]
private def node75 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked75 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix75) node75 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix75) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix76 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, c, c],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, c, b, c, none, b],
  [b, b, c, b, b, b, none]]
private def node76 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a c [
    .cache matrix69 node69,
    .cache matrix70 node70,
    .cache matrix71 node71,
    .cache matrix72 node72,
    .cache matrix73 node73,
    .cache matrix74 node74,
    .cache matrix75 node75]
private theorem checked76 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix76) node76 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix76) ⟨0, by decide⟩ ⟨6, by decide⟩ a c = [
        ![da, da, db, da, da, dc, dc],
        ![da, da, db, db, dc, da, dc],
        ![da, da, db, dc, da, da, dc],
        ![da, da, db, dc, da, dc, dc],
        ![da, da, db, dc, dc, da, dc],
        ![da, dc, db, da, da, db, dc],
        ![da, dc, db, da, da, dc, dc]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked69, checked70, checked71, checked72, checked73, checked74, checked75]
  decide +kernel
private def matrix77 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, c, c],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, c],
  [c, a, c, b, c, none, b],
  [b, b, c, b, c, b, none]]
private def node77 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked77 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix77) node77 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix77) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix78 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, a, c],
  [b, c, none, b, b, c, a],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, c, b, c, none, b],
  [b, c, a, b, b, b, none]]
private def node78 : NetworkRefutation.Certificate 3 0 :=
  .node 1 6 a a [
    ]
private theorem checked78 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix78) node78 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix78) ⟨1, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix79 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, a, c],
  [b, c, none, b, b, c, b],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, c, b, c, none, b],
  [b, c, b, b, b, b, none]]
private def node79 : NetworkRefutation.Certificate 3 0 :=
  .node 1 6 a a [
    ]
private theorem checked79 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix79) node79 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix79) ⟨1, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix80 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, c, a],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, c, b, c, none, b],
  [c, b, a, b, b, b, none]]
private def node80 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked80 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix80) node80 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix80) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix81 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, c, a],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, c],
  [c, a, c, b, c, none, b],
  [c, b, a, b, c, b, none]]
private def node81 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked81 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix81) node81 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix81) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix82 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, c, b],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, c, b, c, none, b],
  [c, b, b, b, b, b, none]]
private def node82 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked82 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix82) node82 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix82) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix83 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, c, b],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, c],
  [c, a, c, b, c, none, b],
  [c, b, b, b, c, b, none]]
private def node83 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked83 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix83) node83 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix83) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix84 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, c, c],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, c, b, c, none, b],
  [c, b, c, b, b, b, none]]
private def node84 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked84 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix84) node84 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix84) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix85 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, a, b],
  [b, c, none, b, b, c, c],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, c],
  [c, a, c, b, c, none, b],
  [c, b, c, b, c, b, none]]
private def node85 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked85 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix85) node85 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix85) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix86 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, a, c],
  [b, c, none, b, b, c, a],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, c, b, c, none, b],
  [c, c, a, b, b, b, none]]
private def node86 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked86 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix86) node86 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix86) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix87 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, a, c],
  [b, c, none, b, b, c, b],
  [c, c, b, none, a, b, b],
  [a, c, b, a, none, c, b],
  [c, a, c, b, c, none, b],
  [c, c, b, b, b, b, none]]
private def node87 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked87 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix87) node87 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix87) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
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
  .node 3 5 b b [
    .cache matrix60 node60,
    .cache matrix61 node61,
    .cache matrix67 node67,
    .cache matrix68 node68,
    .cache matrix76 node76,
    .cache matrix77 node77,
    .cache matrix78 node78,
    .cache matrix79 node79,
    .cache matrix80 node80,
    .cache matrix81 node81,
    .cache matrix82 node82,
    .cache matrix83 node83,
    .cache matrix84 node84,
    .cache matrix85 node85,
    .cache matrix86 node86,
    .cache matrix87 node87]
private theorem checked88 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix88) node88 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix88) ⟨3, by decide⟩ ⟨5, by decide⟩ b b = [
        ![db, db, da, db, db, db],
        ![db, db, da, db, dc, db],
        ![db, db, db, db, db, db],
        ![db, db, db, db, dc, db],
        ![db, db, dc, db, db, db],
        ![db, db, dc, db, dc, db],
        ![db, dc, da, db, db, db],
        ![db, dc, db, db, db, db],
        ![dc, db, da, db, db, db],
        ![dc, db, da, db, dc, db],
        ![dc, db, db, db, db, db],
        ![dc, db, db, db, dc, db],
        ![dc, db, dc, db, db, db],
        ![dc, db, dc, db, dc, db],
        ![dc, dc, da, db, db, db],
        ![dc, dc, db, db, db, db]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked60, checked61, checked67, checked68, checked76, checked77, checked78, checked79,
    checked80, checked81, checked82, checked83, checked84, checked85, checked86, checked87]
  decide +kernel
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
    decide +kernel
  rw [hrows]
  rfl
private def matrix90 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, b],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, b, a, a],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, c],
  [c, b, b, a, c, none, b, b],
  [b, b, a, b, b, b, none, a],
  [b, b, a, b, c, b, a, none]]
private def node90 : NetworkRefutation.Certificate 3 0 :=
  .node 4 7 a a [
    ]
private theorem checked90 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix90) node90 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix90) ⟨4, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix91 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, b],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, b, a, a],
  [c, c, b, none, a, a, b, c],
  [a, c, b, a, none, c, b, c],
  [c, b, b, a, c, none, b, b],
  [b, b, a, b, b, b, none, a],
  [b, b, a, c, c, b, a, none]]
private def node91 : NetworkRefutation.Certificate 3 0 :=
  .node 3 7 a a [
    ]
private theorem checked91 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix91) node91 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix91) ⟨3, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix92 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, b],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, b, a, c],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, c],
  [c, b, b, a, c, none, b, b],
  [b, b, a, b, b, b, none, a],
  [b, b, c, b, c, b, a, none]]
private def node92 : NetworkRefutation.Certificate 3 0 :=
  .node 4 7 a a [
    ]
private theorem checked92 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix92) node92 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix92) ⟨4, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix93 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, b],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, b, a, c],
  [c, c, b, none, a, a, b, c],
  [a, c, b, a, none, c, b, c],
  [c, b, b, a, c, none, b, b],
  [b, b, a, b, b, b, none, a],
  [b, b, c, c, c, b, a, none]]
private def node93 : NetworkRefutation.Certificate 3 0 :=
  .node 3 7 a a [
    ]
private theorem checked93 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix93) node93 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix93) ⟨3, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix94 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, b, a, a],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, c],
  [c, b, b, a, c, none, b, b],
  [b, b, a, b, b, b, none, a],
  [c, b, a, b, c, b, a, none]]
private def node94 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked94 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix94) node94 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix94) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix95 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, b, a, c],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, c],
  [c, b, b, a, c, none, b, b],
  [b, b, a, b, b, b, none, a],
  [c, b, c, b, c, b, a, none]]
private def node95 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked95 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix95) node95 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix95) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix96 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, a],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, b],
  [c, b, b, a, c, none, b],
  [b, b, a, b, b, b, none]]
private def node96 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 c a [
    .cache matrix90 node90,
    .cache matrix91 node91,
    .cache matrix92 node92,
    .cache matrix93 node93,
    .cache matrix94 node94,
    .cache matrix95 node95]
private theorem checked96 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix96) node96 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix96) ⟨4, by decide⟩ ⟨6, by decide⟩ c a = [
        ![db, db, da, db, dc, db, da],
        ![db, db, da, dc, dc, db, da],
        ![db, db, dc, db, dc, db, da],
        ![db, db, dc, dc, dc, db, da],
        ![dc, db, da, db, dc, db, da],
        ![dc, db, dc, db, dc, db, da]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked90, checked91, checked92, checked93, checked94, checked95]
  decide +kernel
private def matrix97 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, a],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, c],
  [c, b, b, a, c, none, b],
  [b, b, a, b, c, b, none]]
private def node97 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked97 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix97) node97 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix97) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix98 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, a],
  [c, c, b, none, a, a, c],
  [a, c, b, a, none, c, b],
  [c, b, b, a, c, none, b],
  [b, b, a, c, b, b, none]]
private def node98 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked98 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix98) node98 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix98) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix99 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, a],
  [c, c, b, none, a, a, c],
  [a, c, b, a, none, c, c],
  [c, b, b, a, c, none, b],
  [b, b, a, c, c, b, none]]
private def node99 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked99 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix99) node99 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix99) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix100 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, b],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, b, b, b],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, c],
  [c, b, b, a, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, b, b, b, c, b, a, none]]
private def node100 : NetworkRefutation.Certificate 3 0 :=
  .node 4 7 a a [
    ]
private theorem checked100 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix100)
      node100 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix100) ⟨4, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix101 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, b],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, b, b, b],
  [c, c, b, none, a, a, b, c],
  [a, c, b, a, none, c, b, c],
  [c, b, b, a, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, b, b, c, c, b, a, none]]
private def node101 : NetworkRefutation.Certificate 3 0 :=
  .node 3 7 a a [
    ]
private theorem checked101 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix101)
      node101 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix101) ⟨3, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix102 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, b],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, b, b, c],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, c],
  [c, b, b, a, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, b, c, b, c, b, a, none]]
private def node102 : NetworkRefutation.Certificate 3 0 :=
  .node 4 7 a a [
    ]
private theorem checked102 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix102)
      node102 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix102) ⟨4, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix103 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, b],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, b, b, c],
  [c, c, b, none, a, a, b, c],
  [a, c, b, a, none, c, b, c],
  [c, b, b, a, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, b, c, c, c, b, a, none]]
private def node103 : NetworkRefutation.Certificate 3 0 :=
  .node 3 7 a a [
    ]
private theorem checked103 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix103)
      node103 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix103) ⟨3, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix104 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, b, b, b],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, c],
  [c, b, b, a, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, b, b, b, c, b, a, none]]
private def node104 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked104 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix104)
      node104 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix104) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix105 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, b, b, c],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, c],
  [c, b, b, a, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, b, c, b, c, b, a, none]]
private def node105 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked105 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix105)
      node105 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix105) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix106 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, b],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, b],
  [c, b, b, a, c, none, b],
  [b, b, b, b, b, b, none]]
private def node106 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 c a [
    .cache matrix100 node100,
    .cache matrix101 node101,
    .cache matrix102 node102,
    .cache matrix103 node103,
    .cache matrix104 node104,
    .cache matrix105 node105]
private theorem checked106 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix106)
      node106 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix106) ⟨4, by decide⟩ ⟨6, by decide⟩ c a = [
        ![db, db, db, db, dc, db, da],
        ![db, db, db, dc, dc, db, da],
        ![db, db, dc, db, dc, db, da],
        ![db, db, dc, dc, dc, db, da],
        ![dc, db, db, db, dc, db, da],
        ![dc, db, dc, db, dc, db, da]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked100, checked101, checked102, checked103, checked104, checked105]
  decide +kernel
private def matrix107 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, b],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, c],
  [c, b, b, a, c, none, b],
  [b, b, b, b, c, b, none]]
private def node107 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked107 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix107)
      node107 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix107) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix108 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, b],
  [c, c, b, none, a, a, c],
  [a, c, b, a, none, c, b],
  [c, b, b, a, c, none, b],
  [b, b, b, c, b, b, none]]
private def node108 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked108 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix108)
      node108 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix108) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix109 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, b],
  [c, c, b, none, a, a, c],
  [a, c, b, a, none, c, c],
  [c, b, b, a, c, none, b],
  [b, b, b, c, c, b, none]]
private def node109 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked109 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix109)
      node109 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix109) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix110 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, b, b, a],
  [b, c, none, b, b, b, c, b],
  [c, c, b, none, a, a, b, a],
  [a, c, b, a, none, c, b, a],
  [c, b, b, a, c, none, b, c],
  [b, b, c, b, b, b, none, c],
  [a, a, b, a, a, c, c, none]]
private def node110 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked110 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix110)
      node110 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix110) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix111 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, b, b, a],
  [b, c, none, b, b, b, c, b],
  [c, c, b, none, a, a, b, c],
  [a, c, b, a, none, c, b, a],
  [c, b, b, a, c, none, b, b],
  [b, b, c, b, b, b, none, c],
  [a, a, b, c, a, b, c, none]]
private def node111 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked111 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix111)
      node111 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix111) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix112 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, b, b, a],
  [b, c, none, b, b, b, c, b],
  [c, c, b, none, a, a, b, c],
  [a, c, b, a, none, c, b, a],
  [c, b, b, a, c, none, b, c],
  [b, b, c, b, b, b, none, c],
  [a, a, b, c, a, c, c, none]]
private def node112 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked112 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix112)
      node112 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix112) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix113 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, b, b, c],
  [b, c, none, b, b, b, c, b],
  [c, c, b, none, a, a, b, a],
  [a, c, b, a, none, c, b, a],
  [c, b, b, a, c, none, b, a],
  [b, b, c, b, b, b, none, c],
  [a, c, b, a, a, a, c, none]]
private def node113 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked113 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix113)
      node113 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix113) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix114 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, b, b, c],
  [b, c, none, b, b, b, c, b],
  [c, c, b, none, a, a, b, a],
  [a, c, b, a, none, c, b, a],
  [c, b, b, a, c, none, b, c],
  [b, b, c, b, b, b, none, c],
  [a, c, b, a, a, c, c, none]]
private def node114 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked114 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix114)
      node114 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix114) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix115 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, b, c, b],
  [c, c, b, none, a, a, b, a],
  [a, c, b, a, none, c, b, a],
  [c, b, b, a, c, none, b, a],
  [b, b, c, b, b, b, none, c],
  [c, b, b, a, a, a, c, none]]
private def node115 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked115 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix115)
      node115 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix115) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix116 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, b, b, c],
  [b, c, none, b, b, b, c, b],
  [c, c, b, none, a, a, b, a],
  [a, c, b, a, none, c, b, a],
  [c, b, b, a, c, none, b, a],
  [b, b, c, b, b, b, none, c],
  [c, c, b, a, a, a, c, none]]
private def node116 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked116 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix116)
      node116 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix116) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix117 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, c],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, b],
  [c, b, b, a, c, none, b],
  [b, b, c, b, b, b, none]]
private def node117 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a c [
    .cache matrix110 node110,
    .cache matrix111 node111,
    .cache matrix112 node112,
    .cache matrix113 node113,
    .cache matrix114 node114,
    .cache matrix115 node115,
    .cache matrix116 node116]
private theorem checked117 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix117)
      node117 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix117) ⟨4, by decide⟩ ⟨6, by decide⟩ a c = [
        ![da, da, db, da, da, dc, dc],
        ![da, da, db, dc, da, db, dc],
        ![da, da, db, dc, da, dc, dc],
        ![da, dc, db, da, da, da, dc],
        ![da, dc, db, da, da, dc, dc],
        ![dc, db, db, da, da, da, dc],
        ![dc, dc, db, da, da, da, dc]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked110, checked111, checked112, checked113, checked114, checked115, checked116]
  decide +kernel
private def matrix118 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, c],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, c],
  [c, b, b, a, c, none, b],
  [b, b, c, b, c, b, none]]
private def node118 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked118 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix118)
      node118 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix118) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix119 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, c],
  [c, c, b, none, a, a, c],
  [a, c, b, a, none, c, b],
  [c, b, b, a, c, none, b],
  [b, b, c, c, b, b, none]]
private def node119 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked119 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix119)
      node119 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix119) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix120 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, c],
  [c, c, b, none, a, a, c],
  [a, c, b, a, none, c, c],
  [c, b, b, a, c, none, b],
  [b, b, c, c, c, b, none]]
private def node120 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked120 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix120)
      node120 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix120) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix121 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, a],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, b],
  [c, b, b, a, c, none, b],
  [c, b, a, b, b, b, none]]
private def node121 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked121 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix121)
      node121 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix121) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix122 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, a],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, c],
  [c, b, b, a, c, none, b],
  [c, b, a, b, c, b, none]]
private def node122 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked122 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix122)
      node122 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix122) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix123 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, b],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, b],
  [c, b, b, a, c, none, b],
  [c, b, b, b, b, b, none]]
private def node123 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked123 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix123)
      node123 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix123) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix124 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, b],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, c],
  [c, b, b, a, c, none, b],
  [c, b, b, b, c, b, none]]
private def node124 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked124 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix124)
      node124 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix124) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix125 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, c],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, b],
  [c, b, b, a, c, none, b],
  [c, b, c, b, b, b, none]]
private def node125 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked125 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix125)
      node125 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix125) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix126 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, b, c],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, c],
  [c, b, b, a, c, none, b],
  [c, b, c, b, c, b, none]]
private def node126 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked126 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix126)
      node126 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix126) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
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
  .node 1 5 b b [
    .cache matrix96 node96,
    .cache matrix97 node97,
    .cache matrix98 node98,
    .cache matrix99 node99,
    .cache matrix106 node106,
    .cache matrix107 node107,
    .cache matrix108 node108,
    .cache matrix109 node109,
    .cache matrix117 node117,
    .cache matrix118 node118,
    .cache matrix119 node119,
    .cache matrix120 node120,
    .cache matrix121 node121,
    .cache matrix122 node122,
    .cache matrix123 node123,
    .cache matrix124 node124,
    .cache matrix125 node125,
    .cache matrix126 node126]
private theorem checked127 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix127)
      node127 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix127) ⟨1, by decide⟩ ⟨5, by decide⟩ b b = [
        ![db, db, da, db, db, db],
        ![db, db, da, db, dc, db],
        ![db, db, da, dc, db, db],
        ![db, db, da, dc, dc, db],
        ![db, db, db, db, db, db],
        ![db, db, db, db, dc, db],
        ![db, db, db, dc, db, db],
        ![db, db, db, dc, dc, db],
        ![db, db, dc, db, db, db],
        ![db, db, dc, db, dc, db],
        ![db, db, dc, dc, db, db],
        ![db, db, dc, dc, dc, db],
        ![dc, db, da, db, db, db],
        ![dc, db, da, db, dc, db],
        ![dc, db, db, db, db, db],
        ![dc, db, db, db, dc, db],
        ![dc, db, dc, db, db, db],
        ![dc, db, dc, db, dc, db]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked96, checked97, checked98, checked99, checked106, checked107, checked108, checked109,
    checked117, checked118, checked119, checked120, checked121, checked122, checked123,
    checked124, checked125, checked126]
  decide +kernel
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
    decide +kernel
  rw [hrows]
  rfl
private def matrix129 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, b, b, a],
  [b, c, none, b, b, c, a, a],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, b],
  [c, b, c, a, c, none, b, b],
  [b, b, a, b, b, b, none, c],
  [c, a, a, b, b, b, c, none]]
private def node129 : NetworkRefutation.Certificate 3 0 :=
  .node 2 5 a a [
    ]
private theorem checked129 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix129)
      node129 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix129) ⟨2, by decide⟩ ⟨5, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix130 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, b, b, a],
  [b, c, none, b, b, c, a, a],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, c],
  [c, b, c, a, c, none, b, b],
  [b, b, a, b, b, b, none, c],
  [c, a, a, b, c, b, c, none]]
private def node130 : NetworkRefutation.Certificate 3 0 :=
  .node 2 5 a a [
    ]
private theorem checked130 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix130)
      node130 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix130) ⟨2, by decide⟩ ⟨5, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix131 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, a],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, b],
  [c, b, c, a, c, none, b],
  [b, b, a, b, b, b, none]]
private def node131 : NetworkRefutation.Certificate 3 0 :=
  .node 1 2 a a [
    .cache matrix129 node129,
    .cache matrix130 node130]
private theorem checked131 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix131)
      node131 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix131) ⟨1, by decide⟩ ⟨2, by decide⟩ a a = [
        ![dc, da, da, db, db, db, dc],
        ![dc, da, da, db, dc, db, dc]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked129, checked130]
  decide +kernel
private def matrix132 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, a],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, c],
  [c, b, c, a, c, none, b],
  [b, b, a, b, c, b, none]]
private def node132 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked132 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix132)
      node132 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix132) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix133 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, a],
  [c, c, b, none, a, a, c],
  [a, c, b, a, none, c, b],
  [c, b, c, a, c, none, b],
  [b, b, a, c, b, b, none]]
private def node133 : NetworkRefutation.Certificate 3 0 :=
  .node 2 5 a a [
    ]
private theorem checked133 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix133)
      node133 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix133) ⟨2, by decide⟩ ⟨5, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix134 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, a],
  [c, c, b, none, a, a, c],
  [a, c, b, a, none, c, c],
  [c, b, c, a, c, none, b],
  [b, b, a, c, c, b, none]]
private def node134 : NetworkRefutation.Certificate 3 0 :=
  .node 2 5 a a [
    ]
private theorem checked134 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix134)
      node134 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix134) ⟨2, by decide⟩ ⟨5, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix135 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, b],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, c, b, b],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, c],
  [c, b, c, a, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, b, b, b, c, b, a, none]]
private def node135 : NetworkRefutation.Certificate 3 0 :=
  .node 4 7 a a [
    ]
private theorem checked135 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix135)
      node135 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix135) ⟨4, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix136 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, b],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, c, b, b],
  [c, c, b, none, a, a, b, c],
  [a, c, b, a, none, c, b, c],
  [c, b, c, a, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, b, b, c, c, b, a, none]]
private def node136 : NetworkRefutation.Certificate 3 0 :=
  .node 3 7 a a [
    ]
private theorem checked136 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix136)
      node136 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix136) ⟨3, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix137 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, b],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, c, b, c],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, c],
  [c, b, c, a, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, b, c, b, c, b, a, none]]
private def node137 : NetworkRefutation.Certificate 3 0 :=
  .node 4 7 a a [
    ]
private theorem checked137 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix137)
      node137 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix137) ⟨4, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix138 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, b],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, c, b, c],
  [c, c, b, none, a, a, b, c],
  [a, c, b, a, none, c, b, c],
  [c, b, c, a, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [b, b, c, c, c, b, a, none]]
private def node138 : NetworkRefutation.Certificate 3 0 :=
  .node 3 7 a a [
    ]
private theorem checked138 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix138)
      node138 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix138) ⟨3, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix139 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, c, b, b],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, c],
  [c, b, c, a, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, b, b, b, c, b, a, none]]
private def node139 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked139 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix139)
      node139 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix139) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix140 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, c, b, c],
  [c, c, b, none, a, a, b, b],
  [a, c, b, a, none, c, b, c],
  [c, b, c, a, c, none, b, b],
  [b, b, b, b, b, b, none, a],
  [c, b, c, b, c, b, a, none]]
private def node140 : NetworkRefutation.Certificate 3 0 :=
  .node 0 7 a a [
    ]
private theorem checked140 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix140)
      node140 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix140) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix141 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, b],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, b],
  [c, b, c, a, c, none, b],
  [b, b, b, b, b, b, none]]
private def node141 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 c a [
    .cache matrix135 node135,
    .cache matrix136 node136,
    .cache matrix137 node137,
    .cache matrix138 node138,
    .cache matrix139 node139,
    .cache matrix140 node140]
private theorem checked141 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix141)
      node141 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix141) ⟨4, by decide⟩ ⟨6, by decide⟩ c a = [
        ![db, db, db, db, dc, db, da],
        ![db, db, db, dc, dc, db, da],
        ![db, db, dc, db, dc, db, da],
        ![db, db, dc, dc, dc, db, da],
        ![dc, db, db, db, dc, db, da],
        ![dc, db, dc, db, dc, db, da]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked135, checked136, checked137, checked138, checked139, checked140]
  decide +kernel
private def matrix142 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, b],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, c],
  [c, b, c, a, c, none, b],
  [b, b, b, b, c, b, none]]
private def node142 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked142 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix142)
      node142 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix142) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix143 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, b],
  [c, c, b, none, a, a, c],
  [a, c, b, a, none, c, b],
  [c, b, c, a, c, none, b],
  [b, b, b, c, b, b, none]]
private def node143 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked143 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix143)
      node143 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix143) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix144 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, b],
  [c, c, b, none, a, a, c],
  [a, c, b, a, none, c, c],
  [c, b, c, a, c, none, b],
  [b, b, b, c, c, b, none]]
private def node144 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked144 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix144)
      node144 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix144) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix145 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, b, b, a],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, a, b, a],
  [a, c, b, a, none, c, b, a],
  [c, b, c, a, c, none, b, c],
  [b, b, c, b, b, b, none, c],
  [a, a, b, a, a, c, c, none]]
private def node145 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked145 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix145)
      node145 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix145) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix146 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, b, b, a],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, a, b, c],
  [a, c, b, a, none, c, b, a],
  [c, b, c, a, c, none, b, b],
  [b, b, c, b, b, b, none, c],
  [a, a, b, c, a, b, c, none]]
private def node146 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked146 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix146)
      node146 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix146) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix147 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, b, b, a],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, a, b, c],
  [a, c, b, a, none, c, b, a],
  [c, b, c, a, c, none, b, c],
  [b, b, c, b, b, b, none, c],
  [a, a, b, c, a, c, c, none]]
private def node147 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked147 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix147)
      node147 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix147) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix148 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, b, b, c],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, a, b, a],
  [a, c, b, a, none, c, b, a],
  [c, b, c, a, c, none, b, a],
  [b, b, c, b, b, b, none, c],
  [a, c, b, a, a, a, c, none]]
private def node148 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked148 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix148)
      node148 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix148) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix149 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, a],
  [a, none, c, c, c, b, b, c],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, a, b, a],
  [a, c, b, a, none, c, b, a],
  [c, b, c, a, c, none, b, c],
  [b, b, c, b, b, b, none, c],
  [a, c, b, a, a, c, c, none]]
private def node149 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked149 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix149)
      node149 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix149) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix150 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, b, b, b],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, a, b, a],
  [a, c, b, a, none, c, b, a],
  [c, b, c, a, c, none, b, a],
  [b, b, c, b, b, b, none, c],
  [c, b, b, a, a, a, c, none]]
private def node150 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked150 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix150)
      node150 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix150) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix151 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b, c],
  [a, none, c, c, c, b, b, c],
  [b, c, none, b, b, c, c, b],
  [c, c, b, none, a, a, b, a],
  [a, c, b, a, none, c, b, a],
  [c, b, c, a, c, none, b, a],
  [b, b, c, b, b, b, none, c],
  [c, c, b, a, a, a, c, none]]
private def node151 : NetworkRefutation.Certificate 3 0 :=
  .node 6 7 a a [
    ]
private theorem checked151 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix151)
      node151 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨6, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix151) ⟨6, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix152 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, c],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, b],
  [c, b, c, a, c, none, b],
  [b, b, c, b, b, b, none]]
private def node152 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a c [
    .cache matrix145 node145,
    .cache matrix146 node146,
    .cache matrix147 node147,
    .cache matrix148 node148,
    .cache matrix149 node149,
    .cache matrix150 node150,
    .cache matrix151 node151]
private theorem checked152 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix152)
      node152 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix152) ⟨4, by decide⟩ ⟨6, by decide⟩ a c = [
        ![da, da, db, da, da, dc, dc],
        ![da, da, db, dc, da, db, dc],
        ![da, da, db, dc, da, dc, dc],
        ![da, dc, db, da, da, da, dc],
        ![da, dc, db, da, da, dc, dc],
        ![dc, db, db, da, da, da, dc],
        ![dc, dc, db, da, da, da, dc]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked145, checked146, checked147, checked148, checked149, checked150, checked151]
  decide +kernel
private def matrix153 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, c],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, c],
  [c, b, c, a, c, none, b],
  [b, b, c, b, c, b, none]]
private def node153 : NetworkRefutation.Certificate 3 0 :=
  .node 4 6 a a [
    ]
private theorem checked153 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix153)
      node153 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix153) ⟨4, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix154 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, c],
  [c, c, b, none, a, a, c],
  [a, c, b, a, none, c, b],
  [c, b, c, a, c, none, b],
  [b, b, c, c, b, b, none]]
private def node154 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked154 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix154)
      node154 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix154) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix155 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, b],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, c],
  [c, c, b, none, a, a, c],
  [a, c, b, a, none, c, c],
  [c, b, c, a, c, none, b],
  [b, b, c, c, c, b, none]]
private def node155 : NetworkRefutation.Certificate 3 0 :=
  .node 3 6 a a [
    ]
private theorem checked155 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix155)
      node155 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix155) ⟨3, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix156 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, a],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, b],
  [c, b, c, a, c, none, b],
  [c, b, a, b, b, b, none]]
private def node156 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked156 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix156)
      node156 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix156) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix157 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, a],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, c],
  [c, b, c, a, c, none, b],
  [c, b, a, b, c, b, none]]
private def node157 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked157 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix157)
      node157 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix157) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix158 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, b],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, b],
  [c, b, c, a, c, none, b],
  [c, b, b, b, b, b, none]]
private def node158 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked158 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix158)
      node158 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix158) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix159 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, b],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, c],
  [c, b, c, a, c, none, b],
  [c, b, b, b, c, b, none]]
private def node159 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked159 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix159)
      node159 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix159) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix160 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, c],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, b],
  [c, b, c, a, c, none, b],
  [c, b, c, b, b, b, none]]
private def node160 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked160 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix160)
      node160 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix160) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
private def matrix161 : List (List (Atom 3 0)) := [
  [none, a, b, c, a, c, c],
  [a, none, c, c, c, b, b],
  [b, c, none, b, b, c, c],
  [c, c, b, none, a, a, b],
  [a, c, b, a, none, c, c],
  [c, b, c, a, c, none, b],
  [c, b, c, b, c, b, none]]
private def node161 : NetworkRefutation.Certificate 3 0 :=
  .node 0 6 a a [
    ]
private theorem checked161 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix161)
      node161 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix161) ⟨0, by decide⟩ ⟨6, by decide⟩ a a = [] := by
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
  .node 1 5 b b [
    .cache matrix131 node131,
    .cache matrix132 node132,
    .cache matrix133 node133,
    .cache matrix134 node134,
    .cache matrix141 node141,
    .cache matrix142 node142,
    .cache matrix143 node143,
    .cache matrix144 node144,
    .cache matrix152 node152,
    .cache matrix153 node153,
    .cache matrix154 node154,
    .cache matrix155 node155,
    .cache matrix156 node156,
    .cache matrix157 node157,
    .cache matrix158 node158,
    .cache matrix159 node159,
    .cache matrix160 node160,
    .cache matrix161 node161]
private theorem checked162 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix162)
      node162 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix162) ⟨1, by decide⟩ ⟨5, by decide⟩ b b = [
        ![db, db, da, db, db, db],
        ![db, db, da, db, dc, db],
        ![db, db, da, dc, db, db],
        ![db, db, da, dc, dc, db],
        ![db, db, db, db, db, db],
        ![db, db, db, db, dc, db],
        ![db, db, db, dc, db, db],
        ![db, db, db, dc, dc, db],
        ![db, db, dc, db, db, db],
        ![db, db, dc, db, dc, db],
        ![db, db, dc, dc, db, db],
        ![db, db, dc, dc, dc, db],
        ![dc, db, da, db, db, db],
        ![dc, db, da, db, dc, db],
        ![dc, db, db, db, db, db],
        ![dc, db, db, db, dc, db],
        ![dc, db, dc, db, db, db],
        ![dc, db, dc, db, dc, db]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked131, checked132, checked133, checked134, checked141, checked142, checked143,
    checked144, checked152, checked153, checked154, checked155, checked156, checked157,
    checked158, checked159, checked160, checked161]
  decide +kernel
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
        ![dc, db, dc, db, dc]] := by decide +kernel
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
  .node 0 7 a a [
    ]
private theorem checked168 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix168)
      node168 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix168) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
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
  .node 0 7 a a [
    ]
private theorem checked172 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix172)
      node172 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix172) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
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
  .node 0 7 a a [
    ]
private theorem checked173 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix173)
      node173 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix173) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
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
        ![dc, dc, da, db, db, dc, da]] := by decide +kernel
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
  .node 0 7 a a [
    ]
private theorem checked177 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 8) matrix177)
      node177 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨7, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 8) matrix177) ⟨0, by decide⟩ ⟨7, by decide⟩ a a = [] := by
    decide +kernel
  rw [hrows]
  rfl
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
        ![dc, db, dc, da, db, dc, da]] := by decide +kernel
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
        ![db, db, da, dc, dc, db]] := by decide +kernel
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
        ![da, da, dc, da, dc]] := by decide +kernel
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
        ![da, dc, db, db]] := by decide +kernel
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
        ![dc, dc, db]] := by decide +kernel
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
        ![db, dc]] := by decide +kernel
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
