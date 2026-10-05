/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.NetworkRefutation

/-!
# Catalogue algebra ⟨1, 1, 1⟩, number 27

Entry 27 in the ⟨1, 1, 1⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab abb~ ab~b~ aaa bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
A checked finite-network obstruction proves that no representation exists.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra27

/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := Sum.inl 0
  let b : DiversityAtom 1 1 := Sum.inr (0, false)
  let b' : DiversityAtom 1 1 := Sum.inr (0, true)
  {(a, a, b), (a, b, b'), (a, b', b'), (a, a, a), (b, b, b)}

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 1 1 where
  cycles := cycles
  associative := by decide +kernel

/-- The finite relation algebra determined by this table. -/
abbrev Algebra : Type := Complex table

/-- This algebra has the signature of its catalogue row. -/
theorem signature : HasSignature Algebra 1 1 1 :=
  Complex.hasSignature table

/-- Atomic multiplication is characterized exactly by the listed cycles and their closure. -/
theorem cycles_iff (x y z : Atom 1 1) :
    Complex.atom table z ≤ Complex.atom table x * Complex.atom table y ↔
      cycleClosure cycles x y z :=
  Complex.atom_le_mul_iff table x y z

private abbrev da : DiversityAtom 1 1 := .inl 0
private abbrev db : DiversityAtom 1 1 := .inr (0, false)
private abbrev dc : DiversityAtom 1 1 := .inr (0, true)
private abbrev a : Atom 1 1 := some da
private abbrev b : Atom 1 1 := some db
private abbrev c : Atom 1 1 := some dc

private def matrix0 : List (List (Atom 1 1)) := [
  [none, a, a, a, b, c, b],
  [a, none, a, b, c, c, a],
  [a, a, none, a, a, b, c],
  [a, c, a, none, c, c, a],
  [c, b, a, b, none, c, a],
  [b, b, c, b, b, none, a],
  [c, a, b, a, a, a, none]]

private def node0 : NetworkRefutation.Certificate 1 1 :=
  .node 1 2 b b [
    ]

private theorem checked0 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix0) node0 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix0) ⟨1, by decide⟩ ⟨2, by decide⟩ b b = [] := by
    decide +kernel
  rw [hrows]
  rfl

private def matrix1 : List (List (Atom 1 1)) := [
  [none, a, a, a, b, c, b],
  [a, none, a, b, c, c, a],
  [a, a, none, a, a, b, c],
  [a, c, a, none, c, c, a],
  [c, b, a, b, none, c, b],
  [b, b, c, b, b, none, a],
  [c, a, b, a, c, a, none]]

private def node1 : NetworkRefutation.Certificate 1 1 :=
  .node 1 2 b b [
    ]

private theorem checked1 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix1) node1 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix1) ⟨1, by decide⟩ ⟨2, by decide⟩ b b = [] := by
    decide +kernel
  rw [hrows]
  rfl

private def matrix2 : List (List (Atom 1 1)) := [
  [none, a, a, a, b, c],
  [a, none, a, b, c, c],
  [a, a, none, a, a, b],
  [a, c, a, none, c, c],
  [c, b, a, b, none, c],
  [b, b, c, b, b, none]]

private def node2 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    .cache matrix0 node0,
    .cache matrix1 node1]

private theorem checked2 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix2) node2 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix2) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [
        ![db, da, dc, da, da, da],
        ![db, da, dc, da, db, da]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked0, checked1]
  decide +kernel

private def matrix3 : List (List (Atom 1 1)) := [
  [none, a, a, a, b],
  [a, none, a, b, c],
  [a, a, none, a, a],
  [a, c, a, none, c],
  [c, b, a, b, none]]

private def node3 : NetworkRefutation.Certificate 1 1 :=
  .node 2 3 b b [
    .cache matrix2 node2]

private theorem checked3 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 5) matrix3) node3 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨3, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 5) matrix3) ⟨2, by decide⟩ ⟨3, by decide⟩ b b = [
        ![dc, dc, db, dc, dc]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked2]
  decide +kernel

private def matrix4 : List (List (Atom 1 1)) := [
  [none, a, a, a, b, c],
  [a, none, a, b, c, a],
  [a, a, none, a, c, b],
  [a, c, a, none, c, a],
  [c, b, b, b, none, a],
  [b, a, c, a, a, none]]

private def node4 : NetworkRefutation.Certificate 1 1 :=
  .node 0 1 c c [
    ]

private theorem checked4 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix4) node4 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨1, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix4) ⟨0, by decide⟩ ⟨1, by decide⟩ c c = [] := by
    decide +kernel
  rw [hrows]
  rfl

private def matrix5 : List (List (Atom 1 1)) := [
  [none, a, a, a, b],
  [a, none, a, b, c],
  [a, a, none, a, c],
  [a, c, a, none, c],
  [c, b, b, b, none]]

private def node5 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 c c [
    .cache matrix4 node4]

private theorem checked5 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 5) matrix5) node5 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 5) matrix5) ⟨0, by decide⟩ ⟨2, by decide⟩ c c = [
        ![dc, da, db, da, da]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked4]
  decide +kernel

private def matrix6 : List (List (Atom 1 1)) := [
  [none, a, a, a],
  [a, none, a, b],
  [a, a, none, a],
  [a, c, a, none]]

private def node6 : NetworkRefutation.Certificate 1 1 :=
  .node 0 3 b b [
    .cache matrix3 node3,
    .cache matrix5 node5]

private theorem checked6 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 4) matrix6) node6 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨3, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 4) matrix6) ⟨0, by decide⟩ ⟨3, by decide⟩ b b = [
        ![db, dc, da, dc],
        ![db, dc, dc, dc]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked3, checked5]
  decide +kernel

private def matrix7 : List (List (Atom 1 1)) := [
  [none, a, a, a, b, a, c],
  [a, none, a, b, a, c, b],
  [a, a, none, c, a, c, a],
  [a, c, b, none, a, c, a],
  [c, a, a, a, none, b, c],
  [a, b, b, b, c, none, a],
  [b, c, a, a, b, a, none]]

private def node7 : NetworkRefutation.Certificate 1 1 :=
  .node 2 4 b b [
    ]

private theorem checked7 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix7) node7 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix7) ⟨2, by decide⟩ ⟨4, by decide⟩ b b = [] := by
    decide +kernel
  rw [hrows]
  rfl

private def matrix8 : List (List (Atom 1 1)) := [
  [none, a, a, a, b, a, c],
  [a, none, a, b, a, c, b],
  [a, a, none, c, a, c, a],
  [a, c, b, none, a, c, b],
  [c, a, a, a, none, b, c],
  [a, b, b, b, c, none, a],
  [b, c, a, c, b, a, none]]

private def node8 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 c c [
    ]

private theorem checked8 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix8) node8 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix8) ⟨0, by decide⟩ ⟨2, by decide⟩ c c = [] := by
    decide +kernel
  rw [hrows]
  rfl

private def matrix9 : List (List (Atom 1 1)) := [
  [none, a, a, a, b, a],
  [a, none, a, b, a, c],
  [a, a, none, c, a, c],
  [a, c, b, none, a, c],
  [c, a, a, a, none, b],
  [a, b, b, b, c, none]]

private def node9 : NetworkRefutation.Certificate 1 1 :=
  .node 1 4 b b [
    .cache matrix7 node7,
    .cache matrix8 node8]

private theorem checked9 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix9) node9 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix9) ⟨1, by decide⟩ ⟨4, by decide⟩ b b = [
        ![dc, db, da, da, dc, da],
        ![dc, db, da, db, dc, da]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked7, checked8]
  decide +kernel

private def matrix10 : List (List (Atom 1 1)) := [
  [none, a, a, a, b, b, c],
  [a, none, a, b, a, c, b],
  [a, a, none, c, a, c, a],
  [a, c, b, none, a, c, a],
  [c, a, a, a, none, b, c],
  [c, b, b, b, c, none, a],
  [b, c, a, a, b, a, none]]

private def node10 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 c c [
    ]

private theorem checked10 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix10) node10 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix10) ⟨0, by decide⟩ ⟨2, by decide⟩ c c = [] := by
    decide +kernel
  rw [hrows]
  rfl

private def matrix11 : List (List (Atom 1 1)) := [
  [none, a, a, a, b, b, c],
  [a, none, a, b, a, c, b],
  [a, a, none, c, a, c, a],
  [a, c, b, none, a, c, b],
  [c, a, a, a, none, b, c],
  [c, b, b, b, c, none, a],
  [b, c, a, c, b, a, none]]

private def node11 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 c c [
    ]

private theorem checked11 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix11) node11 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix11) ⟨0, by decide⟩ ⟨2, by decide⟩ c c = [] := by
    decide +kernel
  rw [hrows]
  rfl

private def matrix12 : List (List (Atom 1 1)) := [
  [none, a, a, a, b, b],
  [a, none, a, b, a, c],
  [a, a, none, c, a, c],
  [a, c, b, none, a, c],
  [c, a, a, a, none, b],
  [c, b, b, b, c, none]]

private def node12 : NetworkRefutation.Certificate 1 1 :=
  .node 1 4 b b [
    .cache matrix10 node10,
    .cache matrix11 node11]

private theorem checked12 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix12) node12 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix12) ⟨1, by decide⟩ ⟨4, by decide⟩ b b = [
        ![dc, db, da, da, dc, da],
        ![dc, db, da, db, dc, da]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked10, checked11]
  decide +kernel

private def matrix13 : List (List (Atom 1 1)) := [
  [none, a, a, a, b],
  [a, none, a, b, a],
  [a, a, none, c, a],
  [a, c, b, none, a],
  [c, a, a, a, none]]

private def node13 : NetworkRefutation.Certificate 1 1 :=
  .node 2 4 c c [
    .cache matrix9 node9,
    .cache matrix12 node12]

private theorem checked13 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 5) matrix13) node13 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 5) matrix13) ⟨2, by decide⟩ ⟨4, by decide⟩ c c = [
        ![da, dc, dc, dc, db],
        ![db, dc, dc, dc, db]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked9, checked12]
  decide +kernel

private def matrix14 : List (List (Atom 1 1)) := [
  [none, a, a, a],
  [a, none, a, b],
  [a, a, none, c],
  [a, c, b, none]]

private def node14 : NetworkRefutation.Certificate 1 1 :=
  .node 0 1 b a [
    .cache matrix13 node13]

private theorem checked14 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 4) matrix14) node14 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨1, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 4) matrix14) ⟨0, by decide⟩ ⟨1, by decide⟩ b a = [
        ![db, da, da, da]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked13]
  decide +kernel

private def matrix15 : List (List (Atom 1 1)) := [
  [none, a, a],
  [a, none, a],
  [a, a, none]]

private def node15 : NetworkRefutation.Certificate 1 1 :=
  .node 0 1 a c [
    .cache matrix6 node6,
    .cache matrix14 node14]

private theorem checked15 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 3) matrix15) node15 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨1, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 3) matrix15) ⟨0, by decide⟩ ⟨1, by decide⟩ a c = [
        ![da, db, da],
        ![da, db, dc]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked6, checked14]
  decide +kernel

private def matrix16 : List (List (Atom 1 1)) := [
  [none, a],
  [a, none]]

private def node16 : NetworkRefutation.Certificate 1 1 :=
  .node 0 1 a a [
    .cache matrix15 node15]

private theorem checked16 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 2) matrix16) node16 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨1, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 2) matrix16) ⟨0, by decide⟩ ⟨1, by decide⟩ a a = [
        ![da, da]] := by decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked15]
  decide +kernel

/-- A finite tree of impossible composition-witness extensions. -/
private def obstruction : NetworkRefutation.Certificate 1 1 := by exact node16

/-- This catalogue algebra has no representation by binary relations. -/
theorem not_representable : ¬ Representable Algebra := by
  apply NetworkRefutation.not_representable table (some (.inl 0)) obstruction
  have hi : NetworkRefutation.initial (some (.inl 0)) =
      NetworkRefutation.ofMatrix (n := 2) matrix16 := by decide +kernel
  rw [hi]
  exact checked16

end Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra27
