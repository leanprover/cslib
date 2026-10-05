/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/
module
public import Cslib.Foundations.RelationAlgebra.FastCycles
public import Cslib.Foundations.RelationAlgebra.NetworkRefutation
/-!
# Catalogue algebra ⟨1, 1, 1⟩, number 34
Entry 34 in the ⟨1, 1, 1⟩ row of
[Jipsen’s catalogue](https://www1.chapman.edu/~jipsen/gap/ramaddux.html).
The source lists cycles `aab abb abb~ ab~b~ bbb`.
Identity cycles are supplied by `cycleClosure`; only diversity cycles are stored below.
A checked finite-network obstruction proves that no representation exists.
-/
@[expose] public section
namespace Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra34
/-- The diversity-cycle representatives listed in the source. -/
def cycles : Finset (Cycle 1 1) :=
  let a : DiversityAtom 1 1 := Sum.inl 0
  let b : DiversityAtom 1 1 := Sum.inr (0, false)
  let b' : DiversityAtom 1 1 := Sum.inr (0, true)
  {(a, a, b), (a, b, b), (a, b, b'), (a, b', b'), (b, b, b)}
private theorem tableCode_eq : tableCode cycles = 12675652614354011169 := by decide +kernel

/-- The cycle table, with associativity checked by the kernel. -/
def table : IntegralCycleTable 1 1 where
  cycles := cycles
  associative := atomCompositionAssociative_of_assocCheck (by
    rw [tableCode_eq]
    decide +kernel)
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
  [none, a, a, c, a, b, a],
  [a, none, c, b, b, c, c],
  [a, b, none, a, b, b, c],
  [b, c, a, none, b, a, c],
  [a, c, c, c, none, a, c],
  [c, b, c, a, a, none, a],
  [a, b, b, b, b, a, none]]
private def node0 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked0 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix0) node0 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix0) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix1 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, b, b],
  [a, none, c, b, b, c, a],
  [a, b, none, a, b, b, c],
  [b, c, a, none, b, a, b],
  [a, c, c, c, none, a, c],
  [c, b, c, a, a, none, a],
  [c, a, b, c, b, a, none]]
private def node1 : NetworkRefutation.Certificate 1 1 :=
  .node 0 4 c c [
    ]
private theorem checked1 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix1) node1 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix1) ⟨0, by decide⟩ ⟨4, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix2 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, b, c],
  [a, none, c, b, b, c, a],
  [a, b, none, a, b, b, c],
  [b, c, a, none, b, a, b],
  [a, c, c, c, none, a, c],
  [c, b, c, a, a, none, a],
  [b, a, b, c, b, a, none]]
private def node2 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked2 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix2) node2 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix2) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix3 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, b, c],
  [a, none, c, b, b, c, a],
  [a, b, none, a, b, b, c],
  [b, c, a, none, b, a, c],
  [a, c, c, c, none, a, c],
  [c, b, c, a, a, none, a],
  [b, a, b, b, b, a, none]]
private def node3 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked3 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix3) node3 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix3) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix4 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, b, c],
  [a, none, c, b, b, c, c],
  [a, b, none, a, b, b, c],
  [b, c, a, none, b, a, c],
  [a, c, c, c, none, a, c],
  [c, b, c, a, a, none, a],
  [b, b, b, b, b, a, none]]
private def node4 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked4 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix4) node4 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix4) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix5 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, b],
  [a, none, c, b, b, c],
  [a, b, none, a, b, b],
  [b, c, a, none, b, a],
  [a, c, c, c, none, a],
  [c, b, c, a, a, none]]
private def node5 : NetworkRefutation.Certificate 1 1 :=
  .node 2 5 c a [
    .cache matrix0 node0,
    .cache matrix1 node1,
    .cache matrix2 node2,
    .cache matrix3 node3,
    .cache matrix4 node4]
private theorem checked5 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix5) node5 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix5) ⟨2, by decide⟩ ⟨5, by decide⟩ c a = [
        ![da, dc, dc, dc, dc, da],
        ![db, da, dc, db, dc, da],
        ![dc, da, dc, db, dc, da],
        ![dc, da, dc, dc, dc, da],
        ![dc, dc, dc, dc, dc, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked0, checked1, checked2, checked3, checked4]
  decide +kernel
private def matrix6 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, b, a],
  [a, none, c, b, b, c, b],
  [a, b, none, a, b, c, b],
  [b, c, a, none, b, a, a],
  [a, c, c, c, none, a, b],
  [c, b, b, a, a, none, b],
  [a, c, c, a, c, c, none]]
private def node6 : NetworkRefutation.Certificate 1 1 :=
  .node 3 6 c c [
    ]
private theorem checked6 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix6) node6 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix6) ⟨3, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix7 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, b, b],
  [a, none, c, b, b, c, a],
  [a, b, none, a, b, c, b],
  [b, c, a, none, b, a, a],
  [a, c, c, c, none, a, b],
  [c, b, b, a, a, none, b],
  [c, a, c, a, c, c, none]]
private def node7 : NetworkRefutation.Certificate 1 1 :=
  .node 3 6 c c [
    ]
private theorem checked7 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix7) node7 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix7) ⟨3, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix8 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, b, b],
  [a, none, c, b, b, c, b],
  [a, b, none, a, b, c, b],
  [b, c, a, none, b, a, a],
  [a, c, c, c, none, a, b],
  [c, b, b, a, a, none, b],
  [c, c, c, a, c, c, none]]
private def node8 : NetworkRefutation.Certificate 1 1 :=
  .node 3 6 c c [
    ]
private theorem checked8 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix8) node8 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix8) ⟨3, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix9 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, b],
  [a, none, c, b, b, c],
  [a, b, none, a, b, c],
  [b, c, a, none, b, a],
  [a, c, c, c, none, a],
  [c, b, b, a, a, none]]
private def node9 : NetworkRefutation.Certificate 1 1 :=
  .node 3 4 a c [
    .cache matrix6 node6,
    .cache matrix7 node7,
    .cache matrix8 node8]
private theorem checked9 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix9) node9 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix9) ⟨3, by decide⟩ ⟨4, by decide⟩ a c = [
        ![da, db, db, da, db, db],
        ![db, da, db, da, db, db],
        ![db, db, db, da, db, db]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked6, checked7, checked8]
  decide +kernel
private def matrix10 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c, c],
  [a, none, c, b, b, c, a],
  [a, b, none, a, b, a, b],
  [b, c, a, none, b, c, a],
  [a, c, c, c, none, a, b],
  [b, b, a, b, a, none, c],
  [b, a, c, a, c, b, none]]
private def node10 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    ]
private theorem checked10 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix10) node10 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix10) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix11 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c],
  [a, none, c, b, b, c],
  [a, b, none, a, b, a],
  [b, c, a, none, b, c],
  [a, c, c, c, none, a],
  [b, b, a, b, a, none]]
private def node11 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 b b [
    .cache matrix10 node10]
private theorem checked11 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix11) node11 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix11) ⟨4, by decide⟩ ⟨5, by decide⟩ b b = [
        ![dc, da, db, da, db, dc]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked10]
  decide +kernel
private def matrix12 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c, b],
  [a, none, c, b, b, c, a],
  [a, b, none, a, b, b, c],
  [b, c, a, none, b, a, b],
  [a, c, c, c, none, a, c],
  [b, b, c, a, a, none, a],
  [c, a, b, c, b, a, none]]
private def node12 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 b b [
    ]
private theorem checked12 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix12) node12 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix12) ⟨4, by decide⟩ ⟨5, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix13 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c],
  [a, none, c, b, b, c],
  [a, b, none, a, b, b],
  [b, c, a, none, b, a],
  [a, c, c, c, none, a],
  [b, b, c, a, a, none]]
private def node13 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    .cache matrix12 node12]
private theorem checked13 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix13) node13 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix13) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [
        ![db, da, dc, db, dc, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked12]
  decide +kernel
private def matrix14 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c, c],
  [a, none, c, b, b, c, a],
  [a, b, none, a, b, b, b],
  [b, c, a, none, b, c, a],
  [a, c, c, c, none, a, b],
  [b, b, c, b, a, none, c],
  [b, a, c, a, c, b, none]]
private def node14 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    ]
private theorem checked14 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix14) node14 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix14) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix15 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c],
  [a, none, c, b, b, c],
  [a, b, none, a, b, b],
  [b, c, a, none, b, c],
  [a, c, c, c, none, a],
  [b, b, c, b, a, none]]
private def node15 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 b b [
    .cache matrix14 node14]
private theorem checked15 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix15) node15 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix15) ⟨4, by decide⟩ ⟨5, by decide⟩ b b = [
        ![dc, da, db, da, db, dc]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked14]
  decide +kernel
private def matrix16 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c, b],
  [a, none, c, b, b, c, a],
  [a, b, none, a, b, c, a],
  [b, c, a, none, b, a, b],
  [a, c, c, c, none, a, b],
  [b, b, b, a, a, none, a],
  [c, a, a, c, c, a, none]]
private def node16 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 c c [
    ]
private theorem checked16 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix16) node16 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix16) ⟨5, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix17 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c, b],
  [a, none, c, b, b, c, a],
  [a, b, none, a, b, c, a],
  [b, c, a, none, b, a, b],
  [a, c, c, c, none, a, c],
  [b, b, b, a, a, none, a],
  [c, a, a, c, b, a, none]]
private def node17 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 b b [
    ]
private theorem checked17 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix17) node17 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix17) ⟨4, by decide⟩ ⟨5, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix18 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c, b],
  [a, none, c, b, b, c, a],
  [a, b, none, a, b, c, b],
  [b, c, a, none, b, a, b],
  [a, c, c, c, none, a, b],
  [b, b, b, a, a, none, a],
  [c, a, c, c, c, a, none]]
private def node18 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 c c [
    ]
private theorem checked18 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix18) node18 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix18) ⟨5, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix19 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c, b],
  [a, none, c, b, b, c, a],
  [a, b, none, a, b, c, b],
  [b, c, a, none, b, a, b],
  [a, c, c, c, none, a, c],
  [b, b, b, a, a, none, a],
  [c, a, c, c, b, a, none]]
private def node19 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 b b [
    ]
private theorem checked19 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix19) node19 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix19) ⟨4, by decide⟩ ⟨5, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix20 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c, b],
  [a, none, c, b, b, c, a],
  [a, b, none, a, b, c, c],
  [b, c, a, none, b, a, b],
  [a, c, c, c, none, a, c],
  [b, b, b, a, a, none, a],
  [c, a, b, c, b, a, none]]
private def node20 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 b b [
    ]
private theorem checked20 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix20) node20 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix20) ⟨4, by decide⟩ ⟨5, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix21 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c, b],
  [a, none, c, b, b, c, b],
  [a, b, none, a, b, c, a],
  [b, c, a, none, b, a, b],
  [a, c, c, c, none, a, b],
  [b, b, b, a, a, none, a],
  [c, c, a, c, c, a, none]]
private def node21 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 c c [
    ]
private theorem checked21 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix21) node21 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix21) ⟨5, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix22 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c, b],
  [a, none, c, b, b, c, b],
  [a, b, none, a, b, c, a],
  [b, c, a, none, b, a, b],
  [a, c, c, c, none, a, c],
  [b, b, b, a, a, none, a],
  [c, c, a, c, b, a, none]]
private def node22 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 b b [
    ]
private theorem checked22 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix22) node22 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix22) ⟨4, by decide⟩ ⟨5, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix23 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c, b],
  [a, none, c, b, b, c, b],
  [a, b, none, a, b, c, b],
  [b, c, a, none, b, a, b],
  [a, c, c, c, none, a, b],
  [b, b, b, a, a, none, a],
  [c, c, c, c, c, a, none]]
private def node23 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 c c [
    ]
private theorem checked23 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix23) node23 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix23) ⟨5, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix24 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c, b],
  [a, none, c, b, b, c, b],
  [a, b, none, a, b, c, b],
  [b, c, a, none, b, a, b],
  [a, c, c, c, none, a, c],
  [b, b, b, a, a, none, a],
  [c, c, c, c, b, a, none]]
private def node24 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 c c [
    ]
private theorem checked24 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix24) node24 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix24) ⟨5, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix25 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c],
  [a, none, c, b, b, c],
  [a, b, none, a, b, c],
  [b, c, a, none, b, a],
  [a, c, c, c, none, a],
  [b, b, b, a, a, none]]
private def node25 : NetworkRefutation.Certificate 1 1 :=
  .node 0 5 b a [
    .cache matrix16 node16,
    .cache matrix17 node17,
    .cache matrix18 node18,
    .cache matrix19 node19,
    .cache matrix20 node20,
    .cache matrix21 node21,
    .cache matrix22 node22,
    .cache matrix23 node23,
    .cache matrix24 node24]
private theorem checked25 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix25) node25 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix25) ⟨0, by decide⟩ ⟨5, by decide⟩ b a = [
        ![db, da, da, db, db, da],
        ![db, da, da, db, dc, da],
        ![db, da, db, db, db, da],
        ![db, da, db, db, dc, da],
        ![db, da, dc, db, dc, da],
        ![db, db, da, db, db, da],
        ![db, db, da, db, dc, da],
        ![db, db, db, db, db, da],
        ![db, db, db, db, dc, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked16, checked17, checked18, checked19, checked20, checked21, checked22, checked23,
    checked24]
  decide +kernel
private def matrix26 : List (List (Atom 1 1)) := [
  [none, a, a, c, a, c],
  [a, none, c, b, b, c],
  [a, b, none, a, b, c],
  [b, c, a, none, b, c],
  [a, c, c, c, none, a],
  [b, b, b, b, a, none]]
private def node26 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 b b [
    ]
private theorem checked26 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix26) node26 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix26) ⟨4, by decide⟩ ⟨5, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix27 : List (List (Atom 1 1)) := [
  [none, a, a, c, a],
  [a, none, c, b, b],
  [a, b, none, a, b],
  [b, c, a, none, b],
  [a, c, c, c, none]]
private def node27 : NetworkRefutation.Certificate 1 1 :=
  .node 1 4 c a [
    .cache matrix5 node5,
    .cache matrix9 node9,
    .cache matrix11 node11,
    .cache matrix13 node13,
    .cache matrix15 node15,
    .cache matrix25 node25,
    .cache matrix26 node26]
private theorem checked27 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 5) matrix27) node27 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 5) matrix27) ⟨1, by decide⟩ ⟨4, by decide⟩ c a = [
        ![db, dc, db, da, da],
        ![db, dc, dc, da, da],
        ![dc, dc, da, dc, da],
        ![dc, dc, db, da, da],
        ![dc, dc, db, dc, da],
        ![dc, dc, dc, da, da],
        ![dc, dc, dc, dc, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked5, checked9, checked11, checked13, checked15, checked25, checked26]
  decide +kernel
private def matrix28 : List (List (Atom 1 1)) := [
  [none, a, a, c],
  [a, none, c, b],
  [a, b, none, a],
  [b, c, a, none]]
private def node28 : NetworkRefutation.Certificate 1 1 :=
  .node 0 3 a c [
    .cache matrix27 node27]
private theorem checked28 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 4) matrix28) node28 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨3, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 4) matrix28) ⟨0, by decide⟩ ⟨3, by decide⟩ a c = [
        ![da, db, db, db]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked27]
  decide +kernel
private def matrix29 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, a, c],
  [c, b, a, a, none, b, c],
  [c, c, a, a, c, none, a],
  [a, b, c, b, b, a, none]]
private def node29 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked29 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix29) node29 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix29) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix30 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, c],
  [b, c, c, none, a, a, c],
  [c, b, a, a, none, b, c],
  [c, c, a, a, c, none, a],
  [a, b, b, b, b, a, none]]
private def node30 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked30 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix30) node30 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix30) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix31 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, b],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, a, b],
  [c, b, a, a, none, b, c],
  [c, c, a, a, c, none, a],
  [c, a, c, c, b, a, none]]
private def node31 : NetworkRefutation.Certificate 1 1 :=
  .node 2 5 c c [
    ]
private theorem checked31 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix31) node31 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix31) ⟨2, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix32 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, a, b],
  [c, b, a, a, none, b, c],
  [c, c, a, a, c, none, a],
  [b, a, c, c, b, a, none]]
private def node32 : NetworkRefutation.Certificate 1 1 :=
  .node 2 5 c c [
    ]
private theorem checked32 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix32) node32 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix32) ⟨2, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix33 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, a, c],
  [c, b, a, a, none, b, c],
  [c, c, a, a, c, none, a],
  [b, a, c, b, b, a, none]]
private def node33 : NetworkRefutation.Certificate 1 1 :=
  .node 2 5 c c [
    ]
private theorem checked33 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix33) node33 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix33) ⟨2, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix34 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, a, c],
  [b, c, c, none, a, a, c],
  [c, b, a, a, none, b, c],
  [c, c, a, a, c, none, a],
  [b, a, b, b, b, a, none]]
private def node34 : NetworkRefutation.Certificate 1 1 :=
  .node 1 6 b b [
    ]
private theorem checked34 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix34) node34 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix34) ⟨1, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix35 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, a, c],
  [c, b, a, a, none, b, c],
  [c, c, a, a, c, none, a],
  [b, b, c, b, b, a, none]]
private def node35 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked35 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix35) node35 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix35) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix36 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, c],
  [b, c, c, none, a, a, c],
  [c, b, a, a, none, b, c],
  [c, c, a, a, c, none, a],
  [b, b, b, b, b, a, none]]
private def node36 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked36 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix36) node36 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix36) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix37 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b],
  [a, none, c, b, c, b],
  [a, b, none, b, a, a],
  [b, c, c, none, a, a],
  [c, b, a, a, none, b],
  [c, c, a, a, c, none]]
private def node37 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 c a [
    .cache matrix29 node29,
    .cache matrix30 node30,
    .cache matrix31 node31,
    .cache matrix32 node32,
    .cache matrix33 node33,
    .cache matrix34 node34,
    .cache matrix35 node35,
    .cache matrix36 node36]
private theorem checked37 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix37) node37 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix37) ⟨4, by decide⟩ ⟨5, by decide⟩ c a = [
        ![da, dc, db, dc, dc, da],
        ![da, dc, dc, dc, dc, da],
        ![db, da, db, db, dc, da],
        ![dc, da, db, db, dc, da],
        ![dc, da, db, dc, dc, da],
        ![dc, da, dc, dc, dc, da],
        ![dc, dc, db, dc, dc, da],
        ![dc, dc, dc, dc, dc, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked29, checked30, checked31, checked32, checked33, checked34, checked35, checked36]
  decide +kernel
private def matrix38 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, b, a],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [a, b, c, a, b, a, none]]
private def node38 : NetworkRefutation.Certificate 1 1 :=
  .node 2 4 c c [
    ]
private theorem checked38 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix38) node38 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix38) ⟨2, by decide⟩ ⟨4, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix39 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, b, c],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [a, b, c, b, b, a, none]]
private def node39 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked39 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix39) node39 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix39) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix40 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, c],
  [b, c, c, none, a, b, a],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [a, b, b, a, b, a, none]]
private def node40 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked40 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix40) node40 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix40) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix41 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, c],
  [b, c, c, none, a, b, c],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [a, b, b, b, b, a, none]]
private def node41 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked41 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix41) node41 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix41) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix42 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, b],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, b, a],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [c, a, c, a, b, a, none]]
private def node42 : NetworkRefutation.Certificate 1 1 :=
  .node 2 5 c c [
    ]
private theorem checked42 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix42) node42 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix42) ⟨2, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix43 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, b],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, b, b],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [c, a, c, c, b, a, none]]
private def node43 : NetworkRefutation.Certificate 1 1 :=
  .node 2 5 c c [
    ]
private theorem checked43 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix43) node43 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix43) ⟨2, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix44 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, b],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, a, c],
  [b, c, c, none, a, b, a],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [c, a, b, a, b, a, none]]
private def node44 : NetworkRefutation.Certificate 1 1 :=
  .node 1 6 b b [
    ]
private theorem checked44 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix44) node44 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix44) ⟨1, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix45 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, b],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, b, a],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [c, b, c, a, b, a, none]]
private def node45 : NetworkRefutation.Certificate 1 1 :=
  .node 2 5 c c [
    ]
private theorem checked45 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix45) node45 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix45) ⟨2, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix46 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, b],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, c],
  [b, c, c, none, a, b, a],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [c, b, b, a, b, a, none]]
private def node46 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked46 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix46) node46 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix46) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix47 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, b, a],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [b, a, c, a, b, a, none]]
private def node47 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    ]
private theorem checked47 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix47) node47 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix47) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix48 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, b, b],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [b, a, c, c, b, a, none]]
private def node48 : NetworkRefutation.Certificate 1 1 :=
  .node 2 5 c c [
    ]
private theorem checked48 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix48) node48 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix48) ⟨2, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix49 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, b, c],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [b, a, c, b, b, a, none]]
private def node49 : NetworkRefutation.Certificate 1 1 :=
  .node 2 5 c c [
    ]
private theorem checked49 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix49) node49 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix49) ⟨2, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix50 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, a, c],
  [b, c, c, none, a, b, a],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [b, a, b, a, b, a, none]]
private def node50 : NetworkRefutation.Certificate 1 1 :=
  .node 1 6 b b [
    ]
private theorem checked50 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix50) node50 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix50) ⟨1, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix51 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, a, c],
  [b, c, c, none, a, b, c],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [b, a, b, b, b, a, none]]
private def node51 : NetworkRefutation.Certificate 1 1 :=
  .node 1 6 b b [
    ]
private theorem checked51 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix51) node51 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix51) ⟨1, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix52 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, b, a],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [b, b, c, a, b, a, none]]
private def node52 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    ]
private theorem checked52 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix52) node52 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix52) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix53 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, b],
  [b, c, c, none, a, b, c],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [b, b, c, b, b, a, none]]
private def node53 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked53 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix53) node53 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix53) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix54 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, c],
  [b, c, c, none, a, b, a],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [b, b, b, a, b, a, none]]
private def node54 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked54 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix54) node54 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix54) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix55 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b, c],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, a, c],
  [b, c, c, none, a, b, c],
  [c, b, a, a, none, b, c],
  [c, c, a, c, c, none, a],
  [b, b, b, b, b, a, none]]
private def node55 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked55 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix55) node55 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix55) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix56 : List (List (Atom 1 1)) := [
  [none, a, a, c, b, b],
  [a, none, c, b, c, b],
  [a, b, none, b, a, a],
  [b, c, c, none, a, b],
  [c, b, a, a, none, b],
  [c, c, a, c, c, none]]
private def node56 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 c a [
    .cache matrix38 node38,
    .cache matrix39 node39,
    .cache matrix40 node40,
    .cache matrix41 node41,
    .cache matrix42 node42,
    .cache matrix43 node43,
    .cache matrix44 node44,
    .cache matrix45 node45,
    .cache matrix46 node46,
    .cache matrix47 node47,
    .cache matrix48 node48,
    .cache matrix49 node49,
    .cache matrix50 node50,
    .cache matrix51 node51,
    .cache matrix52 node52,
    .cache matrix53 node53,
    .cache matrix54 node54,
    .cache matrix55 node55]
private theorem checked56 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix56) node56 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix56) ⟨4, by decide⟩ ⟨5, by decide⟩ c a = [
        ![da, dc, db, da, dc, da],
        ![da, dc, db, dc, dc, da],
        ![da, dc, dc, da, dc, da],
        ![da, dc, dc, dc, dc, da],
        ![db, da, db, da, dc, da],
        ![db, da, db, db, dc, da],
        ![db, da, dc, da, dc, da],
        ![db, dc, db, da, dc, da],
        ![db, dc, dc, da, dc, da],
        ![dc, da, db, da, dc, da],
        ![dc, da, db, db, dc, da],
        ![dc, da, db, dc, dc, da],
        ![dc, da, dc, da, dc, da],
        ![dc, da, dc, dc, dc, da],
        ![dc, dc, db, da, dc, da],
        ![dc, dc, db, dc, dc, da],
        ![dc, dc, dc, da, dc, da],
        ![dc, dc, dc, dc, dc, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked38, checked39, checked40, checked41, checked42, checked43, checked44, checked45,
    checked46, checked47, checked48, checked49, checked50, checked51, checked52, checked53,
    checked54, checked55]
  decide +kernel
private def matrix57 : List (List (Atom 1 1)) := [
  [none, a, a, c, b],
  [a, none, c, b, c],
  [a, b, none, b, a],
  [b, c, c, none, a],
  [c, b, a, a, none]]
private def node57 : NetworkRefutation.Certificate 1 1 :=
  .node 1 2 b a [
    .cache matrix37 node37,
    .cache matrix56 node56]
private theorem checked57 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 5) matrix57) node57 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 5) matrix57) ⟨1, by decide⟩ ⟨2, by decide⟩ b a = [
        ![db, db, da, da, db],
        ![db, db, da, db, db]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked37, checked56]
  decide +kernel
private def matrix58 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, b],
  [a, none, c, b, c, a, a],
  [a, b, none, b, a, c, b],
  [b, c, c, none, a, a, b],
  [b, b, a, a, none, b, a],
  [c, a, b, a, c, none, b],
  [c, a, c, c, a, c, none]]
private def node58 : NetworkRefutation.Certificate 1 1 :=
  .node 4 6 c c [
    ]
private theorem checked58 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix58) node58 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix58) ⟨4, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix59 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, b],
  [a, none, c, b, c, a, b],
  [a, b, none, b, a, c, b],
  [b, c, c, none, a, a, b],
  [b, b, a, a, none, b, a],
  [c, a, b, a, c, none, a],
  [c, c, c, c, a, a, none]]
private def node59 : NetworkRefutation.Certificate 1 1 :=
  .node 4 6 c c [
    ]
private theorem checked59 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix59) node59 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix59) ⟨4, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix60 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, b],
  [a, none, c, b, c, a, b],
  [a, b, none, b, a, c, b],
  [b, c, c, none, a, a, b],
  [b, b, a, a, none, b, a],
  [c, a, b, a, c, none, b],
  [c, c, c, c, a, c, none]]
private def node60 : NetworkRefutation.Certificate 1 1 :=
  .node 4 6 c c [
    ]
private theorem checked60 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix60) node60 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix60) ⟨4, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix61 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b],
  [a, none, c, b, c, a],
  [a, b, none, b, a, c],
  [b, c, c, none, a, a],
  [b, b, a, a, none, b],
  [c, a, b, a, c, none]]
private def node61 : NetworkRefutation.Certificate 1 1 :=
  .node 0 4 b a [
    .cache matrix58 node58,
    .cache matrix59 node59,
    .cache matrix60 node60]
private theorem checked61 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix61) node61 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix61) ⟨0, by decide⟩ ⟨4, by decide⟩ b a = [
        ![db, da, db, db, da, db],
        ![db, db, db, db, da, da],
        ![db, db, db, db, da, db]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked58, checked59, checked60]
  decide +kernel
private def matrix62 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, a],
  [a, none, c, b, c, c, c],
  [a, b, none, b, a, c, b],
  [b, c, c, none, a, a, c],
  [b, b, a, a, none, b, c],
  [c, b, b, a, c, none, a],
  [a, b, c, b, b, a, none]]
private def node62 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked62 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix62) node62 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix62) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix63 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, a],
  [a, none, c, b, c, c, c],
  [a, b, none, b, a, c, c],
  [b, c, c, none, a, a, a],
  [b, b, a, a, none, b, c],
  [c, b, b, a, c, none, c],
  [a, b, b, a, b, b, none]]
private def node63 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked63 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix63) node63 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix63) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix64 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, a],
  [a, none, c, b, c, c, c],
  [a, b, none, b, a, c, c],
  [b, c, c, none, a, a, c],
  [b, b, a, a, none, b, c],
  [c, b, b, a, c, none, a],
  [a, b, b, b, b, a, none]]
private def node64 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked64 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix64) node64 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix64) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix65 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, a],
  [a, none, c, b, c, c, c],
  [a, b, none, b, a, c, c],
  [b, c, c, none, a, a, c],
  [b, b, a, a, none, b, c],
  [c, b, b, a, c, none, c],
  [a, b, b, b, b, b, none]]
private def node65 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked65 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix65) node65 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix65) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix66 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b],
  [a, none, c, b, c, c],
  [a, b, none, b, a, c],
  [b, c, c, none, a, a],
  [b, b, a, a, none, b],
  [c, b, b, a, c, none]]
private def node66 : NetworkRefutation.Certificate 1 1 :=
  .node 0 4 a b [
    .cache matrix62 node62,
    .cache matrix63 node63,
    .cache matrix64 node64,
    .cache matrix65 node65]
private theorem checked66 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix66) node66 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix66) ⟨0, by decide⟩ ⟨4, by decide⟩ a b = [
        ![da, dc, db, dc, dc, da],
        ![da, dc, dc, da, dc, dc],
        ![da, dc, dc, dc, dc, da],
        ![da, dc, dc, dc, dc, dc]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked62, checked63, checked64, checked65]
  decide +kernel
private def matrix67 : List (List (Atom 1 1)) := [
  [none, a, a, c, c],
  [a, none, c, b, c],
  [a, b, none, b, a],
  [b, c, c, none, a],
  [b, b, a, a, none]]
private def node67 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    .cache matrix61 node61,
    .cache matrix66 node66]
private theorem checked67 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 5) matrix67) node67 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 5) matrix67) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [
        ![db, da, dc, da, db],
        ![db, dc, dc, da, db]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked61, checked66]
  decide +kernel
private def matrix68 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, a, b],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, a],
  [a, c, c, c, a, none, b],
  [c, a, c, a, a, c, none]]
private def node68 : NetworkRefutation.Certificate 1 1 :=
  .node 3 6 c c [
    ]
private theorem checked68 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix68) node68 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix68) ⟨3, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix69 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, a, b],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, a],
  [a, c, c, c, a, none, c],
  [c, a, c, a, a, b, none]]
private def node69 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 c c [
    ]
private theorem checked69 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix69) node69 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix69) ⟨4, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix70 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, a, b],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, b],
  [b, b, a, b, none, a, a],
  [a, c, c, c, a, none, b],
  [c, a, c, c, a, c, none]]
private def node70 : NetworkRefutation.Certificate 1 1 :=
  .node 4 6 c c [
    ]
private theorem checked70 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix70) node70 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix70) ⟨4, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix71 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, a, b],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, b],
  [b, b, a, b, none, a, a],
  [a, c, c, c, a, none, c],
  [c, a, c, c, a, b, none]]
private def node71 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 c c [
    ]
private theorem checked71 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix71) node71 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix71) ⟨4, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix72 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, a, b],
  [a, none, c, b, c, b, a],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, a],
  [a, c, c, c, a, none, c],
  [c, a, b, a, a, b, none]]
private def node72 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 c c [
    ]
private theorem checked72 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix72) node72 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix72) ⟨4, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix73 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, a, b],
  [a, none, c, b, c, b, b],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, a],
  [a, c, c, c, a, none, b],
  [c, c, c, a, a, c, none]]
private def node73 : NetworkRefutation.Certificate 1 1 :=
  .node 3 6 c c [
    ]
private theorem checked73 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix73) node73 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix73) ⟨3, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix74 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, a, b],
  [a, none, c, b, c, b, b],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, a],
  [a, c, c, c, a, none, c],
  [c, c, c, a, a, b, none]]
private def node74 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 c c [
    ]
private theorem checked74 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix74) node74 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix74) ⟨4, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix75 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, a, b],
  [a, none, c, b, c, b, b],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, b],
  [b, b, a, b, none, a, a],
  [a, c, c, c, a, none, b],
  [c, c, c, c, a, c, none]]
private def node75 : NetworkRefutation.Certificate 1 1 :=
  .node 4 6 c c [
    ]
private theorem checked75 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix75) node75 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix75) ⟨4, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix76 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, a, b],
  [a, none, c, b, c, b, b],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, b],
  [b, b, a, b, none, a, a],
  [a, c, c, c, a, none, c],
  [c, c, c, c, a, b, none]]
private def node76 : NetworkRefutation.Certificate 1 1 :=
  .node 4 6 c c [
    ]
private theorem checked76 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix76) node76 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix76) ⟨4, by decide⟩ ⟨6, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix77 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, a, b],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, a],
  [a, c, c, c, a, none, c],
  [c, b, c, a, a, b, none]]
private def node77 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 c c [
    ]
private theorem checked77 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix77) node77 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix77) ⟨4, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix78 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, a, b],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, a],
  [a, c, c, c, a, none, c],
  [c, b, b, a, a, b, none]]
private def node78 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 c c [
    ]
private theorem checked78 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix78) node78 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix78) ⟨4, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix79 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, a],
  [a, none, c, b, c, b],
  [a, b, none, b, a, b],
  [b, c, c, none, c, b],
  [b, b, a, b, none, a],
  [a, c, c, c, a, none]]
private def node79 : NetworkRefutation.Certificate 1 1 :=
  .node 0 4 b a [
    .cache matrix68 node68,
    .cache matrix69 node69,
    .cache matrix70 node70,
    .cache matrix71 node71,
    .cache matrix72 node72,
    .cache matrix73 node73,
    .cache matrix74 node74,
    .cache matrix75 node75,
    .cache matrix76 node76,
    .cache matrix77 node77,
    .cache matrix78 node78]
private theorem checked79 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix79) node79 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix79) ⟨0, by decide⟩ ⟨4, by decide⟩ b a = [
        ![db, da, db, da, da, db],
        ![db, da, db, da, da, dc],
        ![db, da, db, db, da, db],
        ![db, da, db, db, da, dc],
        ![db, da, dc, da, da, dc],
        ![db, db, db, da, da, db],
        ![db, db, db, da, da, dc],
        ![db, db, db, db, da, db],
        ![db, db, db, db, da, dc],
        ![db, dc, db, da, da, dc],
        ![db, dc, dc, da, da, dc]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked68, checked69, checked70, checked71, checked72, checked73, checked74, checked75,
    checked76, checked77, checked78]
  decide +kernel
private def matrix80 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, a],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, b],
  [c, a, c, c, a, none, a],
  [a, b, b, a, c, a, none]]
private def node80 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 c c [
    ]
private theorem checked80 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix80) node80 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix80) ⟨4, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix81 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, a],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, c],
  [c, a, c, c, a, none, a],
  [a, b, b, a, b, a, none]]
private def node81 : NetworkRefutation.Certificate 1 1 :=
  .node 3 6 b b [
    ]
private theorem checked81 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix81) node81 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix81) ⟨3, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix82 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, a],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, c],
  [b, b, a, b, none, a, b],
  [c, a, c, c, a, none, a],
  [a, b, b, b, c, a, none]]
private def node82 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 c c [
    ]
private theorem checked82 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix82) node82 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix82) ⟨4, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix83 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, a],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, c],
  [b, b, a, b, none, a, c],
  [c, a, c, c, a, none, a],
  [a, b, b, b, b, a, none]]
private def node83 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked83 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix83) node83 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix83) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix84 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, b],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, b],
  [c, a, c, c, a, none, a],
  [c, b, b, a, c, a, none]]
private def node84 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 c c [
    ]
private theorem checked84 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix84) node84 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix84) ⟨4, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix85 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, c],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, b],
  [c, a, c, c, a, none, a],
  [b, b, b, a, c, a, none]]
private def node85 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 c c [
    ]
private theorem checked85 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix85) node85 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix85) ⟨4, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix86 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, c],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, c],
  [c, a, c, c, a, none, a],
  [b, b, b, a, b, a, none]]
private def node86 : NetworkRefutation.Certificate 1 1 :=
  .node 3 6 b b [
    ]
private theorem checked86 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix86) node86 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix86) ⟨3, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix87 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, c],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, c],
  [b, b, a, b, none, a, b],
  [c, a, c, c, a, none, a],
  [b, b, b, b, c, a, none]]
private def node87 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked87 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix87) node87 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix87) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix88 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b, c],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, c],
  [b, b, a, b, none, a, c],
  [c, a, c, c, a, none, a],
  [b, b, b, b, b, a, none]]
private def node88 : NetworkRefutation.Certificate 1 1 :=
  .node 5 6 b b [
    ]
private theorem checked88 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix88) node88 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨5, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix88) ⟨5, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix89 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b],
  [a, none, c, b, c, a],
  [a, b, none, b, a, b],
  [b, c, c, none, c, b],
  [b, b, a, b, none, a],
  [c, a, c, c, a, none]]
private def node89 : NetworkRefutation.Certificate 1 1 :=
  .node 2 5 c a [
    .cache matrix80 node80,
    .cache matrix81 node81,
    .cache matrix82 node82,
    .cache matrix83 node83,
    .cache matrix84 node84,
    .cache matrix85 node85,
    .cache matrix86 node86,
    .cache matrix87 node87,
    .cache matrix88 node88]
private theorem checked89 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix89) node89 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨2, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix89) ⟨2, by decide⟩ ⟨5, by decide⟩ c a = [
        ![da, dc, dc, da, db, da],
        ![da, dc, dc, da, dc, da],
        ![da, dc, dc, dc, db, da],
        ![da, dc, dc, dc, dc, da],
        ![db, dc, dc, da, db, da],
        ![dc, dc, dc, da, db, da],
        ![dc, dc, dc, da, dc, da],
        ![dc, dc, dc, dc, db, da],
        ![dc, dc, dc, dc, dc, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked80, checked81, checked82, checked83, checked84, checked85, checked86, checked87,
    checked88]
  decide +kernel
private def matrix90 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, b],
  [a, none, c, b, c, b],
  [a, b, none, b, a, b],
  [b, c, c, none, c, b],
  [b, b, a, b, none, a],
  [c, c, c, c, a, none]]
private def node90 : NetworkRefutation.Certificate 1 1 :=
  .node 4 5 c c [
    ]
private theorem checked90 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix90) node90 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨4, by decide⟩ ⟨5, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix90) ⟨4, by decide⟩ ⟨5, by decide⟩ c c = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix91 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, c],
  [b, a, c, c, a, none, a],
  [a, b, c, a, b, a, none]]
private def node91 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    ]
private theorem checked91 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix91) node91 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix91) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix92 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, c],
  [b, a, c, c, a, none, b],
  [a, b, c, a, b, c, none]]
private def node92 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    ]
private theorem checked92 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix92) node92 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix92) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix93 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, c],
  [b, a, c, c, a, none, c],
  [a, b, c, a, b, b, none]]
private def node93 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    ]
private theorem checked93 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix93) node93 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix93) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix94 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, c],
  [b, b, a, b, none, a, c],
  [b, a, c, c, a, none, a],
  [a, b, c, b, b, a, none]]
private def node94 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    ]
private theorem checked94 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix94) node94 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix94) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix95 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, c],
  [b, b, a, b, none, a, c],
  [b, a, c, c, a, none, c],
  [a, b, c, b, b, b, none]]
private def node95 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked95 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix95) node95 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix95) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix96 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, c],
  [b, a, c, c, a, none, a],
  [a, b, b, a, b, a, none]]
private def node96 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked96 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix96) node96 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix96) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix97 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, c],
  [b, a, c, c, a, none, c],
  [a, b, b, a, b, b, none]]
private def node97 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked97 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix97) node97 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix97) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix98 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, c],
  [b, b, a, b, none, a, c],
  [b, a, c, c, a, none, a],
  [a, b, b, b, b, a, none]]
private def node98 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked98 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix98) node98 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix98) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix99 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, a, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, c],
  [b, b, a, b, none, a, c],
  [b, a, c, c, a, none, c],
  [a, b, b, b, b, b, none]]
private def node99 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked99 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix99) node99 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix99) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix100 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c],
  [a, none, c, b, c, a],
  [a, b, none, b, a, b],
  [b, c, c, none, c, b],
  [b, b, a, b, none, a],
  [b, a, c, c, a, none]]
private def node100 : NetworkRefutation.Certificate 1 1 :=
  .node 0 4 a b [
    .cache matrix91 node91,
    .cache matrix92 node92,
    .cache matrix93 node93,
    .cache matrix94 node94,
    .cache matrix95 node95,
    .cache matrix96 node96,
    .cache matrix97 node97,
    .cache matrix98 node98,
    .cache matrix99 node99]
private theorem checked100 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix100)
      node100 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix100) ⟨0, by decide⟩ ⟨4, by decide⟩ a b = [
        ![da, dc, db, da, dc, da],
        ![da, dc, db, da, dc, db],
        ![da, dc, db, da, dc, dc],
        ![da, dc, db, dc, dc, da],
        ![da, dc, db, dc, dc, dc],
        ![da, dc, dc, da, dc, da],
        ![da, dc, dc, da, dc, dc],
        ![da, dc, dc, dc, dc, da],
        ![da, dc, dc, dc, dc, dc]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked91, checked92, checked93, checked94, checked95, checked96, checked97, checked98,
    checked99]
  decide +kernel
private def matrix101 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, c],
  [b, c, c, c, a, none, a],
  [a, b, c, a, b, a, none]]
private def node101 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    ]
private theorem checked101 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix101)
      node101 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix101) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix102 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, c],
  [b, c, c, c, a, none, c],
  [a, b, c, a, b, b, none]]
private def node102 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    ]
private theorem checked102 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix102)
      node102 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix102) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix103 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, c],
  [b, b, a, b, none, a, c],
  [b, c, c, c, a, none, a],
  [a, b, c, b, b, a, none]]
private def node103 : NetworkRefutation.Certificate 1 1 :=
  .node 0 2 b b [
    ]
private theorem checked103 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix103)
      node103 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix103) ⟨0, by decide⟩ ⟨2, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix104 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, b, b],
  [b, c, c, none, c, b, c],
  [b, b, a, b, none, a, c],
  [b, c, c, c, a, none, c],
  [a, b, c, b, b, b, none]]
private def node104 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked104 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix104)
      node104 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix104) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix105 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, c],
  [b, c, c, c, a, none, a],
  [a, b, b, a, b, a, none]]
private def node105 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked105 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix105)
      node105 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix105) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix106 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, a],
  [b, b, a, b, none, a, c],
  [b, c, c, c, a, none, c],
  [a, b, b, a, b, b, none]]
private def node106 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked106 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix106)
      node106 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix106) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix107 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, c],
  [b, b, a, b, none, a, c],
  [b, c, c, c, a, none, a],
  [a, b, b, b, b, a, none]]
private def node107 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked107 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix107)
      node107 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix107) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix108 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c, a],
  [a, none, c, b, c, b, c],
  [a, b, none, b, a, b, c],
  [b, c, c, none, c, b, c],
  [b, b, a, b, none, a, c],
  [b, c, c, c, a, none, c],
  [a, b, b, b, b, b, none]]
private def node108 : NetworkRefutation.Certificate 1 1 :=
  .node 0 6 b b [
    ]
private theorem checked108 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 7) matrix108)
      node108 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨6, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 7) matrix108) ⟨0, by decide⟩ ⟨6, by decide⟩ b b = [] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  rfl
private def matrix109 : List (List (Atom 1 1)) := [
  [none, a, a, c, c, c],
  [a, none, c, b, c, b],
  [a, b, none, b, a, b],
  [b, c, c, none, c, b],
  [b, b, a, b, none, a],
  [b, c, c, c, a, none]]
private def node109 : NetworkRefutation.Certificate 1 1 :=
  .node 0 4 a b [
    .cache matrix101 node101,
    .cache matrix102 node102,
    .cache matrix103 node103,
    .cache matrix104 node104,
    .cache matrix105 node105,
    .cache matrix106 node106,
    .cache matrix107 node107,
    .cache matrix108 node108]
private theorem checked109 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 6) matrix109)
      node109 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 6) matrix109) ⟨0, by decide⟩ ⟨4, by decide⟩ a b = [
        ![da, dc, db, da, dc, da],
        ![da, dc, db, da, dc, dc],
        ![da, dc, db, dc, dc, da],
        ![da, dc, db, dc, dc, dc],
        ![da, dc, dc, da, dc, da],
        ![da, dc, dc, da, dc, dc],
        ![da, dc, dc, dc, dc, da],
        ![da, dc, dc, dc, dc, dc]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked101, checked102, checked103, checked104, checked105, checked106, checked107, checked108]
  decide +kernel
private def matrix110 : List (List (Atom 1 1)) := [
  [none, a, a, c, c],
  [a, none, c, b, c],
  [a, b, none, b, a],
  [b, c, c, none, c],
  [b, b, a, b, none]]
private def node110 : NetworkRefutation.Certificate 1 1 :=
  .node 3 4 b a [
    .cache matrix79 node79,
    .cache matrix89 node89,
    .cache matrix90 node90,
    .cache matrix100 node100,
    .cache matrix109 node109]
private theorem checked110 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 5) matrix110)
      node110 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨3, by decide⟩ ⟨4, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 5) matrix110) ⟨3, by decide⟩ ⟨4, by decide⟩ b a = [
        ![da, db, db, db, da],
        ![db, da, db, db, da],
        ![db, db, db, db, da],
        ![dc, da, db, db, da],
        ![dc, db, db, db, da]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked79, checked89, checked90, checked100, checked109]
  decide +kernel
private def matrix111 : List (List (Atom 1 1)) := [
  [none, a, a, c],
  [a, none, c, b],
  [a, b, none, b],
  [b, c, c, none]]
private def node111 : NetworkRefutation.Certificate 1 1 :=
  .node 1 2 c a [
    .cache matrix57 node57,
    .cache matrix67 node67,
    .cache matrix110 node110]
private theorem checked111 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 4) matrix111)
      node111 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨1, by decide⟩ ⟨2, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 4) matrix111) ⟨1, by decide⟩ ⟨2, by decide⟩ c a = [
        ![db, dc, da, da],
        ![dc, dc, da, da],
        ![dc, dc, da, dc]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked57, checked67, checked110]
  decide +kernel
private def matrix112 : List (List (Atom 1 1)) := [
  [none, a, a],
  [a, none, c],
  [a, b, none]]
private def node112 : NetworkRefutation.Certificate 1 1 :=
  .node 0 1 c c [
    .cache matrix28 node28,
    .cache matrix111 node111]
private theorem checked112 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 3) matrix112)
      node112 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨1, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 3) matrix112) ⟨0, by decide⟩ ⟨1, by decide⟩ c c = [
        ![dc, db, da],
        ![dc, db, db]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked28, checked111]
  decide +kernel
private def matrix113 : List (List (Atom 1 1)) := [
  [none, a],
  [a, none]]
private def node113 : NetworkRefutation.Certificate 1 1 :=
  .node 0 1 a b [
    .cache matrix112 node112]
private theorem checked113 :
    NetworkRefutation.check table (NetworkRefutation.ofMatrix (n := 2) matrix113)
      node113 = true := by
  apply NetworkRefutation.check_node_of table _ ⟨0, by decide⟩ ⟨1, by decide⟩ _ _ _
    (by decide +kernel)
  have hrows : NetworkRefutation.extensions table
      (NetworkRefutation.ofMatrix (n := 2) matrix113) ⟨0, by decide⟩ ⟨1, by decide⟩ a b = [
        ![da, dc]] := by
    rw [NetworkRefutation.extensions_eq_of_encodes
      (tableCode_eq ▸ encodesTable_tableCode cycles)]
    decide +kernel
  rw [hrows]
  simp only [NetworkRefutation.checkChildren, NetworkRefutation.check_cache,
    checked112]
  decide +kernel
/-- A finite tree of impossible composition-witness extensions. -/
private def obstruction : NetworkRefutation.Certificate 1 1 := by exact node113
/-- This catalogue algebra has no representation by binary relations. -/
theorem not_representable : ¬ Representable Algebra := by
  apply NetworkRefutation.not_representable table (some (.inl 0)) obstruction
  have hi : NetworkRefutation.initial (some (.inl 0)) =
      NetworkRefutation.ofMatrix (n := 2) matrix113 := by decide +kernel
  rw [hi]
  exact checked113
end Cslib.RelationAlgebra.Catalogue.I1S1N1.Ra34
