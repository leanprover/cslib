/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai
-/
import Mathlib.Data.Sym.Sym2
import Cslib.Foundations.Semantics.LTS.Basic

@[expose] public section

/-!
# Graph structures

This file introduces graph-like combinatorial structures on a vertex
type `α`. We follow `Graph` definition in Mathlib: The main principle is to define a vertex set
as a `Set α` (see https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Graph/Basic.html#Graph for the rationale behind the design).
Since Mathlib already defined a simple multi graph, we define the other three combinations here:
`SimpleGraph`, `SimpleDiGraph` and `DiGraph`. `SimpleGraph` and `SimpleDiGraph` carry
their adjacency relation directly and disallow loops and multi-edges. `DiGraph` reuses `Cslib.LTS`
to additionally support edge labels, and hence parallel edges.
Both `SimpleGraph` and `SimpleDiGraph` follow `Graph` definitions in Mathlib.

## Main definitions

* `SimpleGraph α`: an undirected graph with adjacency `Adj : α → α → Prop`, no loops or
  multi-edges.
* `SimpleDiGraph α`: a directed graph with adjacency `Adj : α → α → Prop`, no loops or
  multi-edges.
* `DiGraph α β`: a directed graph built from `Cslib.LTS α β`, with edge labels in `β`.
  Parallel edges and loops are permitted.

## Main API

* `SimpleGraph.edgeSet`, `SimpleDiGraph.edgeSet`, `DiGraph.edgeSet`: the edge set of a
  graph, derived from its adjacency/transition relation.
-/

namespace Cslib.Algorithms.Lean.Graph

/-- An undirected graph on `α` with adjacency relation `Adj`, containing no loops or
multi-edges. Both endpoints of every adjacent pair lie in `vertexSet`. -/
structure SimpleGraph (α : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The adjacency relation. `Adj x y` means `x` and `y` are joined by an edge. -/
  Adj : α → α → Prop
  /-- Adjacency is symmetric: if `x` is adjacent to `y`, then `y` is adjacent to `x`. -/
  symm : Std.Symm Adj := by grind
  /-- No vertex is adjacent to itself. -/
  loopless : Std.Irrefl Adj := by grind
  /-- The left endpoint of every adjacent pair is a vertex. -/
  incidence_left : ∀ ⦃x y⦄, Adj x y → x ∈ vertexSet := by grind

/-- The edge set of a `SimpleGraph`, as unordered pairs of adjacent vertices. -/
def SimpleGraph.edgeSet {α} (G : SimpleGraph α) : Set (Sym2 α) :=
  Sym2.fromRel (G.symm)

lemma SimpleGraph.Adj.symm {G : SimpleGraph α} {x y : α} (h : G.Adj x y) : G.Adj y x :=
  G.symm.symm x y h

lemma SimpleGraph.incidence {G : SimpleGraph α} ⦃x y : α⦄ (h : G.Adj x y) :
    x ∈ G.vertexSet ∧ y ∈ G.vertexSet :=
  ⟨G.incidence_left h, G.incidence_left h.symm⟩

/-- A directed graph on `α` with adjacency relation `Adj`, containing no loops or
multi-edges. Both endpoints of every adjacent pair lie in `vertexSet`. -/
structure SimpleDiGraph (α : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The adjacency relation. `Adj x y` means there is an arc from `x` to `y`. -/
  Adj : α → α → Prop
  /-- No vertex is adjacent to itself. -/
  loopless : Std.Irrefl Adj := by grind
  /-- Both endpoints of every adjacent pair are vertices. -/
  incidence : ∀ ⦃x y⦄, Adj x y → x ∈ vertexSet ∧ y ∈ vertexSet := by grind

/-- The edge set of a `SimpleDiGraph`, as ordered pairs of adjacent vertices. -/
def SimpleDiGraph.edgeSet {α} (G : SimpleDiGraph α) : Set (α × α) :=
  { (x,y) | G.Adj x y}

/-- A directed graph on vertex type `α` with edge labels in `β`, built from `Cslib.LTS`.
Parallel edges (distinguished by label) and loops are permitted, and both the vertex and
edge sets may be infinite. -/
structure DiGraph (α β : Type*) extends Cslib.LTS α β where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- Both endpoints of every transition are vertices. -/
  incidence : ∀ ⦃x l y⦄, Tr x l y → x ∈ vertexSet ∧ y ∈ vertexSet := by grind

/-- The edge set of a `DiGraph`, as labelled ordered triples `(source, label, target)`. -/
def DiGraph.edgeSet {α β} (G : DiGraph α β) : Set (α × β × α) :=
  {(x, l, y) | G.Tr x l y}

end Cslib.Algorithms.Lean.Graph
