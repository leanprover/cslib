/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai
-/

import Cslib.Foundations.Semantics.LTS.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.Graph.Basic

@[expose] public section

/-!
# Graph structures

This file follows the `Set`-based vertex/edge design of `Mathlib.Combinatorics.Graph`: a
vertex set of type `Set α`. `SimpleGraph` extends Mathlib's
`SimpleGraph`, adding a vertex subset in the same style. `SimpleDiGraph` has no Mathlib
counterpart to extend and is built from scratch. We proritize computability., and thus
`DiGraph, Graph` require storing `Arc, Edge` structure.

## Main definitions

* `Graph α β`: an undirected multi-graph.
* `DiGraph α β`: a directed graph.
* `SimpleGraph α`: an undirected graph build on top of Mathlib's SimpleGraph.
* `SimpleDiGraph α`: a directed graph with adjacency `Adj : α → α → Prop`, no loops or
  multi-edges.

## Main API

* `SimpleGraph.edgeSet`, `SimpleDiGraph.edgeSet`: the edge set of a
  graph, derived from its adjacency relation.
-/

namespace Cslib.Algorithms.Lean

/-- An undirected edge with a label of type `β` and an unordered pair of endpoints. -/
structure Edge (α β : Type*) where
  /-- The edge label, used to distinguish parallel edges. -/
  endpointsLabel : β
  /-- The unordered pair of endpoints. -/
  endpoints : Sym2 α
deriving DecidableEq

/-- A directed edge with a label of type `β` and an ordered pair of endpoints. -/
structure Arc (α β : Type*) where
  /-- The edge label, used to distinguish parallel edges. -/
  endpointsLabel : β
  /-- The ordered pair `(source, target)` of endpoints. -/
  endpoints : α × α
deriving DecidableEq

/-- A general graph on vertex type `α` with edge labels in `β`. Each edge bundles a label
and an unordered pair of endpoints. Parallel edges and loops are permitted, and both the
vertex and edge sets may be infinite. -/
structure Graph (α β : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The set of edges. -/
  edgeSet : Set (Edge α β)
  /-- Every endpoint of an edge is a vertex. Prefer `Graph.incidence`. -/
  incidence' : ∀ e ∈ edgeSet, ∀ v ∈ e.endpoints, v ∈ vertexSet

/-- A directed graph on vertex type `α` with edge labels in `β`. Each edge bundles a label
and an ordered pair of endpoints. Parallel edges and loops are permitted, and both the
vertex and edge sets may be infinite. -/
structure DiGraph (α β : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The set of edges. -/
  edgeSet : Set (Arc α β)
  /-- Both endpoints of every edge are vertices. Prefer `DiGraph.incidence`. -/
  incidence' : ∀ e ∈ edgeSet, e.endpoints.1 ∈ vertexSet ∧ e.endpoints.2 ∈ vertexSet


/-- An undirected graph on `α` with adjacency relation `Adj`, containing no loops or
multi-edges. Both endpoints of every adjacent pair lie in `vertexSet`. -/
structure SimpleGraph (α : Type*) extends _root_.SimpleGraph α where
  /-- The set of vertices. -/
  vertexSet : Set α
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


end Cslib.Algorithms.Lean
