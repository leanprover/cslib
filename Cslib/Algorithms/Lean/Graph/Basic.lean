/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Fabrizio Montesi, Sorrachai Yingchareonthawornchai
-/

import Cslib.Foundations.Semantics.LTS.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.Graph.Basic

@[expose] public section

/-!
# Graph structures

This file follows the `Set`-based vertex/edge design of `Mathlib.Combinatorics.Graph`: a
vertex set of type `Set α`, with any relation on `α` or `β` constrained by an incidence
relation. `Graph` is Mathlib's `Graph` directly. `SimpleGraph` extends Mathlib's
`SimpleGraph`, adding a vertex subset in the same style. `SimpleDiGraph` has no Mathlib
counterpart to extend and is built from scratch. `DiGraph` reuses `Cslib.LTS` for its
transition relation and adds the same vertex-subset layer.

## Main definitions

* `Graph α β`: an undirected multi-graph as a Mathlib's graph.
* `SimpleGraph α`: an undirected graph with adjacency `Adj : α → α → Prop`, no loops or
  multi-edges.
* `DiGraph α β`: a directed graph built from `Cslib.LTS α β`, with edge labels in `β`.
  Parallel edges and loops are permitted.
* `SimpleDiGraph α`: a directed graph with adjacency `Adj : α → α → Prop`, no loops or
  multi-edges.


## Main API

* `SimpleGraph.edgeSet`, `SimpleDiGraph.edgeSet`, `DiGraph.edgeSet`: the edge set of a
  graph, derived from its adjacency/transition relation.
-/

namespace Cslib.Algorithms.Lean

/-- An undirected multigraph on vertex type `α` with edge labels in `β` -/
abbrev Graph (α β : Type*) :=  _root_.Graph α β

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

/-- A directed graph on vertex type `α`  whose edges are identified by labels `β`
  built from `Cslib.LTS`. Parallel edges (distinguished by label) and loops are permitted. -/
structure DiGraph (α β : Type*) extends Cslib.LTS α β where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- Both endpoints of every transition are vertices. -/
  incidence : ∀ ⦃x l y⦄, Tr x l y → x ∈ vertexSet ∧ y ∈ vertexSet := by grind
  /-- Each label is used at most once. -/
  tr_inj : ∀ ⦃x y x' y' : α⦄ ⦃l : β⦄, Tr x l y → Tr x' l y' → x = x' ∧ y = y'

/-- The edge set of a `DiGraph`, as labelled ordered triples `(source, label, target)`. -/
def DiGraph.edgeSet {α β} (G : DiGraph α β) : Set (α × β × α) :=
  {(x, l, y) | G.Tr x l y}

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
