/-
Copyright (c) 2026 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai
-/

module
public import Cslib.Init
public import Mathlib.Data.Sym.Sym2

@[expose] public section

/-!
# Simple Undirected Graphs
This file defines simple undirected graphs and basic definitions.

--
## Main definitions
- `Edge`: A type alias for `Sym2 α`, representing an undirected edge as an
  unordered pair.
- `SimpleGraph`: A structure encoding a simple graph with a finite vertex set,
  a finite edge set, an incidence condition (every endpoint of every edge is a
  vertex), and a looplessness condition (no edge is a diagonal of `Sym2`).
- `IncidentEdgeSet`: The set of all edges in a graph that are incident to a
  given vertex.
- `Neighbors`: The set of all vertices adjacent to a given vertex, i.e. the
  open neighbourhood of that vertex.
- `subgraphOf`: A relation asserting that one graph is a subgraph of another;
  both the vertex set and the edge set of the first are subsets of those of the
  second.

## Implementation notes

Edges are represented as elements of `Sym2 α` (i.e., `{x, y}` with `x ≠ y`
enforced via the `loopless` field rather than the type). This mirrors the
approach used in Mathlib's combinatorics library.

The graph definitions in this file intentionally diverge from those in Mathlib;
we prioritise representations that support algorithmic reasoning over those designed for
classical combinatorial arguments.
-/

namespace Cslib.Algorithms.Lean.Graph.Core.Simple

variable {α : Type*} [DecidableEq α]


/-- An undirected edge, represented as an unordered pair via `Sym2`. -/
abbrev Edge := Sym2

/-- A simple graph on vertex type `α` consists of a finite vertex set, a finite
edge set, and two well-formedness conditions: every edge endpoint is a vertex,
and no edge is a self-loop. -/
structure SimpleGraph (α : Type*) where
  /-- The finite set of vertices of the graph. -/
  vertexSet : Finset α
  /-- The finite set of edges of the graph. -/
  edgeSet   : Finset (Edge α)
  /-- Every endpoint of every edge is a vertex. -/
  incidence : ∀ e ∈ edgeSet, ∀ v ∈ e, v ∈ vertexSet
  /-- The graph has no self-loops. -/
  loopless  : ∀ e ∈ edgeSet, ¬ e.IsDiag

open Finset


/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => SimpleGraph.vertexSet G

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => SimpleGraph.edgeSet G

/-- The set of all edges in a graph that are incident to a given vertex. -/
abbrev IncidentEdgeSet (G : SimpleGraph α) (s : α) :
  Finset (Edge α) := {e ∈ E(G) | s ∈ e}

/-- `δ(G,v)` denotes the `edge-incident-set` of a vertex `v` in `G`. -/
scoped notation "δ(" G "," v ")" => SimpleGraph.IncidentEdgeSet G v

/-- The set of all vertices adjacent to a given vertex, i.e. the
  open neighbourhood of that vertex. -/
abbrev Neighbors (G : SimpleGraph α) (s : α) :
  Finset α := {u ∈ V(G) | ∃ e ∈ E(G), s ∈ e ∧ u ∈ e ∧ u ≠ s}

/-- `N(G,v)` denotes the `neighbors` of a vertex `v` in `G`. -/
scoped notation "N(" G "," v ")" => SimpleGraph.Neighbors G v

/-- `deg(G)` denotes the `degree` of a vertex `v` in `G`. -/
scoped notation "deg(" G "," v ")" => #δ(G,v)

/-- A graph `H` is a subgraph of `G` if both vertex and edge sets are subsets of those in G -/
abbrev subgraphOf (H G : SimpleGraph α) : Prop :=
  V(H) ⊆ V(G) ∧ E(H) ⊆ E(G)

/-- Notation for the subgraph relation -/
scoped infix:50 " ⊆ᴳ " => SimpleGraph.subgraphOf

end Cslib.Algorithms.Lean.Graph.Core.Simple
