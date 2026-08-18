/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Graph structures

Vertex and edge sets are `Set`-valued, following the design of
`Mathlib.Combinatorics.Graph`: a subgraph of `G : Graph V E` is another term of
`Graph V E` rather than a separate type, so no coercion maps are needed.

Four structures are provided, in two pairs. `Graph` and `Digraph` are multigraphs whose
edges carry labels in `E`, so parallel edges and loops are permitted. `SimpleGraph` and
`SimpleDigraph` have `Prop`-valued adjacency and therefore disallowing parallel edges.

## Main definitions

We use the following definition of a multigraph.
A multigraph is a triple (V,E,f) where V is a vertex set, E is an edge set,
and f is a function from an edge to an (ordered/unordered) pair of vertices.
In particular, f is a computable function. We reuse the definitions from Mathlib as much as we can.

* `MultiGraph V E`: an undirected multigraph (abbrev for Mathlib's `Graph V E`).
* `MultiDigraph V E`: a directed multigraph; the directed counterpart of Mathlib's `Graph V E`.
* `SimpleGraph V`: a simple graph with a vertex set, extending Mathlib's `SimpleGraph V`.
* `SimpleDigraph V`: a loopless directed graph with adjacency `Adj : V → V → Prop` and a
  vertex set, extending Mathlib's `Digraph V`.

## Main API

* `Graph.endpoints`, `Digraph.endpoints`: the ends of an edge or arc.
* `SimpleDigraph.arcSet`: the arc set of a `SimpleDigraph`, derived from its adjacency
  relation. The corresponding `SimpleGraph.edgeSet` is inherited from Mathlib rather than
  redefined here.

## Implementation notes

`IsLink` and `IsArc` are `Prop`-valued, so nothing about them is executable. To recover
computation, `Graph` and `Digraph` each carry an `endpoints : E → Option _` field together
with `endpoints_spec`. That specification pins the value of `endpoints` at *every* label —
`some` on the edge set, and `none` off it, since every `s : Sym2 V` is of the form
`s(x, y)`.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

/-- An undirected multigraph on vertex type `V` with edge labels in `E`.

This is Mathlib's `Graph V E` — so parallel edges and loops are permitted, and both the
vertex and edge sets may be infinite. -/
abbrev MultiGraph (V E : Type*) :=  _root_.Graph V E

/-- A computable map from an edge label of `G` to its ends. -/
class MultiGraph.HasEndpoints {V E : Type*} (G : MultiGraph V E) where
  /-- The ends of the edge labelled `e`, or `none` if `e` is not an edge of `G`. -/
  endpoints : E → Option (Sym2 V)
  /-- `endpoints` computes `Graph.IsLink`. -/
  endpoints_spec : ∀ e x y, G.IsLink e x y ↔ s(x, y) ∈ endpoints e

/-- The ends of `e` in `G`, or `none` if `e ∉ E(G)`. -/
def MultiGraph.endpoints? (G : MultiGraph V E) [inst : G.HasEndpoints] (e : E) : Option (Sym2 V) :=
  inst.endpoints e

theorem isLink_iff_endpoints (G : MultiGraph V E) [G.HasEndpoints] :
  G.IsLink e x y ↔ s(x, y) ∈ G.endpoints? e :=
  MultiGraph.HasEndpoints.endpoints_spec e x y

/-- A directed multigraph on vertex type `V` with arc labels in `E`, bundled with a
computable map from an arc label to its endpoints.

The directed counterpart of Mathlib's `Graph V E`, which has no Mathlib counterpart to
extend; the field layout mirrors it, with symmetry dropped. -/
structure MultiDigraph (V E : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set V
  /-- The incidence predicate: `IsArc e x y` states that the arc labelled `e` runs from
  `x` to `y`. -/
  IsArc : E → V → V → Prop
  /-- The ends of the edge labelled `e`, or `none` if `e` is not an edge of `G`. -/
  endpoints : E → Option (V × V)
  /-- `endpoints` computes `Graph.IsLink`. -/
  endpoints_spec : ∀ e x y, IsArc e x y ↔ (x, y) ∈ endpoints e
  /-- Both ends of every arc are vertices. `IsArc` is not symmetric, so neither direction
  follows from the other. -/
  incidence : ∀ ⦃e x y⦄, IsArc e x y → (x ∈ vertexSet ∧ y ∈ vertexSet) := by grind
  /-- The set of arc labels. -/
  arcSet : Set E := { e | ∃ x y, IsArc e x y}
  /-- A label lies in `arcSet` exactly when it is used by some arc. -/
  arc_mem_iff_exists_isArc (e) : e ∈ arcSet ↔ ∃ x y, IsArc e x y := by exact fun _ ↦ Iff.rfl

/-- A simple graph on `V` — irreflexive and symmetric adjacency, hence no loops and no
parallel edges — together with a vertex set containing every end of an adjacent pair.

Extends Mathlib's `SimpleGraph V`, so its API is available through `toSimpleGraph`; in
particular `edgeSet`, the unordered pairs of adjacent vertices, is inherited rather than
redefined. Note that `Adj` is a relation on all of `V`, so `vertexSet` may be any superset
of the vertices actually incident to an edge. -/
structure SimpleGraph (V : Type*) extends _root_.SimpleGraph V where
  /-- The set of vertices. -/
  vertexSet : Set V
  /-- The left end of every adjacent pair is a vertex. The right end then follows by
  symmetry of `Adj`. -/
  adj_imp_left_mem_vertexSet : ∀ ⦃x y⦄, Adj x y → x ∈ vertexSet := by grind

/-- A simple directed graph on `V` — adjacency `Adj : V → V → Prop`, hence no parallel
arcs — with loops explicitly excluded, together with a vertex set containing every end of
an adjacent pair.

Extends Mathlib's `Digraph V`, which is a bare adjacency relation and does permit loops;
`loopless` is what rules them out here. Antiparallel arcs are permitted: `Adj x y` and
`Adj y x` may both hold. -/
structure SimpleDigraph (V : Type*) extends _root_.Digraph V where
  /-- The set of vertices. -/
  vertexSet : Set V
  /-- No vertex is adjacent to itself. -/
  irrefl_adj : Std.Irrefl Adj
  /-- Both ends of every adjacent pair are vertices. Unlike `SimpleGraph`, `Adj` is not
  symmetric, so neither direction follows from the other. -/
  incidence : ∀ ⦃x y⦄, Adj x y → x ∈ vertexSet ∧ y ∈ vertexSet := by grind

/-- The edge set of a `SimpleDigraph`, as ordered pairs of adjacent vertices. -/
def SimpleDigraph.edgeSet (G : SimpleDigraph V) : Set (V × V) :=
  {p | G.Adj p.1 p.2}


end Cslib.Algorithms.Lean
