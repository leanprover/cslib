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
public import Mathlib.Data.PFun


/-!
# Graph structures

Vertex and edge sets are `Set`-valued, following the design of
`Mathlib.Combinatorics.Graph`: a subgraph of `G : Graph V E` is another term of
`Graph V E` rather than a separate type, so no coercion maps are needed.

Four structures are provided, in two pairs. `MultiGraph` and `MultiDigraph` are multigraphs whose
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

* `MultiGraph.endpoints`, `MultiDigraph.endpoints`: the ends of an edge.
* `SimpleDigraph.edgeSet`: the edge set of a `SimpleDigraph`, derived from its adjacency
  relation. The corresponding `SimpleGraph.edgeSet` is inherited from Mathlib rather than
  redefined here.

## Implementation notes

`IsLink` are `Prop`-valued, so nothing about them is executable. To recover
computation, `MultiGraph` and `Digraph` each carry an `endpoints : E →. _` field together
with `endpoints_spec`. That specification pins the value of `endpoints` at *every* label —
`some` on the edge set, and `none` otherwise.

-/

@[expose] public section

namespace Cslib.Algorithms.Lean

/-- An undirected multigraph on vertex type `V` with edge labels in `E`.

This is Mathlib's `Graph V E` — so parallel edges and loops are permitted, and both the
vertex and edge sets may be infinite. -/
abbrev MultiGraph (V E : Type*) :=  _root_.Graph V E

/-- A map from an edge label of `G` to its ends. -/
class MultiGraph.HasEndpoints {V E : Type*} (G : MultiGraph V E) where
  /-- The ends of the edge labelled `e`, or `none` if `e` is not an edge of `G`. -/
  endpoints : E →. (Sym2 V)
  /-- `endpoints` computes `Graph.IsLink`. -/
  endpoints_spec : ∀ e x y, G.IsLink e x y ↔ s(x, y) ∈ endpoints e

/-- The ends of `e` in `G`; undefined when `e ∉ E(G)`. -/
def MultiGraph.endpoints (G : MultiGraph V E) [inst : G.HasEndpoints] : E →. Sym2 V :=
  inst.endpoints

theorem isLink_iff_endpoints (G : MultiGraph V E) [G.HasEndpoints] :
  G.IsLink e x y ↔ s(x, y) ∈ G.endpoints e :=
  MultiGraph.HasEndpoints.endpoints_spec e x y

/-- A directed multigraph on vertex type `V` with edge labels in `E`, given by a partial
function from an edge label to its ends. -/
structure MultiDigraph (V E : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set V
  /-- The ends of the edge labelled `e`; undefined when `e` is not an edge of `G`. -/
  endpoints : E →. (V × V)
  /-- The tail of every edge is a vertex. -/
  endpoints_left_mem_vertexSet ⦃e x y⦄ : (x, y) ∈ endpoints e → x ∈ vertexSet := by grind
  /-- The head of every edge is a vertex. -/
  endpoints_right_mem_vertexSet ⦃e x y⦄ : (x, y) ∈ endpoints e → y ∈ vertexSet := by grind

namespace MultiDigraph
variable {V E : Type*} {G : MultiDigraph V E} {e : E} {x y x' y' : V}

/-- The set of edge labels. -/
def edgeSet (G : MultiDigraph V E) : Set E := G.endpoints.Dom

/-- `IsLink e x y` states that the edge labelled `e` runs from `x` to `y`. -/
def IsLink (G : MultiDigraph V E) (e : E) (x y : V) : Prop := (x, y) ∈ G.endpoints e

@[simp] lemma isLink_iff : G.IsLink e x y ↔ (x, y) ∈ G.endpoints e := Iff.rfl
@[simp] lemma mem_edgeSet_iff : e ∈ G.edgeSet ↔ (G.endpoints e).Dom := Iff.rfl

lemma mem_edgeSet_iff_exists_isLink : e ∈ G.edgeSet ↔ ∃ x y, G.IsLink e x y := by
  rw [mem_edgeSet_iff, Part.dom_iff_mem]
  exact ⟨fun ⟨p, hp⟩ => ⟨p.1, p.2, hp⟩, fun ⟨_, _, h⟩ => ⟨_, h⟩⟩

lemma IsLink.mem_edgeSet (h : G.IsLink e x y) : e ∈ G.edgeSet :=
  mem_edgeSet_iff_exists_isLink.2 ⟨x, y, h⟩

/-- An edge is incident with at most one ordered pair of vertices. -/
lemma eq_and_eq_of_isLink_of_isLink (h : G.IsLink e x y) (h' : G.IsLink e x' y') :
    x = x' ∧ y = y' :=
  have hp : (x, y) = (x', y') := Part.mem_unique h h'
  ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

end MultiDigraph


/-- A simple graph on `V` — irreflexive and symmetric adjacency, hence no loops and no
parallel edges — together with a vertex set containing every end of an adjacent pair.

Extends Mathlib's `SimpleGraph V`, so its API is available through `toSimpleGraph`; in
particular `edgeSet`, the unordered pairs of adjacent vertices, is inherited rather than
redefined. -/
structure SimpleGraph (V : Type*) extends _root_.SimpleGraph V where
  /-- The set of vertices. -/
  vertexSet : Set V
  /-- The left end of every adjacent pair is a vertex. The right end then follows by
  symmetry of `Adj`. -/
  adj_imp_left_mem_vertexSet : ∀ ⦃x y⦄, Adj x y → x ∈ vertexSet := by grind

/-- A simple directed graph on `V` — adjacency `Adj : V → V → Prop`, hence no parallel
edges — with loops explicitly excluded, together with a vertex set containing every end of
an adjacent pair.

Extends Mathlib's `Digraph V`, which is a bare adjacency relation and does permit loops;
`loopless` is what rules them out here. -/
structure SimpleDigraph (V : Type*) extends _root_.Digraph V where
  /-- The set of vertices. -/
  vertexSet : Set V
  /-- No vertex is adjacent to itself. -/
  irrefl_adj : Std.Irrefl Adj
  /-- Both ends of every adjacent pair are vertices. Unlike `SimpleGraph`, `Adj` is not
  symmetric, so neither direction follows from the other. -/
  adj_imp_left_mem_vertexSet : ∀ ⦃x y⦄, Adj x y → x ∈ vertexSet := by grind
  adj_imp_right_mem_vertexSet : ∀ ⦃x y⦄, Adj x y → y ∈ vertexSet := by grind

/-- The edge set of a `SimpleDigraph`, as ordered pairs of adjacent vertices. -/
def SimpleDigraph.edgeSet (G : SimpleDigraph V) : Set (V × V) :=
  {p | G.Adj p.1 p.2}


end Cslib.Algorithms.Lean
