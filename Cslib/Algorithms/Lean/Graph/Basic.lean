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


@[expose] public section

/-!
# Graph structures

Vertex and edge sets are `Set`-valued, following the design of
`Mathlib.Combinatorics.Graph`: a subgraph of `G : Graph α β` is another term of
`Graph α β` rather than a separate type, so no coercion maps are needed.

Four structures are provided, in two pairs. `Graph` and `Digraph` are multigraphs whose
edges carry labels in `β`, so parallel edges and loops are permitted. `SimpleGraph` and
`SimpleDigraph` have `Prop`-valued adjacency and therefore disallowing parallel edges.

## Main definitions

We use the following definition of a multigraph.
A multigraph is a triple (V,E,f) where V is a vertex set, E is an edge set,
and f is a function from an edge to an (ordered/unordered) pair of vertices.
In particular, f is a computable function. We reuse the definitions from Mathlib as much as we can.

* `Graph α β`: an undirected multigraph, extending Mathlib's `Graph α β`.
* `Digraph α β`: a directed multigraph; the directed counterpart of Mathlib's `Graph α β`.
* `SimpleGraph α`: a simple graph with a vertex set, extending Mathlib's `SimpleGraph α`.
* `SimpleDigraph α`: a loopless directed graph with adjacency `Adj : α → α → Prop` and a
  vertex set, extending Mathlib's `Digraph α`.


## Main API

* `Graph.endpoints`, `Digraph.endpoints`: the ends of an edge or arc.
* `SimpleDigraph.arcSet`: the arc set of a `SimpleDigraph`, derived from its adjacency
  relation. The corresponding `SimpleGraph.edgeSet` is inherited from Mathlib rather than
  redefined here.

## Implementation notes

`IsLink` and `IsArc` are `Prop`-valued, so nothing about them is executable. To recover
computation, `Graph` and `Digraph` each carry an `endpoints : β → Option _` field together
with `endpoints_spec`. That specification pins the value of `endpoints` at *every* label —
`some` on the edge set, and `none` off it, since every `s : Sym2 α` is of the form
`s(x, y)`.

-/

namespace Cslib.Algorithms.Lean


/-- An undirected multigraph on vertex type `α` with edge labels in `β`, bundled with a
computable map from an edge label to its ends.

This is Mathlib's `Graph α β` — so parallel edges and loops are permitted, and both the
vertex and edge sets may be infinite — together with the `endpoints` field. That field is
uniquely determined by `toGraph`, so it carries no mathematical content; it exists so that
incidence can be evaluated rather than only reasoned about. -/
structure Graph (α β : Type*) extends _root_.Graph α β where
  /-- The ends of the edge labelled `e`, or `none` if `e` is not an edge of the graph. -/
  endpoints : β → Option (Sym2 α)
  /-- `endpoints` computes `Graph.IsLink`. This forces `endpoints e = none` for every
  `e ∉ edgeSet`, since every `s : Sym2 α` is of the form `s(x, y)`. -/
  endpoints_spec : ∀ e x y, toGraph.IsLink e x y ↔ endpoints e = some s(x, y)

/-- A directed multigraph on vertex type `α` with arc labels in `β`, bundled with a
computable map from an arc label to its endpoints.

The directed counterpart of Mathlib's `Graph α β`, which has no Mathlib counterpart to
extend; the field layout mirrors it, with symmetry dropped. -/
structure Digraph (α β : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The incidence predicate: `IsArc e x y` states that the arc labelled `e` runs from
  `x` to `y`. -/
  IsArc : β → α → α → Prop
  /-- Both ends of every arc are vertices. `IsArc` is not symmetric, so neither direction
  follows from the other. -/
  incidence  : ∀ ⦃e x y⦄, IsArc e x y → (x ∈ vertexSet ∧ y ∈ vertexSet) := by grind
  /-- The ends of the arc labelled `e`, or `none` if `e` is not an arc of the graph. -/
  endpoints : β → Option (α × α)
  /-- `endpoints` computes `IsArc`. This forces `endpoints e = none` for every
  `e ∉ arcSet`. -/
  endpoints_spec : ∀ e x y, IsArc e x y ↔ endpoints e = some (x, y)
  /-- The set of arc labels. -/
  arcSet : Set β := { e | ∃ x y, IsArc e x y}
  /-- A label lies in `arcSet` exactly when it is used by some arc. -/
  arc_mem_iff_exists_isArc (e) : e ∈ arcSet ↔ ∃ x y, IsArc e x y := by exact fun _ ↦ Iff.rfl

/-- A simple graph on `α` — irreflexive and symmetric adjacency, hence no loops and no
parallel edges — together with a vertex set containing every end of an adjacent pair.

Extends Mathlib's `SimpleGraph α`, so its API is available through `toSimpleGraph`; in
particular `edgeSet`, the unordered pairs of adjacent vertices, is inherited rather than
redefined. Note that `Adj` is a relation on all of `α`, so `vertexSet` may be any superset
of the vertices actually incident to an edge. -/
structure SimpleGraph (α : Type*) extends _root_.SimpleGraph α where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The left end of every adjacent pair is a vertex. The right end then follows by
  symmetry of `Adj`. -/
  left_incidence : ∀ ⦃x y⦄, Adj x y → x ∈ vertexSet := by grind

/-- A simple directed graph on `α` — adjacency `Adj : α → α → Prop`, hence no parallel
arcs — with loops explicitly excluded, together with a vertex set containing every end of
an adjacent pair.

Extends Mathlib's `Digraph α`, which is a bare adjacency relation and does permit loops;
`loopless` is what rules them out here. Antiparallel arcs are permitted: `Adj x y` and
`Adj y x` may both hold. -/
structure SimpleDigraph (α : Type*) extends _root_.Digraph α where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- No vertex is adjacent to itself. -/
  loopless : Std.Irrefl Adj
  /-- Both ends of every adjacent pair are vertices. Unlike `SimpleGraph`, `Adj` is not
  symmetric, so neither direction follows from the other. -/
  incidence : ∀ ⦃x y⦄, Adj x y → x ∈ vertexSet ∧ y ∈ vertexSet := by grind

/-- The arc set of a `SimpleDigraph`, as ordered pairs of adjacent vertices. -/
def SimpleDigraph.arcSet (G : SimpleDigraph α) : Set (α × α) :=
  {p | G.Adj p.1 p.2}


end Cslib.Algorithms.Lean
