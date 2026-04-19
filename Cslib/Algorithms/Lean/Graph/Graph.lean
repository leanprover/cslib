/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/

module
public import Cslib.Init
public import Mathlib.Data.Sym.Sym2

@[expose] public section

/-!
# Graph structures

This file introduces a small hierarchy of graph-like combinatorial structures on a vertex
type `α`. Each structure carries its vertex and edge sets explicitly.

## Main definitions

* `Graph α ε`: a general graph with abstract edge index type `ε`; each edge carries an
  unordered pair of endpoints as a `Sym2 α`. Parallel edges and loops are permitted.
* `SimpleGraph α`: a finite simple graph, with edges indexed by `Sym2 α` itself, `Finset`
  vertex and edge sets, and no loops.
* `DiGraph α ε`: a directed graph with abstract edge index type `ε`; each edge carries an
  ordered pair `α × α` of endpoints.
* `SimpleDiGraph α`: a finite simple directed graph with edges as ordered pairs and no
  loops.

## Main forgetful maps

* `SimpleGraph.toGraph`: forget the finiteness and looplessness axioms of a simple graph.
* `SimpleDiGraph.toDiGraph`: forget the finiteness and looplessness axioms of a simple
  directed graph.

The corresponding `Coe` instances are registered.
-/

namespace Cslib.Algorithms.Lean
variable {α ε : Type*}

/-- A general graph on vertex type `α` with edges indexed by `ε`. The edge set is abstract;
endpoints are carried by a separate map. Parallel edges and loops are permitted, and both
the vertex and edge sets may be infinite. -/
structure Graph (α ε : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The set of edges. -/
  edgeSet : Set ε
  /-- The endpoint map, sending each edge to its unordered pair of endpoints. -/
  endpoints : ε → Sym2 α
  /-- Every endpoint of an edge is a vertex. -/
  incidence : ∀ e ∈ edgeSet, ∀ v ∈ endpoints e, v ∈ vertexSet

/-- A finite simple graph on `α`: finite vertex and edge sets, edges as unordered pairs of
distinct vertices. -/
@[grind]
structure SimpleGraph (α : Type*) where
  /-- The finite set of vertices. -/
  vertexSet : Finset α
  /-- The finite set of edges, each an unordered pair of vertices. -/
  edgeSet : Finset (Sym2 α)
  /-- Both endpoints of every edge are vertices. -/
  incidence : ∀ e ∈ edgeSet, ∀ v ∈ e, v ∈ vertexSet
  /-- No edge is a loop. -/
  loopless : ∀ e ∈ edgeSet, ¬ e.IsDiag

/-- A directed graph on vertex type `α` with edges indexed by `ε`. The edge set is abstract;
ordered endpoints are carried by a separate map. Parallel edges and loops are permitted,
and both the vertex and edge sets may be infinite. -/
structure DiGraph (α ε : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The set of edges. -/
  edgeSet : Set ε
  /-- The endpoint map, sending each edge to its ordered pair `(source, target)`. -/
  endpoints : ε → α × α
  /-- Both endpoints of every edge are vertices. -/
  incidence : ∀ e ∈ edgeSet, (endpoints e).1 ∈ vertexSet ∧ (endpoints e).2 ∈ vertexSet

/-- A finite simple directed graph on `α`: finite vertex and edge sets, edges as ordered
pairs of distinct vertices. -/
structure SimpleDiGraph (α : Type*) where
  /-- The finite set of vertices. -/
  vertexSet : Finset α
  /-- The finite set of directed edges. -/
  edgeSet : Finset (α × α)
  /-- Both endpoints of every directed edge are vertices. -/
  incidence : ∀ e ∈ edgeSet, e.1 ∈ vertexSet ∧ e.2 ∈ vertexSet
  /-- No directed edge is a loop. -/
  loopless : ∀ e ∈ edgeSet, e.1 ≠ e.2

/-- Reinterpret a `Graph` as a `Hypergraph` by replacing each `Sym2 α` endpoint pair by
the corresponding two-element set. -/
def Graph.toHypergraph (G : Graph α ε) : Hypergraph α ε where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet
  endpoints e := {v | v ∈ G.endpoints e}
  incidence e he v hv := G.incidence e he v hv

/-- Forget the finiteness and looplessness axioms of a `SimpleGraph`, viewing it as a
`Graph` with edges indexed by `Sym2 α` itself and identity endpoint map. -/
def SimpleGraph.toGraph (G : SimpleGraph α) : Graph α (Sym2 α) where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet
  endpoints := id
  incidence e he v hv := by simpa using G.incidence e (by simpa using he) v hv

/-- Forget the finiteness and looplessness axioms of a `SimpleDiGraph`, viewing it as a
`DiGraph` with edges indexed by `α × α` itself and identity endpoint map. -/
def SimpleDiGraph.toDiGraph (G : SimpleDiGraph α) : DiGraph α (α × α) where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet
  endpoints := id
  incidence e he := by simpa using G.incidence e (by simpa using he)

instance : Coe (SimpleGraph α) (Graph α (Sym2 α)) := ⟨SimpleGraph.toGraph⟩

instance : Coe (SimpleDiGraph α) (DiGraph α (α × α)) := ⟨SimpleDiGraph.toDiGraph⟩


/-- Typeclass for graph-like structures that have a vertex set. -/
class HasVertexSet (G : Type*) (V : outParam Type*) where
  /-- The vertex set of the graph. -/
  vertexSet : G → V

/-- Typeclass for graph-like structures that have an edge set. -/
class HasEdgeSet (G : Type*) (E : outParam Type*) where
  /-- The edge set of the graph. -/
  edgeSet : G → E

@[simp] instance {α ε : Type*} : HasVertexSet (Graph α ε) (Set α) :=
  ⟨Graph.vertexSet⟩

@[simp] instance {α : Type*} : HasVertexSet (SimpleGraph α) (Finset α) :=
  ⟨SimpleGraph.vertexSet⟩

@[simp] instance {α ε : Type*} : HasVertexSet (DiGraph α ε) (Set α) :=
  ⟨DiGraph.vertexSet⟩

@[simp] instance {α : Type*} : HasVertexSet (SimpleDiGraph α) (Finset α) :=
  ⟨SimpleDiGraph.vertexSet⟩

@[simp] instance {α ε : Type*} : HasEdgeSet (Graph α ε) (Set (Sym2 α)) :=
  ⟨fun G => G.edgeSet.image G.endpoints⟩

@[simp] instance {α : Type*} : HasEdgeSet (SimpleGraph α) (Finset (Sym2 α)) :=
  ⟨SimpleGraph.edgeSet⟩

@[simp] instance {α ε : Type*} : HasEdgeSet (DiGraph α ε) (Set (α × α)) :=
  ⟨fun G => G.edgeSet.image G.endpoints⟩

@[simp] instance {α : Type*} : HasEdgeSet (SimpleDiGraph α) (Finset (α × α)) :=
  ⟨SimpleDiGraph.edgeSet⟩

/-- Notation for the vertex set of a graph. -/
scoped notation "V(" G ")" => HasVertexSet.vertexSet G
/-- Notation for the edge set of a graph. -/
scoped notation "E(" G ")" => HasEdgeSet.edgeSet G

end Cslib.Algorithms.Lean
