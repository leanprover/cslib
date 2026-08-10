/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/

module
public import Cslib.Init
public import Mathlib.Data.Sym.Sym2

/-!
# Graph structures

This file introduces a small hierarchy of graph-like combinatorial structures on a vertex
type `α`. Each structure carries its vertex and edge sets explicitly.

## Design rationale

We intentionally diverge from Mathlib's graph definitions (`Mathlib.Combinatorics.Graph.Basic`,
`Mathlib.Combinatorics.SimpleGraph.Basic`),
prioritizing representations that support algorithmic reasoning. In graph algorithm design,
it is common to manipulate graphs dynamically (adding or removing nodes/edges, contracting
edges, etc.). We therefore use set-based definitions for both vertex and edge sets with
minimal additional axioms, reducing early proof obligations and keeping proofs closer to
their textbook counterparts.

## Main definitions

* `Edge α β`: an undirected edge with a label of type `β` and endpoints as a `Sym2 α`.
* `Arc α β`: a directed edge with a label of type `β` and endpoints as `α × α`.
* `Graph α β`: a general graph whose edges are `Edge α β` values. Parallel edges and
  loops are permitted.
* `SimpleGraph α`: a simple graph with edges as `Sym2 α`, no loops.
* `DiGraph α β`: a directed graph whose edges are `Arc α β` values. Parallel edges
  and loops are permitted.
* `SimpleDiGraph α`: a simple directed graph with edges as `α × α`, no loops.

## Notation

* `V(G)`: the vertex set of `G`, via `HasVertexSet`.
* `E(G)`: the edge set of `G`, via `HasEdgeSet`.

## Main API

The structure fields are named with a `'` suffix (e.g. `incidence'`, `loopless'`). The
preferred API restates these in terms of `V(G)` and `E(G)`:

* `Graph.incidence`, `SimpleGraph.incidence`, `DiGraph.incidence`, `SimpleDiGraph.incidence`
* `SimpleGraph.loopless`, `SimpleDiGraph.loopless`

## Main forgetful maps

* `SimpleGraph.toGraph`: forget the looplessness axiom of a simple graph.
* `SimpleDiGraph.toDiGraph`: forget the looplessness axiom of a simple directed graph.

The corresponding `Coe` instances are registered.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean
variable {α β : Type*}

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

/-- A simple graph on `α` with edges as unordered pairs of distinct vertices. -/
@[grind]
structure SimpleGraph (α : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The set of edges, each an unordered pair of vertices. -/
  edgeSet : Set (Sym2 α)
  /-- Both endpoints of every edge are vertices. Prefer `SimpleGraph.incidence`. -/
  incidence' : ∀ e ∈ edgeSet, ∀ v ∈ e, v ∈ vertexSet
  /-- No edge is a loop. Prefer `SimpleGraph.loopless`. -/
  loopless' : ∀ e ∈ edgeSet, ¬ e.IsDiag

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

/-- A simple directed graph on `α` with edges as ordered pairs of distinct vertices. -/
structure SimpleDiGraph (α : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The set of directed edges. -/
  edgeSet : Set (α × α)
  /-- Both endpoints of every directed edge are vertices. Prefer `SimpleDiGraph.incidence`. -/
  incidence' : ∀ e ∈ edgeSet, e.1 ∈ vertexSet ∧ e.2 ∈ vertexSet
  /-- No directed edge is a loop. Prefer `SimpleDiGraph.loopless`. -/
  loopless' : ∀ e ∈ edgeSet, e.1 ≠ e.2

/-- Forget the looplessness axiom of a `SimpleGraph`, viewing it as a `Graph` whose edges
are `Edge α (Sym2 α)` with the pair as both label and endpoints. -/
def SimpleGraph.toGraph (G : SimpleGraph α) : Graph α (Sym2 α) where
  vertexSet := G.vertexSet
  edgeSet := (fun e => ⟨e, e⟩) '' G.edgeSet
  incidence' := by
    rintro _ ⟨e, he, rfl⟩ v hv
    exact G.incidence' e he v hv

/-- Forget the looplessness axiom of a `SimpleDiGraph`, viewing it as a `DiGraph` whose
edges are `Arc α (α × α)` with the pair as both label and endpoints. -/
def SimpleDiGraph.toDiGraph (G : SimpleDiGraph α) : DiGraph α (α × α) where
  vertexSet := G.vertexSet
  edgeSet := (fun e => ⟨e, e⟩) '' G.edgeSet
  incidence' := by
    rintro _ ⟨e, he, rfl⟩
    exact G.incidence' e he

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

@[simp] instance {α β : Type*} : HasVertexSet (Graph α β) (Set α) :=
  ⟨Graph.vertexSet⟩

@[simp] instance {α : Type*} : HasVertexSet (SimpleGraph α) (Set α) :=
  ⟨SimpleGraph.vertexSet⟩

@[simp] instance {α β : Type*} : HasVertexSet (DiGraph α β) (Set α) :=
  ⟨DiGraph.vertexSet⟩

@[simp] instance {α : Type*} : HasVertexSet (SimpleDiGraph α) (Set α) :=
  ⟨SimpleDiGraph.vertexSet⟩

@[simp] instance {α β : Type*} : HasEdgeSet (Graph α β) (Set (Sym2 α)) :=
  ⟨fun G => Edge.endpoints '' G.edgeSet⟩

@[simp] instance {α : Type*} : HasEdgeSet (SimpleGraph α) (Set (Sym2 α)) :=
  ⟨SimpleGraph.edgeSet⟩

@[simp] instance {α β : Type*} : HasEdgeSet (DiGraph α β) (Set (α × α)) :=
  ⟨fun G => Arc.endpoints '' G.edgeSet⟩

@[simp] instance {α : Type*} : HasEdgeSet (SimpleDiGraph α) (Set (α × α)) :=
  ⟨SimpleDiGraph.edgeSet⟩

/-- Notation for the vertex set of a graph. -/
scoped notation "V(" G ")" => HasVertexSet.vertexSet G
/-- Notation for the edge set of a graph. -/
scoped notation "E(" G ")" => HasEdgeSet.edgeSet G

theorem Graph.incidence (G : Graph α β) {e : Sym2 α} (he : e ∈ E(G))
    {v : α} (hv : v ∈ e) : v ∈ V(G) := by
  obtain ⟨e', he', rfl⟩ := he
  exact G.incidence' e' he' v hv

theorem SimpleGraph.incidence (G : SimpleGraph α) {e : Sym2 α} (he : e ∈ E(G))
    {v : α} (hv : v ∈ e) : v ∈ V(G) :=
  G.incidence' e he v hv

theorem SimpleGraph.loopless (G : SimpleGraph α) {e : Sym2 α} (he : e ∈ E(G)) :
    ¬ e.IsDiag :=
  G.loopless' e he

theorem DiGraph.incidence (G : DiGraph α β) {e : α × α} (he : e ∈ E(G)) :
    e.1 ∈ V(G) ∧ e.2 ∈ V(G) := by
  obtain ⟨e', he', rfl⟩ := he
  exact G.incidence' e' he'

theorem SimpleDiGraph.incidence (G : SimpleDiGraph α) {e : α × α} (he : e ∈ E(G)) :
    e.1 ∈ V(G) ∧ e.2 ∈ V(G) :=
  G.incidence' e he

theorem SimpleDiGraph.loopless (G : SimpleDiGraph α) {e : α × α} (he : e ∈ E(G)) :
    e.1 ≠ e.2 :=
  G.loopless' e he

end Cslib.Algorithms.Lean
