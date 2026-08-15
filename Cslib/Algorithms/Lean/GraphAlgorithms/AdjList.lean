/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sigma

/-!
# Adjacency lists for finite multigraphs

An `AdjList V` is directly a function `V → List V`. Repeated neighbors represent parallel edge
occurrences; no duplicate-freeness condition is imposed. The vertex type is assumed finite, while a
concrete enumeration is chosen only locally by algorithms that need one.

`AdjList.toGraph` turns every list position into an edge identity, so repeated entries remain
distinct edges. `AdjList.ofGraph` forgets the edge identities of a finite Mathlib `Graph`, retaining
one neighbor-list entry for every incident edge. Since an undirected edge is incident at both ends,
the round-trip API is stated in terms of incidence and adjacency rather than equality of edge types.
-/

@[expose] public section

set_option autoImplicit false

open scoped Graph

namespace Cslib.Algorithms.Lean.GraphAlgorithms

/-- An adjacency list on a finite vertex type. Repeated entries encode parallel edges. -/
structure AdjList (V : Type*) [Finite V] where
  /-- The list of vertices adjacent to each vertex. -/
  incidence : V → List V

namespace AdjList

variable {V α β : Type*} [Finite V] (A : AdjList V)

/-- Edge occurrences of an adjacency list. The first component is the source list and the second
component is a valid position in that list. -/
def Edge := (v : V) × Fin (A.incidence v).length

/-- The other end stored at an edge occurrence. -/
def target (e : A.Edge) : V :=
  (A.incidence e.1).get e.2

/-- The target of an edge occurrence is the entry at its list position. -/
@[simp]
theorem target_mk (v : V) (i : Fin (A.incidence v).length) :
    A.target ⟨v, i⟩ = (A.incidence v).get i :=
  rfl

instance : Finite A.Edge := by
  dsimp only [Edge]
  let _ : Fintype V := Fintype.ofFinite V
  exact Fintype.finite (inferInstance : Fintype ((v : V) × Fin (A.incidence v).length))

/-- The Mathlib multigraph represented by the edge occurrences of an adjacency list. -/
@[simps! vertexSet edgeSet]
def toGraph : Graph V A.Edge where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e u v := (u = e.1 ∧ v = A.target e) ∨ (u = A.target e ∧ v = e.1)
  isLink_symm := fun _ _ ↦ ⟨by grind⟩
  eq_or_eq_of_isLink_of_isLink := by grind
  edge_mem_iff_exists_isLink e :=
    ⟨fun _ ↦ ⟨e.1, A.target e, Or.inl ⟨rfl, rfl⟩⟩, fun _ ↦ Set.mem_univ e⟩

@[simp]
theorem toGraph_isLink (e : A.Edge) (u v : V) :
    A.toGraph.IsLink e u v ↔ (u = e.1 ∧ v = A.target e) ∨ (u = A.target e ∧ v = e.1) :=
  Iff.rfl

@[simp]
theorem target_mem_incidence (e : A.Edge) : A.target e ∈ A.incidence e.1 :=
  List.get_mem _ _

/-- Adjacency in `toGraph` is the symmetric closure of list membership. -/
@[simp]
theorem toGraph_adj_iff (u v : V) :
    A.toGraph.Adj u v ↔ v ∈ A.incidence u ∨ u ∈ A.incidence v := by
  constructor
  · rintro ⟨e, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact Or.inl (A.target_mem_incidence e)
    · exact Or.inr (A.target_mem_incidence e)
  · rintro (h | h)
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
      exact ⟨⟨u, i⟩, Or.inl ⟨rfl, hi.symm⟩⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
      exact ⟨⟨v, i⟩, Or.inr ⟨hi.symm, rfl⟩⟩

/-- The other endpoint of an edge known to be incident with `v`. -/
noncomputable def graphOther (G : Graph α β) (v : V(G)) (e : β) (h : G.Inc e v) : V(G) :=
  ⟨h.other, h.inc_other.vertex_mem⟩

@[simp]
theorem graphOther_spec (G : Graph α β) (v : V(G)) (e : β) (h : G.Inc e v) :
    G.IsLink e v (graphOther G v e h) :=
  h.isLink_other

/-- Convert a finite Mathlib multigraph to adjacency lists on its actual vertex subtype. -/
noncomputable def ofGraph (G : Graph α β) [Finite V(G)] [Finite E(G)] : AdjList V(G) := by
  let _ := Fintype.ofFinite E(G)
  classical
  exact ⟨fun v ↦ (Finset.univ : Finset E(G)).toList.flatMap fun e ↦
    if h : G.Inc e.1 v.1 then [graphOther G v e.1 h] else []⟩

@[simp]
theorem mem_incidence_ofGraph (G : Graph α β) [Finite V(G)] [Finite E(G)]
    (u v : V(G)) : u ∈ (ofGraph G).incidence v ↔ G.Adj v.1 u.1 := by
  let _ := Fintype.ofFinite E(G)
  classical
  simp only [ofGraph, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, h⟩
    split at h
    next he =>
      simp only [List.mem_singleton] at h
      subst u
      exact (graphOther_spec G v e.1 he).adj
    next => simp at h
  · rintro ⟨e, he⟩
    let e' : E(G) := ⟨e, he.edge_mem⟩
    refine ⟨e', ?_⟩
    rw [dite_eq_left he.inc_left]
    simp only [List.mem_singleton]
    apply Subtype.ext
    exact (graphOther_spec G v e he.inc_left).right_unique he |>.symm

theorem toGraph_ofGraph_adj (G : Graph α β) [Finite V(G)] [Finite E(G)]
    (u v : V(G)) : (ofGraph G).toGraph.Adj u v ↔ G.Adj u.1 v.1 := by
  simp [Graph.adj_comm]

end AdjList
end Cslib.Algorithms.Lean.GraphAlgorithms
