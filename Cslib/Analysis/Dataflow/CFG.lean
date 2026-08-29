/-
Copyright (c) 2026 Jacopo Moretti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Moretti
-/

module

public import Cslib.Init
public import Mathlib.Data.Fintype.List
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.DFinsupp.WellFounded
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.Covering


/-!
# Control flow graphs

## Main definitions

- `CFG` is a structure representing Control Flow Graphs on which the dataflow
  algorithm defined in `Kildall.lean` runs.
-/

@[expose] public section

/-- Abstract structure defining the necessary operations on a CFG to define a Control Flow Graph. -/
structure CFG where
  /-- All of the nodes in the CFG. -/
  Node : Type u
  /-- A CFG contains a finite amount of nodes. -/
  [fintypeNode : Fintype Node]
  /-- An ordering of nodes, to make the conversion to lists computable. -/
  [orderNode : LinearOrder Node]
  /-- Decidable equality on nodes. -/
  [dEqNode : DecidableEq Node]
  /-- Quiver structure for the edges of the CFG. -/
  quiver : Quiver Node
  /-- A CFG contains a finite amount of edges. -/
  [fintypeEdges : ∀ a b, Fintype (@Quiver.Hom Node quiver a b)]
  /-- Distinguished entry node in the CFG. -/
  entry : Node

namespace CFG

instance {g : CFG} : Fintype (g.Node) :=
  g.fintypeNode

instance {g : CFG} : LinearOrder (g.Node) :=
  g.orderNode

/-- Finite set of all of the nodes of `g` -/
def nodesOf (g : CFG) : Finset g.Node := g.fintypeNode.elems

/-- List of all of the nodes of `g`, ordered by the ordering on `g.Node` -/
def nodeList (g : CFG) : List g.Node := g.nodesOf.sort

/-- Any node of `g` is in `g.nodeList`. -/
@[simp] theorem mem_nodeList (g : CFG) (n : g.Node) : n ∈ g.nodeList := by
  rw [nodeList]
  apply (Finset.mem_sort (· ≤ ·)).mpr
  exact @Fintype.complete _ g.fintypeNode n

/-- Convenience type for edges of `g`: `Edge src dst` represents an edge between src and dst. -/
abbrev Edge {g : CFG} (src dst : g.Node) := @Quiver.Hom g.Node g.quiver src dst
/-- Convenience type for incoming edges of `n` in `g`: `inEdge n` represents the type of edges
    entering n. -/
abbrev inEdge {g : CFG} (n : g.Node) := @Quiver.Costar g.Node g.quiver n
/-- Convenience type for outgoing edges of `n` in `g`: `outEdge n` represents the type of edges
    entering n. -/
abbrev outEdge {g : CFG} (n : g.Node) := @Quiver.Star g.Node g.quiver n

/-- All incoming edges of a given node, bundled with their source nodes. -/
def inEdges {g : CFG} (n : g.Node) : Finset (inEdge n) := by
  letI := g.quiver
  letI := g.fintypeNode
  letI := g.orderNode
  letI (src dst : g.Node) := g.fintypeEdges src dst
  exact Finset.univ

/-- All outgoing edges of a given node, bundled with their source nodes. -/
def outEdges {g : CFG} (n : g.Node) : Finset (outEdge n) := by
  letI := g.quiver
  letI := g.fintypeNode
  letI (src dst : g.Node) := g.fintypeEdges src dst
  exact Finset.univ

/-- The set of successor nodes of node `n` in `g`. -/
def succOf {g : CFG} (n : g.Node) : Finset g.Node :=
  letI := g.dEqNode
  (outEdges n).image Sigma.fst

end CFG
