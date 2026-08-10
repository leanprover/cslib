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
  [fintypeNode : Fintype Node]
  [orderNode : LinearOrder Node]
  [dEqNode : DecidableEq Node]
  /-- Quiver structure for the edges of the CFG. -/
  quiver : Quiver Node
  [fintypeHom : ∀ a b, Fintype (@Quiver.Hom Node quiver a b)]
  /-- Distinguished entry node in the CFG. -/
  entry : Node

namespace CFG

instance {g : CFG} : Fintype (g.Node) :=
  g.fintypeNode

instance {g : CFG} : LinearOrder (g.Node) :=
  g.orderNode

def nodesOf (g : CFG) : Finset g.Node := g.fintypeNode.elems

def nodeList (g : CFG) : List g.Node := g.nodesOf.sort

@[simp] theorem mem_nodeList (g : CFG) (n : g.Node) : n ∈ g.nodeList := by
  rw [nodeList]
  apply (Finset.mem_sort (· ≤ ·)).mpr
  exact @Fintype.complete _ g.fintypeNode n

abbrev Edge {g : CFG} (src dst : g.Node) := @Quiver.Hom g.Node g.quiver src dst
abbrev inEdge {g : CFG} (n : g.Node) := @Quiver.Costar g.Node g.quiver n
abbrev outEdge {g : CFG} (n : g.Node) := @Quiver.Star g.Node g.quiver n

/-- All incoming edges of a given node, bundled with their source nodes. -/
def inEdges {g : CFG} (n : g.Node) : Finset (inEdge n) := by
  letI := g.quiver
  letI := g.fintypeNode
  letI := g.orderNode
  letI (src dst : g.Node) := g.fintypeHom src dst
  exact Finset.univ

def outEdges {g : CFG} (n : g.Node) : Finset (outEdge n) := by
  letI := g.quiver
  letI := g.fintypeNode
  letI (src dst : g.Node) := g.fintypeHom src dst
  exact Finset.univ

def succOf {g : CFG} (n : g.Node) : Finset g.Node :=
  letI := g.dEqNode
  (outEdges n).image Sigma.fst

end CFG
