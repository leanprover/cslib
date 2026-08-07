/-
Copyright (c) 2026 Jacopo Moretti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacopo Moretti
-/

module

public import Cslib.Init
public import Mathlib.Data.Fintype.List
public import Mathlib.Data.DFinsupp.WellFounded


/-!
# Control flow graphs

## Main definitions

- `CFG` is a structure representing Control Flow Graphs on which the dataflow
  algorithm defined in `Kildall.lean` runs.
-/

@[expose] public section

variable {Node Edge : Type} [DecidableEq Node] [DecidableEq Edge]

/-- Abstract structure defining the necessary operations on a CFG to define a Control Flow Graph. -/
class CFG (Node Edge : Type) [DecidableEq Node] [DecidableEq Edge] where
  /-- All of the nodes in the CFG. -/
  nodes : List Node
  /-- All of the edges in the CFG. -/
  edges : List Edge
  /-- A distinguished entry node in the CFG. -/
  entry : Node
  /-- A proof that the entry node is part of the graph's nodes. -/
  entry_mem : entry ∈ nodes
  /-- Extractor function for an edge's source node. -/
  _srcOf : Edge → Node
  /-- Proof of correctness for the source extractor. -/
  srcOf_mem : ∀ e ∈ edges, _srcOf e ∈ nodes
  /-- Extractor function for an edge's destination node. -/
  _dstOf : Edge → Node
  /-- Proof of correctness for the destination extractor. -/
  dstOf_mem : ∀ e ∈ edges, _dstOf e ∈ nodes

abbrev NodeOf (g : CFG Node Edge) : Type := {n // n ∈ g.nodes}
abbrev EdgeOf (g : CFG Node Edge) : Type := {e // e ∈ g.edges}

namespace CFG

/-- `g.nodes`, presented as `NodeOf g`. -/
def nodesOf (g : CFG Node Edge) : List (NodeOf g) := g.nodes.attach

def edgesOf (g : CFG Node Edge) : List (EdgeOf g) := g.edges.attach

def dstOf (g : CFG Node Edge) (e : EdgeOf g) : NodeOf g :=
  ⟨g._dstOf e, g.dstOf_mem e e.property⟩

def srcOf (g : CFG Node Edge) (e : EdgeOf g) : NodeOf g :=
  ⟨g._srcOf e, g.srcOf_mem e e.property⟩

/-- All in-edges of a given node -/
def inEdges (g : CFG Node Edge) (n : NodeOf g) : List (EdgeOf g) :=
  g.edgesOf.filter (g.dstOf · = n)

def succOf (g : CFG Node Edge) (n : NodeOf g) : List (NodeOf g) :=
  g.nodesOf.filter (fun m => (g.inEdges m).any (g.srcOf · = n))

instance {g : CFG Node Edge} : Fintype (NodeOf g) :=
  List.Subtype.fintype g.nodes

end CFG
