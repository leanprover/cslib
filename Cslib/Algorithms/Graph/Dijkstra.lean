/-
Copyright (c) 2025 Brando Miranda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brando Miranda
-/

module

public import Cslib.Init

@[expose] public section

/-!
# Dijkstra's Algorithm

This file implements Dijkstra's shortest path algorithm on weighted adjacency-list graphs
and proves basic correctness properties.

## Main definitions

- `Graph`: Weighted directed graph as adjacency list `List (List (Nat × Nat))`.
- `extractMin`: Extract the minimum-distance entry from a priority queue.
- `dijkstraAux`: Fuel-based Dijkstra helper.
- `dijkstra`: Top-level shortest path computation.
- `IsWeightedPath`: Inductive definition of weighted paths in a graph.

## Main results

- `dijkstra_start_self`: Dijkstra from a node to itself returns `some 0`.

## References

Adapted from the VeriBench benchmark (https://github.com/brandomiranda/veribench).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Graph.Dijkstra

/-- A weighted directed graph as an adjacency list.
`g[i]` is the list of `(neighbor, weight)` pairs for node `i`. -/
abbrev Graph := List (List (Nat × Nat))

/-- Extract the minimum-distance entry from a priority queue (list of (distance, node) pairs).
Returns the entry with smallest distance and the remaining queue. -/
def extractMin (queue : List (Nat × Nat)) : Option ((Nat × Nat) × List (Nat × Nat)) :=
  match queue with
  | [] => none
  | head :: _ =>
    let minEntry := queue.foldl (fun acc x => if x.1 < acc.1 then x else acc) head
    some (minEntry, queue.erase minEntry)

/-- Fuel-based Dijkstra's algorithm helper.
Explores nodes in order of increasing distance from the source. -/
def dijkstraAux (g : Graph) (target : Nat) (queue : List (Nat × Nat))
    (visited : List Nat) (fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match extractMin queue with
    | none => none
    | some ((dist, u), restQueue) =>
      if u == target then some dist
      else if u ∈ visited then dijkstraAux g target restQueue visited n
      else
        let neighbors := g[u]?.getD []
        let newEntries := neighbors.map (fun (v, w) => (dist + w, v))
        dijkstraAux g target (restQueue ++ newEntries) (u :: visited) n

/-- Compute shortest path distance from `start` to `target` in graph `g`.
Returns `some distance` if reachable, `none` otherwise. -/
def dijkstra (g : Graph) (start target : Nat) : Option Nat :=
  dijkstraAux g target [(0, start)] [] (g.length * g.length + 1)

/-! ## Tests -/

private def g1 : Graph := [[(1, 1), (2, 4)], [(2, 2)], []]

example : dijkstra g1 0 2 = some 3 := by decide
example : dijkstra g1 0 1 = some 1 := by decide
example : dijkstra g1 0 0 = some 0 := by decide

private def g2 : Graph := [[(1, 10)], [], []]

example : dijkstra g2 0 2 = none := by decide
example : dijkstra g2 0 1 = some 10 := by decide

/-! ## Weighted paths -/

/-- A weighted path in a graph from node `src` to node `dst` with total weight `w`. -/
inductive IsWeightedPath (g : Graph) : Nat → Nat → Nat → Prop where
  | refl (x : Nat) : IsWeightedPath g x x 0
  | step (x y z w total : Nat) :
      (y, w) ∈ (g[x]?.getD []) →
      IsWeightedPath g y z total →
      IsWeightedPath g x z (w + total)

/-- A path of weight 0 from any node to itself. -/
theorem weighted_path_refl (g : Graph) (x : Nat) : IsWeightedPath g x x 0 :=
  IsWeightedPath.refl x

/-! ## Self-distance -/

/-- Helper: extractMin of a singleton returns that element with empty rest. -/
private theorem extractMin_singleton (d n : Nat) :
    extractMin [(d, n)] = some ((d, n), []) := by
  simp only [extractMin, List.foldl, List.erase, beq_self_eq_true,
    Nat.lt_irrefl, ite_false]

/-- Dijkstra from a node to itself returns `some 0`. -/
theorem dijkstra_start_self (g : Graph) (start : Nat) :
    dijkstra g start start = some 0 := by
  simp only [dijkstra, dijkstraAux, extractMin_singleton, beq_self_eq_true, ite_true]

end Cslib.Algorithms.Graph.Dijkstra
