/-
Copyright (c) 2025 Brando Miranda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brando Miranda
-/

module

public import Cslib.Init

@[expose] public section

/-!
# Breadth-First Search (BFS) for Shortest Paths in Graphs

This file defines a breadth-first search algorithm on directed graphs represented as adjacency
lists, and proves soundness: if BFS returns a distance, a path of that length exists.

## Main definitions

- `Graph`: A directed graph as an adjacency list (`List (List Nat)`).
- `bfsAux`: BFS loop with a queue of `(node, distance)` pairs.
- `bfs`: Top-level BFS returning the shortest distance from `start` to `target`.
- `IsPath`: Inductive predicate for directed paths with explicit intermediate nodes.

## Main results

- `bfs_soundness`: If `bfs g start target = some d`, then there is a path of length `d`.

## References

Adapted from the VeriBench benchmark (https://github.com/brandomiranda/veribench).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Graph.BFS

/-- A directed graph represented as an adjacency list. -/
abbrev Graph := List (List Nat)

/-- BFS loop. Processes a queue of `(node, distance)` pairs, returning the distance to `target`
if found. The `fuel` parameter bounds the number of iterations. -/
def bfsAux (g : Graph) (target : Nat) (queue : List (Nat × Nat))
    (visited : List Nat) (fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match queue with
    | [] => none
    | (curr, dist) :: restQueue =>
      if curr == target then
        some dist
      else
        let neighbors := g[curr]?.getD []
        let newNeighbors := neighbors.filter (fun x => x ∉ visited)
        let newEntries := newNeighbors.map (fun x => (x, dist + 1))
        bfsAux g target (restQueue ++ newEntries) (visited ++ newNeighbors) n

/-- Breadth-first search for shortest distance. Returns `some d` where `d` is the shortest
distance from `start` to `target`, or `none` if `target` is unreachable. -/
def bfs (g : Graph) (start target : Nat) : Option Nat :=
  if start == target then
    some 0
  else
    bfsAux g target [(start, 0)] [start] (g.length * g.length + 1)

/-! ## Tests -/

private def g1 : Graph := [[1], [2], []]
example : bfs g1 0 2 = some 2 := by decide
example : bfs g1 0 1 = some 1 := by decide

private def g2 : Graph := [[1], [], [3], []]
example : bfs g2 0 2 = none := by decide

private def g4 : Graph := [[1, 2], [], []]
example : bfs g4 0 2 = some 1 := by decide

/-! ## Path predicate -/

/-- `IsPath g x y path` holds iff `path` is a sequence of intermediate nodes forming a directed
walk from `x` to `y` in `g`. The length of `path` equals the number of edges traversed. -/
inductive IsPath (g : Graph) : Nat → Nat → List Nat → Prop where
  /-- The empty path from a node to itself. -/
  | base (x : Nat) : IsPath g x x []
  /-- Extend a path at the front: if `y` is a neighbor of `x` and there is a path from `y` to
  `z`, then there is a path from `x` to `z` via `y`. -/
  | step (x y z : Nat) (path : List Nat) :
      y ∈ (g[x]?.getD []) → IsPath g y z path → IsPath g x z (y :: path)

/-- Transitivity of paths: composing two paths yields a path. -/
theorem IsPath.trans {g : Graph} {x y z : Nat} {p1 p2 : List Nat}
    (h1 : IsPath g x y p1) (h2 : IsPath g y z p2) :
    IsPath g x z (p1 ++ p2) := by
  induction h1 with
  | base _ => exact h2
  | step a b _ p hab _ ih =>
    exact IsPath.step a b z (p ++ p2) hab (ih h2)

/-- Extending a path by one edge at the end. -/
theorem IsPath.snoc {g : Graph} {x y z : Nat} {p : List Nat}
    (h1 : IsPath g x y p) (h2 : z ∈ (g[y]?.getD [])) :
    IsPath g x z (p ++ [z]) :=
  h1.trans (IsPath.step y z z [] h2 (IsPath.base z))

/-! ## Soundness -/

/-- Queue invariant: every `(v, d)` in the queue has a witnessed path from `start` to `v`
of length `d`. -/
def QueueInv (g : Graph) (start : Nat) (queue : List (Nat × Nat)) : Prop :=
  ∀ v d, (v, d) ∈ queue → ∃ path, IsPath g start v path ∧ path.length = d

/-- Core soundness: if `bfsAux` returns `some d` under a valid queue invariant, then a path
of length `d` from `start` to `target` exists. -/
theorem bfsAux_soundness (g : Graph) (start target : Nat) (queue : List (Nat × Nat))
    (visited : List Nat) (fuel d : Nat) (h_inv : QueueInv g start queue)
    (h_result : bfsAux g target queue visited fuel = some d) :
    ∃ path, IsPath g start target path ∧ path.length = d := by
  induction fuel generalizing queue visited with
  | zero => simp [bfsAux] at h_result
  | succ n ih =>
    simp only [bfsAux] at h_result
    split at h_result
    · simp at h_result
    · rename_i curr dist restQueue
      split at h_result
      · -- curr == target
        rename_i h_eq
        have h_ct : curr = target := beq_iff_eq.mp h_eq
        simp only [Option.some.injEq] at h_result
        subst h_ct; subst h_result
        exact h_inv curr dist (List.mem_cons.mpr (Or.inl rfl))
      · -- curr ≠ target, recurse
        apply ih _ _ _ h_result
        intro v dv h_mem
        rw [List.mem_append] at h_mem
        rcases h_mem with h_old | h_new
        · exact h_inv v dv (List.mem_cons.mpr (Or.inr h_old))
        · rw [List.mem_map] at h_new
          obtain ⟨w, h_w_mem, h_eq⟩ := h_new
          have hv : v = w := (Prod.mk.inj h_eq).1.symm
          have hd : dv = dist + 1 := (Prod.mk.inj h_eq).2.symm
          subst hv; subst hd
          rw [List.mem_filter] at h_w_mem
          obtain ⟨h_w_neighbor, _⟩ := h_w_mem
          obtain ⟨path, h_path, h_len⟩ :=
            h_inv curr dist (List.mem_cons.mpr (Or.inl rfl))
          exact ⟨path ++ [v], h_path.snoc h_w_neighbor, by simp [h_len]⟩

/-- **Soundness**: If `bfs g start target = some d`, then there is a directed path of length
`d` from `start` to `target`. -/
theorem bfs_soundness (g : Graph) (start target : Nat) (d : Nat)
    (h : bfs g start target = some d) :
    ∃ path, IsPath g start target path ∧ path.length = d := by
  unfold bfs at h
  by_cases hst : start == target
  · simp [hst] at h
    have h_eq : start = target := beq_iff_eq.mp hst
    rw [← h, h_eq]
    exact ⟨[], IsPath.base target, rfl⟩
  · simp [hst] at h
    exact bfsAux_soundness g start target [(start, 0)] [start] _ d
      (fun v dv hm => by
        simp only [List.mem_singleton, Prod.mk.injEq] at hm
        rw [hm.1, hm.2]
        exact ⟨[], IsPath.base start, rfl⟩)
      h

end Cslib.Algorithms.Graph.BFS
