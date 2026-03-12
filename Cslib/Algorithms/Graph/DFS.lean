/-
Copyright (c) 2025 Brando Miranda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brando Miranda
-/

module

public import Cslib.Init

@[expose] public section

/-!
# Depth-First Search (DFS) for Graph Reachability

This file defines a depth-first search algorithm on directed graphs represented as adjacency
lists, and proves its correctness with respect to reachability.

## Main definitions

- `Graph`: A directed graph as an adjacency list (`List (List Nat)`).
- `dfsAux`: Recursive DFS helper with a visited list and fuel parameter.
- `dfs`: Top-level DFS checking reachability from `start` to `target`.
- `Reachable`: Inductive predicate for path existence in a graph.

## Main results

- `dfs_soundness`: If `dfs g start target = true`, then `target` is reachable from `start`.
- `dfs_completeness`: Under valid graph preconditions, if `target` is reachable from `start`,
  then `dfs g start target = true`.

## References

Adapted from the VeriBench benchmark (https://github.com/brandomiranda/veribench).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Graph.DFS

/-- A directed graph represented as an adjacency list.
`g[i]` is the list of successors of node `i`. -/
abbrev Graph := List (List Nat)

/-- Recursive DFS helper. Explores the graph from `current` looking for `target`,
tracking `visited` nodes to avoid cycles. The `fuel` parameter ensures termination. -/
def dfsAux (g : Graph) (current target : Nat) (visited : List Nat) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | n + 1 =>
    if current == target then
      true
    else if current ∈ visited then
      false
    else
      let neighbors := g[current]?.getD []
      neighbors.any (fun next => dfsAux g next target (current :: visited) n)

/-- Depth-first search for reachability. Returns `true` iff `target` is reachable from `start`
in the directed graph `g`. -/
def dfs (g : Graph) (start target : Nat) : Bool :=
  dfsAux g start target [] (g.length + 1)

/-! ## Tests -/

private def g1 : Graph := [[1], [2], []]
example : dfs g1 0 2 = true := by decide
example : dfs g1 2 0 = false := by decide

private def g2 : Graph := [[1], [], [3], []]
example : dfs g2 0 1 = true := by decide
example : dfs g2 0 2 = false := by decide

private def g3 : Graph := [[1], [0]]
example : dfs g3 0 1 = true := by decide
example : dfs g3 1 0 = true := by decide

/-! ## Reachability -/

/-- `Reachable g x y` holds iff there is a directed path from `x` to `y` in `g`. -/
inductive Reachable (g : Graph) : Nat → Nat → Prop where
  /-- Every node is reachable from itself. -/
  | refl (x : Nat) : Reachable g x x
  /-- If `y` is a neighbor of `x` and `z` is reachable from `y`, then `z` is reachable
  from `x`. -/
  | step (x y z : Nat) : y ∈ (g[x]?.getD []) → Reachable g y z → Reachable g x z

/-! ## Pre-condition -/

/-- A graph is well-formed and the start/target are valid nodes. -/
def Pre (g : Graph) (start target : Nat) : Prop :=
  (∀ i, (hi : i < g.length) → ∀ n ∈ g[i], n < g.length) ∧
  start < g.length ∧
  target < g.length

/-! ## Soundness -/

/-- If `dfsAux` returns `true`, then `target` is reachable from `current`. -/
theorem dfsAux_soundness (g : Graph) (current target : Nat) (visited : List Nat) (fuel : Nat) :
    dfsAux g current target visited fuel = true → Reachable g current target := by
  induction fuel generalizing current visited with
  | zero => simp [dfsAux]
  | succ n ih =>
    simp only [dfsAux]
    split
    · rename_i h_eq
      intro _
      have : current = target := by exact beq_iff_eq.mp h_eq
      rw [this]; exact Reachable.refl target
    · split
      · simp
      · intro h
        rw [List.any_eq_true] at h
        obtain ⟨next, h_mem, h_rec⟩ := h
        exact Reachable.step current next target h_mem (ih next (current :: visited) h_rec)

/-- **Soundness**: If `dfs g start target = true`, then `target` is reachable from `start`. -/
theorem dfs_soundness (g : Graph) (start target : Nat) :
    dfs g start target = true → Reachable g start target :=
  dfsAux_soundness g start target [] (g.length + 1)

/-! ## Completeness auxiliary definitions -/

/-- `ReachableAvoiding g x y n S` holds iff there is a path from `x` to `y` in `g` of at most
`n` steps, where no intermediate node revisits any node already in `S`. -/
inductive ReachableAvoiding (g : Graph) : Nat → Nat → Nat → List Nat → Prop where
  /-- Every node reaches itself in 0 steps. -/
  | refl (x : Nat) (S : List Nat) : ReachableAvoiding g x x 0 S
  /-- If `x ∉ S`, `y` is a neighbor of `x`, and `z` is reachable from `y` in `n` steps while
  also avoiding `x`, then `z` is reachable from `x` in `n + 1` steps. -/
  | step (x y z : Nat) (n : Nat) (S : List Nat) :
      x ∉ S → y ∈ (g[x]?.getD []) → ReachableAvoiding g y z n (x :: S) →
      ReachableAvoiding g x z (n + 1) S

/-- `ReachableAvoiding` implies `Reachable` (forget the bound and avoid set). -/
theorem ReachableAvoiding.toReachable {g : Graph} {x y : Nat} {n : Nat} {S : List Nat}
    (h : ReachableAvoiding g x y n S) : Reachable g x y := by
  induction h with
  | refl x _ => exact Reachable.refl x
  | step x y z _ _ _ h_edge _ ih => exact Reachable.step x y z h_edge ih

/-! ## Completeness: dfsAux finds paths that avoid the visited set -/

/-- If there is a path from `current` to `target` in `n` steps avoiding all nodes in `visited`,
and `n < fuel`, then `dfsAux` returns `true`. -/
theorem dfsAux_complete_avoiding (g : Graph) (current target : Nat) (visited : List Nat)
    (fuel n : Nat) (hreach : ReachableAvoiding g current target n visited)
    (hfuel : n < fuel) :
    dfsAux g current target visited fuel = true := by
  induction hreach generalizing fuel with
  | refl x S =>
    cases fuel with
    | zero => omega
    | succ m => simp [dfsAux]
  | step x y z k S hx_not_visited hy_edge _ ih =>
    cases fuel with
    | zero => omega
    | succ m =>
      unfold dfsAux
      simp only [beq_iff_eq]
      split
      · rfl
      · simp only [List.any_eq_true]
        exact ⟨y, hy_edge, ih m (by omega)⟩

/-! ## Completeness -/

/-- If there is a path from `start` to `target` of at most `g.length` steps (avoiding no
initial nodes), then `dfs` returns `true`. -/
theorem dfs_complete_avoiding (g : Graph) (start target : Nat) (n : Nat)
    (hreach : ReachableAvoiding g start target n [])
    (hlen : n ≤ g.length) :
    dfs g start target = true :=
  dfsAux_complete_avoiding g start target [] (g.length + 1) n hreach (by omega)

end Cslib.Algorithms.Graph.DFS
