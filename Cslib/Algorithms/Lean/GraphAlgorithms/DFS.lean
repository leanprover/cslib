/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.EquivFin

/-!
# Depth-first search

This file implements iterative depth-first search over a finite Mathlib `Graph`. The top-level
function constructs incidence lists directly from the graph. The starting vertex is explicit, and
both loops are tail recursive. The outer loop carries the DFS stack; the inner loop scans one
incidence list and pushes vertices when they are first discovered.

The cost model charges one tick for every incidence-list entry inspected and one tick for every
stack push and pop. Thus a completed search costs twice the number of visited vertices plus the
number of incidence-list entries of visited vertices. In particular, on a connected graph the cost
is `2 * |V| + |E|`, where `|E|` is the total length of the generated incidence lists (the standard
adjacency-list size, counting parallel occurrences).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.GraphAlgorithms

open Cslib.Algorithms.Lean
open scoped Graph

namespace DFS

variable {V : Type*}

/-- The mutable state carried by the tail-recursive DFS loops. -/
structure State (V : Type*) where
  /-- Vertices discovered so far. A vertex is marked when it is pushed. -/
  visited : Finset V
  /-- Vertices whose incidence lists have been completely scanned. -/
  done : Finset V
  /-- The explicit LIFO work stack. -/
  stack : List V

/-- Membership symmetry is the well-formedness condition needed to view an adjacency list as an
undirected representation. Multiplicities may differ and entries may repeat; DFS correctness only
depends on adjacency. -/
def Symmetric (incidence : V → List V) : Prop :=
  ∀ u v, v ∈ incidence u ↔ u ∈ incidence v

/-- Reachability is the reflexive-transitive closure of adjacency-list steps. -/
def Reachable (incidence : V → List V) (u v : V) : Prop :=
  Relation.ReflTransGen (fun x y ↦ y ∈ incidence x) u v

@[refl]
theorem Reachable.refl (incidence : V → List V) (v : V) : Reachable incidence v v :=
  Relation.ReflTransGen.refl

theorem Reachable.tail (incidence : V → List V) {u v w : V} (h : Reachable incidence u v)
    (hvw : w ∈ incidence v) : Reachable incidence u w :=
  Relation.ReflTransGen.tail h hvw

/-- Number of adjacency-list entries belonging to a set of vertices. Repeated entries count
separately, as required for multigraphs and for the actual list-scanning cost. -/
def edgeCount (incidence : V → List V) (vertices : Finset V) : ℕ :=
  vertices.sum fun v ↦ (incidence v).length

@[simp]
theorem edgeCount_empty (incidence : V → List V) : edgeCount incidence ∅ = 0 :=
  rfl

section Algorithm

variable [DecidableEq V]

private theorem insert_sdiff_of_mem {v : V} {s t : Finset V} (hv : v ∈ s) :
    insert v t \ s = t \ s := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  by_cases hx : x = v <;> grind

private theorem card_insert_sdiff_of_not_mem {v : V} {s t : Finset V} (hv : v ∉ s) :
    (insert v t \ s).card = 1 + (t \ insert v s).card := by
  have heq : insert v t \ s = insert v (t \ insert v s) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    by_cases hx : x = v <;> grind
  rw [heq, Finset.card_insert_of_notMem (by simp)]
  lia

/-- Scan an incidence list, pushing each vertex that has not previously been discovered.

Each list entry costs one tick. A successful stack push costs one additional tick. -/
def scan : List V → State V → TimeM ℕ (State V)
  | [], state => pure state
  | v :: neighbors, state => do
      ✓ let seen := v ∈ state.visited
      if seen then
        scan neighbors state
      else
        ✓ scan neighbors { state with
          visited := insert v state.visited, stack := v :: state.stack }

/-- The tail-recursive DFS loop. `fuel` bounds the number of stack pops.

Vertices are marked before they are pushed, so every vertex is pushed at most once and
`Fintype.card V` units of fuel suffice. -/
def loop (incidence : V → List V) : ℕ → State V → TimeM ℕ (State V)
  | 0, state => pure state
  | fuel + 1, state =>
      match state.stack with
      | [] => pure state
      | v :: stack => do
          ✓ let state := { state with stack }
          let state ← scan (incidence v) state
          loop incidence fuel { state with done := insert v state.done }

/-- Run depth-first search over an incidence function from `start`. -/
def runIncidence [Fintype V] (incidence : V → List V) (start : V) :
    TimeM ℕ (Finset V) := do
  ✓ let state : State V := { visited := {start}, done := ∅, stack := [start] }
  let state ← loop incidence (Fintype.card V) state
  return state.visited

@[simp]
private theorem ret_runIncidence [Fintype V] (incidence : V → List V) (start : V) :
    (runIncidence incidence start).ret =
      (loop incidence (Fintype.card V) ⟨{start}, ∅, [start]⟩).ret.visited :=
  rfl

@[simp]
private theorem time_runIncidence [Fintype V] (incidence : V → List V) (start : V) :
    (runIncidence incidence start).time =
      1 + (loop incidence (Fintype.card V) ⟨{start}, ∅, [start]⟩).time :=
  rfl

@[simp]
theorem ret_scan_nil (state : State V) : (scan [] state).ret = state :=
  rfl

@[simp]
theorem time_scan_nil (state : State V) : (scan [] state).time = 0 :=
  rfl

@[simp]
theorem ret_loop_zero (incidence : V → List V) (state : State V) :
    (loop incidence 0 state).ret = state :=
  rfl

@[simp]
theorem time_loop_zero (incidence : V → List V) (state : State V) :
    (loop incidence 0 state).time = 0 :=
  rfl

@[simp]
theorem ret_loop_succ_nil (incidence : V → List V) (fuel : ℕ) (visited done : Finset V) :
    (loop incidence (fuel + 1) ⟨visited, done, []⟩).ret = ⟨visited, done, []⟩ :=
  rfl

@[simp]
theorem time_loop_succ_nil (incidence : V → List V) (fuel : ℕ)
    (visited done : Finset V) : (loop incidence (fuel + 1) ⟨visited, done, []⟩).time = 0 :=
  rfl

@[simp]
theorem ret_loop_succ_cons (incidence : V → List V) (fuel : ℕ) (visited done : Finset V)
    (v : V) (stack : List V) :
    (loop incidence (fuel + 1) ⟨visited, done, v :: stack⟩).ret =
      (loop incidence fuel { (scan (incidence v) ⟨visited, done, stack⟩).ret with
        done := insert v (scan (incidence v) ⟨visited, done, stack⟩).ret.done }).ret :=
  rfl

@[simp]
theorem time_loop_succ_cons (incidence : V → List V) (fuel : ℕ) (visited done : Finset V)
    (v : V) (stack : List V) :
    (loop incidence (fuel + 1) ⟨visited, done, v :: stack⟩).time =
      1 + ((scan (incidence v) ⟨visited, done, stack⟩).time +
        (loop incidence fuel { (scan (incidence v) ⟨visited, done, stack⟩).ret with
          done := insert v (scan (incidence v) ⟨visited, done, stack⟩).ret.done }).time) :=
  rfl

@[simp]
theorem ret_scan_done (neighbors : List V) (state : State V) :
    (scan neighbors state).ret.done = state.done := by
  induction neighbors generalizing state with
  | nil => rfl
  | cons v neighbors ih =>
    simp only [scan, TimeM.ret_bind]
    split <;> simp [ih]

@[simp]
theorem ret_scan_visited (neighbors : List V) (state : State V) :
    (scan neighbors state).ret.visited = state.visited ∪ neighbors.toFinset := by
  induction neighbors generalizing state with
  | nil => simp [scan]
  | cons v neighbors ih =>
    by_cases hv : v ∈ state.visited
    · simp [scan, hv, ih]
    · simp [scan, hv, ih]

theorem visited_subset_ret_scan (neighbors : List V) (state : State V) :
    state.visited ⊆ (scan neighbors state).ret.visited := by
  rw [ret_scan_visited]
  exact Finset.subset_union_left

theorem neighbors_subset_ret_scan (neighbors : List V) (state : State V) :
    neighbors.toFinset ⊆ (scan neighbors state).ret.visited := by
  rw [ret_scan_visited]
  exact Finset.subset_union_right

@[simp]
theorem ret_scan_stack_toFinset (neighbors : List V) (state : State V) :
    (scan neighbors state).ret.stack.toFinset =
      state.stack.toFinset ∪ (neighbors.toFinset \ state.visited) := by
  induction neighbors generalizing state with
  | nil => simp [scan]
  | cons v neighbors ih =>
    by_cases hv : v ∈ state.visited
    · ext a
      simp [scan, hv, ih]
      grind
    · ext a
      simp [scan, hv, ih]
      grind

@[simp]
theorem time_scan (neighbors : List V) (state : State V) :
    (scan neighbors state).time =
      neighbors.length + (neighbors.toFinset \ state.visited).card := by
  induction neighbors generalizing state with
  | nil => simp [scan]
  | cons v neighbors ih =>
    simp only [scan, TimeM.time_bind, TimeM.time_tick]
    by_cases hv : v ∈ state.visited
    · simp only [hv, ↓reduceIte, ih, List.length_cons, List.toFinset_cons]
      rw [insert_sdiff_of_mem hv]
      lia
    · simp only [hv, ↓reduceIte, TimeM.time_bind, TimeM.time_tick, ih,
        List.length_cons, List.toFinset_cons]
      rw [card_insert_sdiff_of_not_mem hv]
      lia

@[simp]
theorem length_ret_scan_stack (neighbors : List V) (state : State V)
    (hstack : state.stack.Nodup) (hsub : ∀ v ∈ state.stack, v ∈ state.visited) :
    (scan neighbors state).ret.stack.length =
      state.stack.length + (neighbors.toFinset \ state.visited).card := by
  induction neighbors generalizing state with
  | nil => simp [scan]
  | cons v neighbors ih =>
    simp only [scan, TimeM.ret_bind]
    by_cases hv : v ∈ state.visited
    · simp only [hv, ↓reduceIte, ih state hstack hsub, List.toFinset_cons]
      rw [insert_sdiff_of_mem hv]
    · have hvstack : v ∉ state.stack := fun h ↦ hv (hsub v h)
      simp only [hv, ↓reduceIte, TimeM.ret_bind]
      rw [ih]
      · simp only [List.length_cons, List.toFinset_cons]
        rw [card_insert_sdiff_of_not_mem hv]
        lia
      · exact hstack.cons hvstack
      · simp_all

theorem nodup_ret_scan_stack (neighbors : List V) (state : State V)
    (hstack : state.stack.Nodup) (hsub : ∀ v ∈ state.stack, v ∈ state.visited) :
    (scan neighbors state).ret.stack.Nodup := by
  induction neighbors generalizing state with
  | nil => exact hstack
  | cons v neighbors ih =>
    simp only [scan, TimeM.ret_bind]
    by_cases hv : v ∈ state.visited
    · simp only [hv, ↓reduceIte]
      exact ih state hstack hsub
    · simp only [hv, ↓reduceIte, TimeM.ret_bind]
      apply ih
      · exact hstack.cons (fun h ↦ hv (hsub v h))
      · simp_all

theorem stack_ret_scan_subset_visited (neighbors : List V) (state : State V)
    (hsub : ∀ v ∈ state.stack, v ∈ state.visited) :
    ∀ v ∈ (scan neighbors state).ret.stack, v ∈ (scan neighbors state).ret.visited := by
  intro v hv
  rw [← List.mem_toFinset, ret_scan_stack_toFinset] at hv
  rw [ret_scan_visited]
  simp only [Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset] at hv ⊢
  grind

private theorem card_visited_ret_scan (neighbors : List V) (state : State V) :
    (scan neighbors state).ret.visited.card =
      state.visited.card + (neighbors.toFinset \ state.visited).card := by
  rw [ret_scan_visited, Finset.union_comm,
    ← Finset.card_sdiff_add_card neighbors.toFinset state.visited]
  ac_rfl

/-- Loop invariant used for both functional correctness and the exact cost proof. -/
structure Invariant (incidence : V → List V) (start : V) (state : State V) : Prop where
  /-- The work stack contains each discovered-but-unprocessed vertex at most once. -/
  stack_nodup : state.stack.Nodup
  /-- Every vertex on the work stack has already been marked as visited. -/
  stack_subset_visited : ∀ v ∈ state.stack, v ∈ state.visited
  /-- Completely processed vertices do not remain on the work stack. -/
  done_disjoint_stack : Disjoint state.done state.stack.toFinset
  /-- Every visited vertex is either processed or waiting on the work stack. -/
  visited_eq : state.visited = state.done ∪ state.stack.toFinset
  /-- Every visited vertex is reachable from the starting vertex. -/
  reachable : ∀ v ∈ state.visited, Reachable incidence start v
  /-- Every neighbor of a completely processed vertex has been discovered. -/
  closed_done : ∀ v ∈ state.done, ∀ w ∈ incidence v, w ∈ state.visited

theorem Invariant.not_mem_done_of_mem_stack {incidence : V → List V} {start : V}
    {state : State V} (hinv : Invariant incidence start state) {v : V}
    (hv : v ∈ state.stack) : v ∉ state.done := by
  exact fun hdone ↦ Finset.disjoint_left.1 hinv.done_disjoint_stack hdone
    (List.mem_toFinset.2 hv)

theorem Invariant.done_eq_visited_of_stack_eq_nil {incidence : V → List V} {start : V}
    {state : State V} (hinv : Invariant incidence start state) (hstack : state.stack = []) :
    state.done = state.visited := by
  rw [hinv.visited_eq, hstack]
  simp

theorem invariant_initial (incidence : V → List V) (start : V) :
    Invariant incidence start ⟨{start}, ∅, [start]⟩ := by
  constructor <;> simp [Reachable.refl]

private theorem invariant_step (incidence : V → List V) (start v : V) (stack : List V)
    (state : State V) (hstate : state.stack = v :: stack)
    (hinv : Invariant incidence start state) :
    let popped := { state with stack }
    let scanned := (scan (incidence v) popped).ret
    Invariant incidence start { scanned with done := insert v scanned.done } := by
  rcases state with ⟨visited, done, stack'⟩
  simp only at hstate
  subst stack'
  let state : State V := ⟨visited, done, v :: stack⟩
  let popped : State V := { state with stack }
  let scanned := (scan (incidence v) popped).ret
  have hvvisited : v ∈ state.visited := hinv.stack_subset_visited v (by simp)
  have hstacksub : ∀ w ∈ stack, w ∈ popped.visited := by
    intro w hw
    exact hinv.stack_subset_visited w (by simp [hw])
  have hstacknodup : stack.Nodup := hinv.stack_nodup.tail
  have hvstack : v ∉ stack := hinv.stack_nodup.notMem
  constructor
  · exact nodup_ret_scan_stack _ _ hstacknodup hstacksub
  · exact stack_ret_scan_subset_visited _ _ hstacksub
  · rw [ret_scan_done, ret_scan_stack_toFinset]
    rw [Finset.disjoint_insert_left, Finset.disjoint_union_right]
    constructor
    · simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_sdiff, not_or]
      exact ⟨hvstack, fun h ↦ h.2 hvvisited⟩
    · constructor
      · exact hinv.done_disjoint_stack.mono_right (by simp)
      · rw [Finset.disjoint_left]
        intro w hdone hw
        rw [Finset.mem_sdiff] at hw
        exact hw.2 (hinv.visited_eq ▸ Finset.mem_union_left _ hdone)
  · rw [ret_scan_visited, ret_scan_done, ret_scan_stack_toFinset, hinv.visited_eq]
    ext w
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, List.mem_toFinset]
    by_cases hwv : w = v
    · grind
    · by_cases hwd : w ∈ done <;> by_cases hws : w ∈ stack <;> grind
  · intro w hw
    simp only at hw
    rw [ret_scan_visited] at hw
    simp only [Finset.mem_union, List.mem_toFinset] at hw
    rcases hw with hw | hw
    · exact hinv.reachable w hw
    · exact Reachable.tail incidence (hinv.reachable v hvvisited) hw
  · intro w hw x hx
    simp only at hw ⊢
    rw [ret_scan_done] at hw
    rw [ret_scan_visited]
    simp only [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact Finset.mem_union_right _ (List.mem_toFinset.2 hx)
    · exact Finset.mem_union_left _ (hinv.closed_done w hw x hx)

theorem invariant_loop (incidence : V → List V) (start : V) (fuel : ℕ) (state : State V)
    (hinv : Invariant incidence start state) :
    Invariant incidence start (loop incidence fuel state).ret := by
  induction fuel generalizing state with
  | zero => exact hinv
  | succ fuel ih =>
    rw [loop]
    cases hstack : state.stack with
    | nil => exact hinv
    | cons v stack =>
      simp only [TimeM.ret_bind]
      apply ih
      exact invariant_step incidence start v stack state hstack hinv

private theorem loop_done_card_of_stack_ne_nil (incidence : V → List V) (start : V)
    (fuel : ℕ) (state : State V) (hinv : Invariant incidence start state)
    (hne : (loop incidence fuel state).ret.stack ≠ []) :
    (loop incidence fuel state).ret.done.card = state.done.card + fuel := by
  induction fuel generalizing state with
  | zero => simp [loop]
  | succ fuel ih =>
    rcases state with ⟨visited, done, work⟩
    cases work with
    | nil => simp [loop] at hne
    | cons v stack =>
      let state : State V := ⟨visited, done, v :: stack⟩
      let popped : State V := ⟨visited, done, stack⟩
      let scanned := (scan (incidence v) popped).ret
      let next : State V := { scanned with done := insert v scanned.done }
      simp only [loop, TimeM.ret_bind] at hne ⊢
      have hnext : Invariant incidence start next :=
        invariant_step incidence start v stack state rfl hinv
      have hrec := ih next hnext hne
      have hvdone : v ∉ done := hinv.not_mem_done_of_mem_stack (by simp)
      have hdone : next.done.card = done.card + 1 := by
        dsimp only [next, scanned, popped]
        rw [ret_scan_done, Finset.card_insert_of_notMem hvdone]
      lia

private theorem stack_ret_runIncidence_eq_nil [Fintype V] (incidence : V → List V) (start : V) :
    (loop incidence (Fintype.card V) ⟨{start}, ∅, [start]⟩).ret.stack = [] := by
  let initial : State V := ⟨{start}, ∅, [start]⟩
  let result := (loop incidence (Fintype.card V) initial).ret
  have hinitial : Invariant incidence start initial := invariant_initial incidence start
  by_contra hne
  have hdone :=
    loop_done_card_of_stack_ne_nil incidence start (Fintype.card V) initial hinitial hne
  have hinv := invariant_loop incidence start (Fintype.card V) initial hinitial
  have hstackpos : 0 < result.stack.toFinset.card := by
    rw [Finset.card_pos]
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil result.stack hne
    exact ⟨v, List.mem_toFinset.2 hv⟩
  have hvisited : result.visited.card = result.done.card + result.stack.toFinset.card := by
    rw [hinv.visited_eq, Finset.card_union_of_disjoint hinv.done_disjoint_stack]
  have hcard : result.visited.card ≤ Fintype.card V := Finset.card_le_univ _
  dsimp only [initial] at hdone
  simp only [Finset.card_empty, zero_add] at hdone
  lia

theorem visited_subset_ret_loop (incidence : V → List V) (fuel : ℕ) (state : State V) :
    state.visited ⊆ (loop incidence fuel state).ret.visited := by
  induction fuel generalizing state with
  | zero => exact Finset.Subset.rfl
  | succ fuel ih =>
    rw [loop]
    cases state.stack with
    | nil => exact Finset.Subset.rfl
    | cons v stack =>
      simp only [TimeM.ret_bind]
      let popped : State V := { state with stack }
      let scanned := (scan (incidence v) popped).ret
      let next : State V := { scanned with done := insert v scanned.done }
      exact (visited_subset_ret_scan (incidence v) popped).trans (ih next)

/-- Incidence-function DFS visits exactly the vertices reachable from its starting vertex. -/
theorem mem_ret_runIncidence_iff_reachable [Fintype V]
    (incidence : V → List V) (start v : V) :
    v ∈ (runIncidence incidence start).ret ↔ Reachable incidence start v := by
  let initial : State V := ⟨{start}, ∅, [start]⟩
  let result := (loop incidence (Fintype.card V) initial).ret
  have hinitial : Invariant incidence start initial := invariant_initial incidence start
  have hinv := invariant_loop incidence start (Fintype.card V) initial hinitial
  have hstack := stack_ret_runIncidence_eq_nil incidence start
  have hdone := hinv.done_eq_visited_of_stack_eq_nil hstack
  have hclosed : ∀ u ∈ result.visited, ∀ w ∈ incidence u, w ∈ result.visited := by
    intro u hu w hw
    exact hinv.closed_done u (hdone ▸ hu) w hw
  have hstart : start ∈ result.visited := by
    apply visited_subset_ret_loop incidence (Fintype.card V) initial
    simp [initial]
  rw [ret_runIncidence]
  constructor
  · exact hinv.reachable v
  · intro hreach
    induction hreach with
    | refl => exact hstart
    | tail h hadj ih => exact hclosed _ ih _ hadj

/-- The amortized cost invariant for the tail-recursive loop. The left and right stack lengths
record unpaid future pop operations. -/
private theorem loop_time_invariant (incidence : V → List V) (start : V) (fuel : ℕ)
    (state : State V) (hinv : Invariant incidence start state) :
    (loop incidence fuel state).time + 2 * state.visited.card + edgeCount incidence state.done +
        (loop incidence fuel state).ret.stack.length =
      2 * (loop incidence fuel state).ret.visited.card +
        edgeCount incidence (loop incidence fuel state).ret.done + state.stack.length := by
  induction fuel generalizing state with
  | zero => simp [loop]
  | succ fuel ih =>
    rw [loop]
    cases hstack : state.stack with
    | nil => simp [hstack]
    | cons v stack =>
      simp only [TimeM.time_bind, TimeM.time_tick, TimeM.ret_bind]
      let popped : State V := { state with stack }
      let scanned := (scan (incidence v) popped).ret
      let next : State V := { scanned with done := insert v scanned.done }
      have hnext : Invariant incidence start next :=
        invariant_step incidence start v stack state hstack hinv
      have hrec := ih next hnext
      have hvdone : v ∉ state.done :=
        hinv.not_mem_done_of_mem_stack (by simp [hstack])
      have hnextdone : edgeCount incidence next.done =
          edgeCount incidence state.done + (incidence v).length := by
        dsimp only [next, scanned, popped]
        rw [ret_scan_done]
        simp [edgeCount, hvdone, Nat.add_comm]
      have hnextvisited : next.visited.card = state.visited.card +
          ((incidence v).toFinset \ state.visited).card := by
        exact card_visited_ret_scan _ _
      have hnextstack : next.stack.length = stack.length +
          ((incidence v).toFinset \ state.visited).card := by
        have htailnodup : stack.Nodup := by
          have hstacknodup := hinv.stack_nodup
          rw [hstack] at hstacknodup
          exact hstacknodup.tail
        have htailsub : ∀ w ∈ stack, w ∈ state.visited := by
          intro w hw
          exact hinv.stack_subset_visited w (by rw [hstack]; exact List.mem_cons_of_mem v hw)
        exact length_ret_scan_stack _ _ htailnodup htailsub
      have hstatelen : state.stack.length = stack.length + 1 := by simp [hstack]
      rw [time_scan]
      dsimp only [next, scanned, popped] at hrec hnextdone hnextvisited hnextstack ⊢
      simp only [List.length_cons] at hstatelen ⊢
      lia

/-- Exact DFS cost: two stack operations per visited vertex, plus one tick for every adjacency-list
entry scanned in the connected component of `start`. -/
theorem runIncidence_time_eq [Fintype V] (incidence : V → List V) (start : V) :
    (runIncidence incidence start).time =
      2 * (runIncidence incidence start).ret.card +
        edgeCount incidence (runIncidence incidence start).ret := by
  let initial : State V := ⟨{start}, ∅, [start]⟩
  let result := (loop incidence (Fintype.card V) initial).ret
  have hinitial : Invariant incidence start initial := invariant_initial incidence start
  have hcost := loop_time_invariant incidence start (Fintype.card V) initial hinitial
  have hstack := stack_ret_runIncidence_eq_nil incidence start
  have hinv := invariant_loop incidence start (Fintype.card V) initial hinitial
  have hdone := hinv.done_eq_visited_of_stack_eq_nil hstack
  rw [time_runIncidence, ret_runIncidence]
  simp only [initial, Finset.card_singleton, mul_one, edgeCount_empty,
    List.length_singleton, hstack, List.length_nil, add_zero] at hcost
  rw [hdone] at hcost
  lia

end Algorithm

section Graph

variable {α β : Type*}

/-- The other endpoint of an edge incident with a vertex. -/
noncomputable def graphOther (G : Graph α β) (v : V(G)) (e : β)
    (h : G.Inc e v) : V(G) :=
  ⟨h.other, h.inc_other.vertex_mem⟩

@[simp]
private theorem graphOther_spec (G : Graph α β) (v : V(G)) (e : β) (h : G.Inc e v) :
    G.IsLink e v (graphOther G v e h) :=
  h.isLink_other

/-- The incidence list generated from all graph edges at a vertex. -/
noncomputable def graphIncidence (G : Graph α β) [Finite E(G)] : V(G) → List V(G) := by
  let _ := Fintype.ofFinite E(G)
  classical
  exact fun v ↦ (Finset.univ : Finset E(G)).toList.flatMap fun e ↦
    if h : G.Inc e.1 v.1 then [graphOther G v e.1 h] else []

@[simp]
theorem mem_graphIncidence (G : Graph α β) [Finite E(G)] (u v : V(G)) :
    u ∈ graphIncidence G v ↔ G.Adj v.1 u.1 := by
  let _ := Fintype.ofFinite E(G)
  classical
  simp only [graphIncidence, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and]
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

/-- Run depth-first search from `start`, constructing each vertex's incidence list directly from
the finite Mathlib graph. -/
noncomputable def run (G : Graph α β) [Finite V(G)] [Finite E(G)] [DecidableEq V(G)]
    (start : V(G)) : TimeM ℕ (Finset V(G)) := by
  let _ := Fintype.ofFinite V(G)
  let _ := Fintype.ofFinite E(G)
  classical
  let incidence : V(G) → List V(G) := fun v ↦
    (Finset.univ : Finset E(G)).toList.flatMap fun e ↦
      if h : G.Inc e.1 v.1 then [graphOther G v e.1 h] else []
  exact runIncidence incidence start

/-- The number of graph-incidence entries belonging to a set of vertices. Parallel edge
occurrences are counted separately. -/
noncomputable def incidenceCount (G : Graph α β) [Finite E(G)] (vertices : Finset V(G)) : ℕ := by
  exact edgeCount (graphIncidence G) vertices

/-- DFS visits exactly the vertices in the connected component of its starting vertex. -/
theorem mem_ret_run_iff_reachable (G : Graph α β) [Finite V(G)] [Finite E(G)]
    [DecidableEq V(G)] (start v : V(G)) :
    v ∈ (run G start).ret ↔
      Relation.ReflTransGen (fun u w : V(G) ↦ G.Adj u.1 w.1) start v := by
  let _ := Fintype.ofFinite V(G)
  let _ := Fintype.ofFinite E(G)
  classical
  unfold run
  rw [mem_ret_runIncidence_iff_reachable]
  rw [show (fun v ↦ (Finset.univ : Finset E(G)).toList.flatMap fun e ↦
    if h : G.Inc e.1 v.1 then [graphOther G v e.1 h] else []) = graphIncidence G from rfl]
  simp only [Reachable, mem_graphIncidence]

/-- Exact DFS cost: two stack operations per visited vertex, plus one tick for every incidence
entry scanned in the starting component. -/
theorem run_time_eq (G : Graph α β) [Finite V(G)] [Finite E(G)] [DecidableEq V(G)]
    (start : V(G)) :
    (run G start).time =
      2 * (run G start).ret.card + incidenceCount G (run G start).ret := by
  let _ := Fintype.ofFinite V(G)
  let _ := Fintype.ofFinite E(G)
  classical
  unfold run incidenceCount graphIncidence
  exact runIncidence_time_eq _ start

/-- If every vertex is reachable from `start`, DFS has global cost
`2 * |V| +` the number of graph-incidence entries. -/
theorem run_time_eq_of_all_reachable (G : Graph α β) [Finite V(G)] [Finite E(G)]
    [Fintype V(G)] [DecidableEq V(G)] (start : V(G))
    (hconnected : ∀ v, Relation.ReflTransGen (fun u w : V(G) ↦ G.Adj u.1 w.1) start v) :
    (run G start).time = 2 * Fintype.card V(G) + incidenceCount G Finset.univ := by
  have hvisited : (run G start).ret = Finset.univ := by
    ext v
    simp only [Finset.mem_univ, iff_true]
    exact (mem_ret_run_iff_reachable G start v).2 (hconnected v)
  rw [run_time_eq, hvisited, Finset.card_univ]

end Graph

end DFS
end Cslib.Algorithms.Lean.GraphAlgorithms
