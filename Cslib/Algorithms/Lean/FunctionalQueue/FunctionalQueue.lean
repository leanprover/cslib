/-
Copyright (c) 2026 Simon Cruanes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Cruanes
-/

module

import Cslib.Init

/-!
# Functional Queue

A classic two-list queue with amortized O(1) `push` and `pop`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

@[ext] structure RawFunctionalQueue (α : Type u) where
  front : List α
  back : List α

/-- Well-formedness: if front is empty, back must be empty too. -/
def invariant {α : Type u} (q : RawFunctionalQueue α) : Prop :=
  q.front = [] → q.back = []

/-- The logical contents of the queue: `front ++ back.reverse`. -/
def ghostList {α : Type u} (q : RawFunctionalQueue α) : List α :=
  List.append q.front q.back.reverse

/-- The empty queue. -/
def empty {α : Type u} : RawFunctionalQueue α := ⟨ [], [] ⟩

/-- Internal: rebalance by moving `back.reverse` to `front` when `front` is empty. -/
def rebalance {α : Type u} (q : RawFunctionalQueue α) : RawFunctionalQueue α :=
  match q.front with
  | [] => ⟨ (q.back).reverse, [] ⟩
  | _ => q

theorem rebalanceInvert {α : Type u} (q : RawFunctionalQueue α) :
    (rebalance q).front = [] → q = empty := by
  intro h
  obtain ⟨f, b⟩ := q
  simp only [rebalance, empty] at h ⊢
  split at h <;> simp_all

theorem rebalanceInvariant {α : Type u} {q : RawFunctionalQueue α} :
    invariant (rebalance q) := by
  obtain ⟨f, b⟩ := q
  simp [rebalance, invariant]
  split <;> grind

@[simp] theorem rebalanceIdempotent {α : Type u} (q : RawFunctionalQueue α) :
    rebalance (rebalance q) = rebalance q := by
  obtain ⟨f, b⟩ := q
  simp [rebalance]
  split <;> grind

@[simp] theorem rebalancePreserveGhost {α : Type u} (q : RawFunctionalQueue α) :
    ghostList (rebalance q) = ghostList q := by
  obtain ⟨f, b⟩ := q
  simp [rebalance, ghostList]
  split <;> grind [List.reverse_append]

/-- Enqueue an element. -/
def push {α : Type u} (x : α) (q : RawFunctionalQueue α) : RawFunctionalQueue α :=
  rebalance ⟨ q.front, x :: q.back ⟩

theorem pushInvariant {α : Type u} (x : α) (q : RawFunctionalQueue α) :
    invariant q → invariant (push x q) := by
  intro h
  rw [push]
  apply rebalanceInvariant

theorem pushGhost {α : Type u} (x : α) (q : RawFunctionalQueue α) :
    ghostList (push x q) = ghostList q ++ [x] := by
  rw [push, rebalancePreserveGhost, ghostList]
  simp [ghostList, List.append_assoc]

/-- Dequeue: returns `some (head, remaining)` or `none` if empty. -/
def pop {α : Type u} (q : RawFunctionalQueue α) : Option (α × RawFunctionalQueue α) :=
  match q.front with
  | [] => none
  | x :: tl =>
    some (x, rebalance ⟨ tl, q.back ⟩)

theorem pop_invariant {α : Type u} (x : α) (q q2 : RawFunctionalQueue α) :
    invariant q → pop q = some (x, q2) → invariant q2 := by
  intro hq hpop
  obtain ⟨f, b⟩ := q
  simp [invariant] at hq
  unfold pop at hpop
  cases f with
  | nil => simp at hpop
  | cons y tl =>
    simp only at hpop
    obtain ⟨rfl, rfl⟩ := hpop
    exact rebalanceInvariant

@[simp] theorem emptyInvariant {α : Type u} : invariant (@empty α) := by
  simp [invariant, empty]

@[simp] theorem emptyGhost {α : Type u} : ghostList (@empty α) = [] := by
  simp [ghostList, empty]

theorem pop_ghost {α : Type u} {x : α} {q q2 : RawFunctionalQueue α} :
    invariant q → pop q = some (x, q2) → ghostList q = x :: ghostList q2 := by
  intro hq hpop
  obtain ⟨f, b⟩ := q
  simp [invariant] at hq
  unfold pop at hpop
  cases f with
  | nil => simp at hpop
  | cons y tl =>
    simp only at hpop
    obtain ⟨rfl, rfl⟩ := hpop
    simp only [rebalancePreserveGhost]
    simp [ghostList]

end Cslib.Algorithms.Lean
