/-
Copyright (c) 2026 Simon Cruanes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Cruanes
-/

module

import Cslib.Init
public import Cslib.Algorithms.Lean.Amortized

/-!
# Functional Queue

A classic two-list queue with amortized O(1) `push` and `pop`.

The representation uses two lists: a front list (for dequeue) and a back list
(for enqueue). When the front list becomes empty, the back list is reversed
and becomes the new front. This yields amortized O(1) operations.

## References

* [Okasaki, *Purely Functional Data Structures*, 1996][okasaki1996]
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

@[expose] public section

universe u

structure RawFunctionalQueue (α : Type u) where
  front : List α
  back : List α

namespace Raw

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
    (rebalance q).front = [] → q = Raw.empty := by
  intro h
  obtain ⟨f, b⟩ := q
  simp only [rebalance, Raw.empty] at h ⊢
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

theorem popInvariant {α : Type u} (x : α) (q q2 : RawFunctionalQueue α) :
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

@[simp] theorem emptyInvariant {α : Type u} : invariant (@Raw.empty α) := by
  simp [invariant, Raw.empty]

@[simp] theorem emptyGhost {α : Type u} : ghostList (@Raw.empty α) = [] := by
  simp [ghostList, Raw.empty]

theorem popGhost {α : Type u} {x : α} {q q2 : RawFunctionalQueue α} :
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

end Raw

namespace Complexity

def potential {α : Type u} (q : RawFunctionalQueue α) : Nat :=
  q.back.length

instance functionalQueuePotential {α : Type u}
    : Amortized.Potential (RawFunctionalQueue α) :=
  ⟨ potential ⟩

inductive queueOp (α : Type u) where
  | push : α → queueOp α
  | pop

def applyOp {α : Type u} (op : queueOp α) (q : RawFunctionalQueue α) : RawFunctionalQueue α :=
  match op with
  | .push x => Raw.push x q
  | .pop =>
    match Raw.pop q with
    | none => q
    | some (_, q2) => q2

def applyOps {α : Type u} (ops : List (queueOp α)) (q : RawFunctionalQueue α)
    : RawFunctionalQueue α :=
  ops.foldl (fun q op => applyOp op q) q

theorem constantTimeAmortized {α : Type u} :
    ∀ (q : RawFunctionalQueue α) (ops:List (queueOp α)),
    false
 := by
   sorry

end Complexity

/-- A functional queue with invariant. -/
@[ext]
structure FunctionalQueue (α : Type u) where
  raw : RawFunctionalQueue α
  inv : Raw.invariant raw

def empty {α : Type u} : FunctionalQueue α := ⟨ @Raw.empty α, Raw.emptyInvariant ⟩

def push {α : Type u} (x : α) (q : FunctionalQueue α) : FunctionalQueue α :=
  ⟨ Raw.push x q.raw, Raw.pushInvariant x q.raw q.inv ⟩

def pop {α : Type u} (q : FunctionalQueue α) : Option (α × FunctionalQueue α) :=
  match h : Raw.pop q.raw with
  | none => none
  | some (x, q2) =>
    some (x, ⟨ q2, Raw.popInvariant x q.raw q2 q.inv h ⟩)

/-- project to a list view, an ordered sequence of elements -/
def ghostList {α : Type u} (q : FunctionalQueue α) : List α := Raw.ghostList q.raw

theorem pushGhost {α : Type u} (x : α) (q : FunctionalQueue α) :
    ghostList (push x q) = ghostList q ++ [x] :=
  Raw.pushGhost x q.raw

theorem popGhost {α : Type u} {x : α} {q q2 : FunctionalQueue α} :
    pop q = some (x, q2) → ghostList q = x :: ghostList q2 := by
  intro h
  simp only [pop, ghostList] at h ⊢
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i x2 q2' heq
    obtain ⟨h1, h2⟩ := h
    exact @Raw.popGhost α x q.raw q2' q.inv heq

end

end Cslib.Algorithms.Lean
