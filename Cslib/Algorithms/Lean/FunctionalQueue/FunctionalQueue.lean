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

namespace Raw

/-- Well-formedness: if front is empty, back must be empty too. -/
def invariant {α : Type u} (q : RawFunctionalQueue α) : Prop :=
  q.front = [] → q.back = []

/-- The logical contents of the queue: `front ++ back.reverse`. -/
def ghostList {α : Type u} (q : RawFunctionalQueue α) : List α :=
  List.append q.front q.back.reverse

/-- The empty queue. -/
def emptyRaw {α : Type u} : RawFunctionalQueue α := ⟨ [], [] ⟩

/-- Internal: rebalance by moving `back.reverse` to `front` when `front` is empty. -/
def rebalance {α : Type u} (q : RawFunctionalQueue α) : RawFunctionalQueue α :=
  match q.front with
  | [] => ⟨ (q.back).reverse, [] ⟩
  | _ => q

theorem rebalanceInvert {α : Type u} (q : RawFunctionalQueue α) :
    (rebalance q).front = [] → q = emptyRaw := by
  intro h
  obtain ⟨f, b⟩ := q
  simp only [rebalance, emptyRaw] at h ⊢
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
def pushRaw {α : Type u} (x : α) (q : RawFunctionalQueue α) : RawFunctionalQueue α :=
  rebalance ⟨ q.front, x :: q.back ⟩

theorem pushInvariant {α : Type u} (x : α) (q : RawFunctionalQueue α) :
    invariant q → invariant (pushRaw x q) := by
  intro h
  rw [pushRaw]
  apply rebalanceInvariant

theorem pushGhost {α : Type u} (x : α) (q : RawFunctionalQueue α) :
    ghostList (pushRaw x q) = ghostList q ++ [x] := by
  rw [pushRaw, rebalancePreserveGhost, ghostList]
  simp [ghostList, List.append_assoc]

/-- Dequeue: returns `some (head, remaining)` or `none` if empty. -/
def popRaw {α : Type u} (q : RawFunctionalQueue α) : Option (α × RawFunctionalQueue α) :=
  match q.front with
  | [] => none
  | x :: tl =>
    some (x, rebalance ⟨ tl, q.back ⟩)

theorem popInvariant {α : Type u} (x : α) (q q2 : RawFunctionalQueue α) :
    invariant q → popRaw q = some (x, q2) → invariant q2 := by
  intro hq hpop
  obtain ⟨f, b⟩ := q
  simp [invariant] at hq
  unfold popRaw at hpop
  cases f with
  | nil => simp at hpop
  | cons y tl =>
    simp only at hpop
    obtain ⟨rfl, rfl⟩ := hpop
    exact rebalanceInvariant

@[simp] theorem emptyInvariant {α : Type u} : invariant (@emptyRaw α) := by
  simp [invariant, emptyRaw]

@[simp] theorem emptyGhost {α : Type u} : ghostList (@emptyRaw α) = [] := by
  simp [ghostList, emptyRaw]

theorem popGhost {α : Type u} {x : α} {q q2 : RawFunctionalQueue α} :
    invariant q → popRaw q = some (x, q2) → ghostList q = x :: ghostList q2 := by
  intro hq hpop
  obtain ⟨f, b⟩ := q
  simp [invariant] at hq
  unfold popRaw at hpop
  cases f with
  | nil => simp at hpop
  | cons y tl =>
    simp only at hpop
    obtain ⟨rfl, rfl⟩ := hpop
    simp only [rebalancePreserveGhost]
    simp [ghostList]

end Raw

/-- A functional queue with invariant. -/
structure FunctionalQueue (α : Type u) where
  q : RawFunctionalQueue α
  inv : Raw.invariant q

def empty {α : Type u} : FunctionalQueue α := ⟨ @Raw.emptyRaw α, Raw.emptyInvariant ⟩

def push {α : Type u} (x : α) (q : FunctionalQueue α) : FunctionalQueue α :=
  ⟨ Raw.pushRaw x q.q, Raw.pushInvariant x q.q q.inv ⟩

def pop {α : Type u} (q : FunctionalQueue α) : Option (α × FunctionalQueue α) :=
  match h : Raw.popRaw q.q with
  | none => none
  | some (x, q2) =>
    some (x, ⟨ q2, Raw.popInvariant x q.q q2 q.inv h ⟩)

@[simp] def ghostList {α : Type u} (q : FunctionalQueue α) : List α := Raw.ghostList q.q

theorem pushGhost {α : Type u} (x : α) (q : FunctionalQueue α) :
    ghostList (push x q) = ghostList q ++ [x] :=
  Raw.pushGhost x q.q

theorem popGhost {α : Type u} {x : α} {q q2 : FunctionalQueue α} :
    pop q = some (x, q2) → ghostList q = x :: ghostList q2 := by
  intro h
  simp only [pop, ghostList] at h ⊢
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i x2 q2' heq
    obtain ⟨ h1, h2 ⟩ := h
    apply @Raw.popGhost α x q.q q2' q.inv; grind

end Cslib.Algorithms.Lean
