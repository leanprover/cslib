/-
Copyright (c) 2026 Simon Cruanes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Cruanes
-/

module

import Cslib.Init
import Mathlib
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Cslib.Algorithms.Lean.Amortized
public import Cslib.Algorithms.Lean.TimeM

/-!
# Functional Queue

A classic two-list queue with amortized O(1) `push` and `pop`.

The representation uses two lists: a front list (for dequeue) and a back list
(for enqueue). When the front list becomes empty, the back list is reversed
and becomes the new front. This yields amortized O(1) operations.

Cost model: each list cons is worth one `TimeM` tick.

## References

* [Okasaki, *Purely Functional Data Structures*, 1996][okasaki1996]
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

@[expose] public section

universe u

namespace Raw

structure FunctionalQueue (α : Type u) where
  front : List α
  back : List α

/-- Well-formedness: if front is empty, back must be empty too. -/
def Invariant {α : Type u} (q : Raw.FunctionalQueue α) : Prop :=
  q.front = [] → q.back = []

/-- The logical contents of the queue: `front ++ back.reverse`. -/
def toList {α : Type u} (q : FunctionalQueue α) : List α :=
  q.front ++ q.back.reverse

/-- The empty queue. -/
def empty {α : Type u} : FunctionalQueue α := ⟨ [], [] ⟩

/-- Internal: rebalance by moving `back.reverse` to `front` when `front` is empty. -/
def rebalance {α : Type u} (q : FunctionalQueue α)
    : TimeM ℕ (FunctionalQueue α) :=
  match q.front with
  | [] => do
    TimeM.tick q.back.length
    pure ⟨ (q.back).reverse, [] ⟩
  | _ => pure q

theorem rebalanceInvert {α : Type u} (q : FunctionalQueue α) :
    (rebalance q).ret.front = [] → q = empty := by
  intro h
  obtain ⟨f, b⟩ := q
  simp only [rebalance, Raw.empty] at h ⊢
  split at h <;> simp_all

theorem rebalanceInvariant {α : Type u} {q : FunctionalQueue α} :
    Invariant (rebalance q).ret := by
  obtain ⟨f, b⟩ := q
  simp [rebalance, Invariant]
  split <;> grind

@[simp] theorem rebalanceIdempotent {α : Type u} (q : FunctionalQueue α) :
    (rebalance (rebalance q).ret).ret = (rebalance q).ret := by
  obtain ⟨f, b⟩ := q
  simp [rebalance]
  split <;> grind

@[simp] theorem rebalancePreserveGhost {α : Type u} (q : FunctionalQueue α) :
    toList (rebalance q).ret = toList q := by
  obtain ⟨f, b⟩ := q
  simp [rebalance, toList]
  split <;> grind [List.reverse_append]

/-- Enqueue an element. -/
def push {α : Type u} (x : α) (q : FunctionalQueue α)
    : TimeM ℕ (FunctionalQueue α) := do
  TimeM.tick 1
  rebalance ⟨ q.front, x :: q.back ⟩

theorem Invariant.push {α : Type u} (x : α) (q : FunctionalQueue α)
    : Invariant q → Invariant (push x q).ret := by
  intro h
  rw [Raw.push]
  apply rebalanceInvariant

theorem pushToList {α : Type u} (x : α) (q : Raw.FunctionalQueue α)
    : toList (push x q).ret = toList q ++ [x] := by
  rw [push]
  simp only [TimeM.ret_bind, rebalancePreserveGhost]
  rw [toList]
  simp [toList, List.append_assoc]

/-- Dequeue: returns `some (head, remaining)` or `none` if empty. -/
def pop {α : Type u} (q : Raw.FunctionalQueue α)
    : TimeM ℕ (Option (α × Raw.FunctionalQueue α)) :=
  match q.front with
  | [] => pure none
  | x :: tl => do
    let q2 ← rebalance ⟨ tl, q.back ⟩
    pure (some (x, q2))

theorem Invariant.pop {α : Type u} (x : α) (q q2 : FunctionalQueue α)
    : Invariant q →
      (pop q).ret = some (x, q2) →
      Invariant q2 := by
  intro hq hpop
  obtain ⟨f, b⟩ := q
  simp [Invariant] at hq
  unfold Raw.pop at hpop
  cases f with
  | nil => simp at hpop
  | cons y tl =>
    simp only at hpop
    obtain ⟨rfl, rfl⟩ := hpop
    exact rebalanceInvariant

@[simp] theorem Invariant.empty {α : Type u} : Invariant (@Raw.empty α) := by
  simp [Invariant, Raw.empty]

@[simp] theorem emptyToList {α : Type u} : toList (@Raw.empty α) = [] := by
  simp [toList, Raw.empty]

theorem popToList {α : Type u} {x : α} {q q2 : Raw.FunctionalQueue α}
    : Invariant q →
      (pop q).ret = some (x, q2) →
      toList q = x :: toList q2 := by
  intro hq hpop
  obtain ⟨f, b⟩ := q
  simp [Invariant] at hq
  unfold pop at hpop
  cases f with
  | nil => simp at hpop
  | cons y tl =>
    simp only at hpop
    obtain ⟨rfl, rfl⟩ := hpop
    simp only [rebalancePreserveGhost]
    simp [toList]

end Raw

namespace Complexity

def potential {α : Type u} (q : Raw.FunctionalQueue α) : ℤ :=
  q.back.length

instance functionalQueuePotential {α : Type u}
    : Amortized.Potential ℤ (Raw.FunctionalQueue α) :=
  ⟨ potential ⟩

inductive queueOp (α : Type u) where
  | push : α → queueOp α
  | pop

def applyOp {α : Type u} (q : Raw.FunctionalQueue α) (op : queueOp α)
    : TimeM ℕ (Raw.FunctionalQueue α) :=
  match op with
  | .push x => Raw.push x q
  | .pop => do
    match (← Raw.pop q) with
    | none => pure q
    | some (_, q2) => pure q2

theorem potentialEmptyIsZero {α : Type u}
    : potential (@Raw.empty α) = 0 := by
  simp [potential, Raw.empty]

theorem amortizedCostQueueOp {α : Type u} (q : Raw.FunctionalQueue α) (op : queueOp α)
    : Amortized.amortizedCost q (fun q => applyOp q op) ≤ (2 : ℤ) := by
  simp only [Amortized.amortizedCost, Amortized.Potential.potential, tsub_le_iff_right]
  cases op with
  | push x =>
    simp only [applyOp, potential]
    cases h_front : q.front <;> (rw [Raw.push, Raw.rebalance, h_front] at ⊢; grind)
  | pop =>
    simp only [applyOp, potential]
    cases h_front : q.front <;> (rw [Raw.pop, h_front] at ⊢; grind [Raw.rebalance])

/-- cost of applying operations to a queue -/
theorem costQueueOps {α : Type u}
    (q : Raw.FunctionalQueue α) (ops : List (queueOp α))
    : (List.foldlM (fun q op => applyOp q op) q ops).time
        + potential (List.foldlM (fun q op => applyOp q op) q ops).ret
        - potential q
      ≤ (2 : ℤ) * ops.length
    := by
  have h_bound (x : Raw.FunctionalQueue α) (op : queueOp α)
      : (applyOp x op).time + potential (applyOp x op).ret - potential x ≤ (2 : ℤ) :=
    amortizedCostQueueOp x op
  revert q
  induction ops with
  | nil => intro q; simp
  | cons op ops2 ih =>
    intro q
    simp only [List.foldlM, TimeM.time_bind, Nat.cast_add, TimeM.ret_bind,
      List.length_cons, Nat.cast_one]
    have step := h_bound q op
    have rest := ih (applyOp q op).ret
    linarith

end Complexity

/-- A functional queue with invariant. -/
@[ext]
structure FunctionalQueue (α : Type u) where
  raw : Raw.FunctionalQueue α
  inv : Raw.Invariant raw

def empty {α : Type u} : FunctionalQueue α := ⟨ @Raw.empty α, Raw.Invariant.empty ⟩

def push {α : Type u} (x : α) (q : FunctionalQueue α)
    : TimeM ℕ (FunctionalQueue α) :=
  let r := Raw.push x q.raw
  ⟨ ⟨ r.ret, Raw.Invariant.push x q.raw q.inv ⟩, r.time ⟩

def pop {α : Type u} (q : FunctionalQueue α)
    : TimeM ℕ (Option (α × FunctionalQueue α)) :=
  let r := Raw.pop q.raw
  match h : r.ret with
  | none => ⟨ none, r.time ⟩
  | some (x, q2) =>
    ⟨ some (x, ⟨ q2, Raw.Invariant.pop x q.raw q2 q.inv h ⟩), r.time ⟩

/-- project to a list view, an ordered sequence of elements -/
def toList {α : Type u} (q : FunctionalQueue α) : List α := Raw.toList q.raw

theorem pushGhost {α : Type u} (x : α) (q : FunctionalQueue α) :
    toList (push x q).ret = toList q ++ [x] :=
  Raw.pushToList x q.raw

theorem popGhost {α : Type u} {x : α} {q2 : FunctionalQueue α} :
    ∀ {q : FunctionalQueue α},
    (pop q).ret = some (x, q2) → toList q = x :: toList q2 := by
  intro q h
  simp only [pop, toList] at h ⊢
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i x2 q2' heq
    obtain ⟨h1, h2⟩ := h
    exact @Raw.popToList α x q.raw q2' q.inv heq

end

end Cslib.Algorithms.Lean
