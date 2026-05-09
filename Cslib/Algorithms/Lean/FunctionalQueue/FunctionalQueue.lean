

module

/- public import Cslib.Algorithms.Lean.TimeM -/

/-!
  The simplest functional queue. -/

@[expose] public section

namespace Cslib.Algorithms.Lean

universe u

@[ext] structure RawFunctionalQueue (α : Type u) where
  front : List α
  back : List α

@[simp] def invariant {α : Type u} (q : RawFunctionalQueue α) : Prop :=
  q.front = [] → q.back = []

@[simp] def ghostList {α : Type u} (q : RawFunctionalQueue α) : List α :=
  List.append q.front q.back.reverse

def empty {α : Type u} : RawFunctionalQueue α := ⟨ [], [] ⟩

def rebalance {α : Type u} (q : RawFunctionalQueue α) : RawFunctionalQueue α :=
  match q.front with
  | [] => ⟨ (q.back).reverse, [] ⟩
  | _ => q

theorem rebalanceInvert {α : Type u} (q : RawFunctionalQueue α) : (rebalance q).front = [] → q = empty := by
  intro h_reb
  rw [empty]
  generalize gen_reb : (rebalance q).front = q_reb_hd
  obtain ⟨ q_hd, q_tl ⟩ := q
  simp [rebalance] at h_reb
  induction q_reb_hd with
  | nil =>
    induction q_hd with
    | nil =>
      simp at h_reb; simp [rebalance] at gen_reb; rw [h_reb]
    | cons q_hd_hd q_hd_tl q_hd_hyp =>
      grind only
  | cons q_reb_hd_hd q_reb_hd_tl q_reb_hd_hyp =>
    induction q_hd with
    | nil =>
      simp at h_reb
      grind only
    | cons _ _ _ =>
      simp at h_reb

@[simp] theorem rebalanceInvariant {α : Type u} {q : RawFunctionalQueue α} : invariant (rebalance q) := by
  generalize h_front : q.front = l
  induction l with
  | nil => simp [rebalance]; rw [h_front]; simp
  | cons x tl h_cons =>
    simp [rebalance]; rw [h_front]; simp; rw [h_front]; grind only

@[simp] theorem rebalanceIdempotent {α : Type u} (q : RawFunctionalQueue α) : rebalance (rebalance q) = rebalance q := by
  generalize h : (rebalance q).front = hd
  induction hd with
  | nil =>
    have h_q_empty : q = empty := rebalanceInvert q h
    simp [rebalance]; rw [h_q_empty]; simp [empty]
  | cons hd_hd hd_tl hd_hyp =>
    generalize def_q2 : rebalance q = q2
    rw [def_q2] at h
    simp [rebalance]
    rw [h]

@[simp] theorem rebalancePreserveGhost {α : Type u} (q : RawFunctionalQueue α) : ghostList (rebalance q) = ghostList q := by
  generalize def_hd : q.front = hd
  induction hd with
  | nil => simp [rebalance]; rw [def_hd]; simp
  | cons hd_hd hd_tl h_ind =>
    simp [rebalance]; rw [def_hd]; simp; grind only [=_ List.cons_append]

def push {α : Type u} (x : α) (q : RawFunctionalQueue α) : (RawFunctionalQueue α) :=
  let q : RawFunctionalQueue α := ⟨ q.front, x :: q.back ⟩
  rebalance q

theorem appendInvariant {α : Type u} (x : α) (q : RawFunctionalQueue α)
  : invariant q → invariant (push x q) := by
  intro h
  rw [push]
  apply rebalanceInvariant

theorem appendGhost {α : Type u} (x : α) (q : RawFunctionalQueue α) : ghostList (push x q) = ghostList q ++ [x] := by
  generalize h_front : q.front = l
  cases l with
  | nil =>
    simp [push, rebalance]; rw [h_front]; simp
  | cons l_hd l_tl =>
    rw [push]
    rw [rebalancePreserveGhost]
    rw [ghostList]
    simp

def pop {α : Type u} (q : RawFunctionalQueue α) : Option (α × RawFunctionalQueue α) :=
  match q.front with
  | [] => none
  | x :: tl =>
    some (x, rebalance ⟨ tl, q.back ⟩)

theorem pop_invariant {α : Type u} (x : α) (q q2 : RawFunctionalQueue α) :
    invariant q → pop q = some (x, q2) → invariant q2 := by
  intro hq hpop_is_some
  simp at hq
  rw [pop] at hpop_is_some
  generalize h_front : q.front = l
  cases l with
  | nil =>
    rw [h_front] at hpop_is_some; simp at hpop_is_some
  | cons _ _ =>
    rw [h_front] at hpop_is_some
    simp only at hpop_is_some
    obtain ⟨ rfl, rfl ⟩ := hpop_is_some
    apply rebalanceInvariant

end Cslib.Algorithms.Lean
