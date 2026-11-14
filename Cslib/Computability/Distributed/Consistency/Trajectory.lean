/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.Consistency.Encodable
public import Cslib.Computability.Distributed.Consistency.Specification
public import Cslib.Computability.Distributed.Consistency.Transition

/-! # Trajectories

A trajectory is the sequence of events corresponding to the transitions executed by a role.
Various well-formedness conditions are imposed on trajectories.

This file formalizes section 7.2 of [Burckhardt2014].

## References

* [*Principles of Eventual Consistency*][Burckhardt2014]
-/

@[expose] public section

namespace Cslib.DistributedConsistency

open Encodable

variable {Event State Operation Value Message Process Role : Type*}

/-- Trajectory structure. -/
structure Trajectory (Event State Operation Value Message Process : Type*) where
  /-- `eo` is the execution order over events. -/
  [eo : Encodable Event]
  /-- `tr` assigns each event its transition. -/
  tr : Event → Transition State Operation Value Message Process

namespace Trajectory

variable (traj : Trajectory Event State Operation Value Message Process)

/-- The strict execution order. -/
abbrev lt := traj.eo.lt

/-- The non-strict execution order. -/
abbrev le := traj.eo.le

/-- The predecessor event according to the execution order. -/
noncomputable abbrev pred := traj.eo.pred

/-- The operation of an event. -/
abbrev op (x : Event) := (traj.tr x).op

/-- The received message of an event. -/
abbrev rcv (x : Event) := (traj.tr x).rcv

/-- The process of an event. -/
abbrev proc (x : Event) := (traj.tr x).proc

/-- The previous state of an event. -/
abbrev pre (x : Event) := (traj.tr x).pre

/-- The next state of an event. -/
abbrev post (x : Event) := (traj.tr x).post

/-- The set of messages sent by an event. -/
abbrev snd (x : Event) := (traj.tr x).snd

/-- The value returned by an event. -/
abbrev rval (x : Event) := (traj.tr x).rval

/-- An event is considered a call iff it has an operation. -/
abbrev isCall (x : Event) := (traj.tr x).op.isSome

/-- An event is considered a return iff it has a return value. -/
abbrev isReturn (x : Event) := (traj.tr x).rval.isSome

/-- The well-formedness conditions on a trajectory.
NOTE: In [Burckhardt2014], this is conditions "t3" and "t4" in the definition of a trajectory. -/
structure WellFormed : Prop where
  /-- The first event has no previous state.  Every subsequent event has its previous state
  matching the next state of its predecessor event. -/
  state_sequence (x : Event) :
    (traj.pred x = x ∧ traj.pre x = none) ∨
    (traj.lt (traj.pred x) x ∧ traj.pre x = traj.post (traj.pred x))
  /-- Between any two calls there must be a return, which may be the same event as
  the first call. -/
  call_return_call (x y : Event) :
    traj.lt x y → traj.isCall x → traj.isCall y →
    ∃ z, traj.isReturn z ∧ traj.le x z ∧ traj.lt z y

/-- The return well-formedness condition on a trajectory, which says that
each event is preceded by no more returns than calls.
NOTE: In [Burckhardt2014], this is called the well-formedness condition of a trajectory. -/
def ReturnWellFormed : Prop :=
  ∀ x, {y | traj.le y x ∧ traj.isReturn y}.ncard ≤ {y | traj.le y x ∧ traj.isCall y}.ncard

/-- Lemma 7.1 of [Burckhardt2014]: if all calls return immediately,
then the trajectory is return well-formed. -/
theorem isCall_eq_isReturn_returnWellFormed
    (h : traj.isCall = traj.isReturn) : traj.ReturnWellFormed := by
  intro x
  rw [h]

/-- The set of returns succeeding an event (according to the non-strict execution order). -/
def returnsAfter (x : Event) : Set Event := {y | traj.le x y ∧ traj.isReturn y}

open Classical in
/-- The return event of an event is the least return event succeeding it, if it exists. -/
noncomputable def returnOf (x : Event) : Option Event :=
  if h : (traj.returnsAfter x).Nonempty then
    some (WellFounded.min (lt_wellFounded (en := traj.eo)) (traj.returnsAfter x) h)
  else none

theorem self_le_returnOf {x y : Event} (h : traj.returnOf x = some y) : traj.le x y := by
  rw [returnOf] at h
  split_ifs at h with hne
  rw [← Option.some_inj.mp h]
  exact (WellFounded.min_mem _ _ hne).1

theorem isReturn_returnOf {x y : Event} (h : traj.returnOf x = some y) : traj.isReturn y := by
  rw [returnOf] at h
  split_ifs at h with hne
  rw [← Option.some_inj.mp h]
  exact (WellFounded.min_mem _ _ hne).2

theorem returnOf_isReturn {x : Event} (h : traj.isReturn x) : traj.returnOf x = some x := by
  let := @Encodable.linearOrder _ traj.eo
  have hx : x ∈ traj.returnsAfter x := ⟨le_refl x, h⟩
  have hne : (traj.returnsAfter x).Nonempty := ⟨x, hx⟩
  rw [returnOf, dite_eq_left_of_eq_true (eq_true hne), Option.some_inj]
  exact le_antisymm (not_lt.mp (WellFounded.not_lt_min _ _ hx)) (WellFounded.min_mem _ _ hne).1

/-- Every event preceding a return event has its return event. -/
theorem returnOf_le {x z : Event} (hz : traj.isReturn z) (hxz : traj.le x z) :
    ∃ y, traj.returnOf x = some y ∧ traj.le y z := by
  let := @Encodable.linearOrder _ traj.eo
  have hmem : z ∈ traj.returnsAfter x := ⟨hxz, hz⟩
  have hne : (traj.returnsAfter x).Nonempty := ⟨z, hmem⟩
  rw [returnOf, dite_eq_left_of_eq_true (eq_true hne)]
  exact ⟨_, rfl, not_lt.mp (WellFounded.not_lt_min _ _ hmem)⟩

/-- The set of calls preceding an event (according to the non-strict execution order). -/
def callsBefore (x : Event) : Set Event := {y | traj.le y x ∧ traj.isCall y}

theorem callsBefore_finite (x : Event) : (traj.callsBefore x).Finite := by
  let := @Encodable.linearOrder _ traj.eo
  refine ((lt_finite_predecessors (en := traj.eo) x).insert x).subset fun y hy ↦ ?_
  exact hy.1.eq_or_lt.imp id id

open Classical in
/-- The call event of an event is the greatest call event preceding it, if it exists. -/
noncomputable def callOf (x : Event) : Option Event :=
  letI := @Encodable.linearOrder _ traj.eo
  if h : (traj.callsBefore x).Nonempty then
    some (Classical.choose ((traj.callsBefore_finite x).exists_maximal h))
  else none

theorem callOf_le_self {x y : Event} (h : traj.callOf x = some y) : traj.le y x := by
  let := @Encodable.linearOrder _ traj.eo
  rw [callOf] at h
  split_ifs at h with hne
  rw [← Option.some_inj.mp h]
  exact (Classical.choose_spec ((traj.callsBefore_finite x).exists_maximal hne)).1.1

theorem callOf_isCall {x : Event} (h : traj.isCall x) : traj.callOf x = some x := by
  let := @Encodable.linearOrder _ traj.eo
  have hx : x ∈ traj.callsBefore x := ⟨le_refl x, h⟩
  have hne : (traj.callsBefore x).Nonempty := ⟨x, hx⟩
  rw [callOf, dite_eq_left_of_eq_true (eq_true hne), Option.some_inj]
  have hm := Classical.choose_spec ((traj.callsBefore_finite x).exists_maximal hne)
  exact le_antisymm hm.1.1 (hm.2 hx hm.1.1)

end Trajectory

end Cslib.DistributedConsistency
