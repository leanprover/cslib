/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.Consistency.Trajectory

/-! # Concrete executions

A concrete execution is the sequence of events corresponding to the transitions executed
by a distributed system containing (potentially) multiple roles.
Various well-formedness conditions are imposed on concrete executions.
We also show that a history (defined in `Specification.lean`) can be extracted from
a concrete execution by restriction to call events

This file formalizes sections 7.3 and 7.4 of [Burckhardt2014].

## References

* [*Principles of Eventual Consistency*][Burckhardt2014]
-/

@[expose] public section

namespace Cslib.DistributedConsistency

open Encodable Relation

variable {Event State Operation Value Message Process Role : Type*}

/-- Concrete execution structure. -/
structure ConcreteExecution (Event State Operation Value Message Process Role : Type*) where
  /-- `eo` is the execution order over events. -/
  [eo : Encodable Event]
  /-- `tr` assigns each event its transition. -/
  tr : Event → Transition State Operation Value Message Process
  /-- `tr` assigns each event its role id. -/
  role : Event → Role
  /-- `del` is the message delivery relation. -/
  del : Event → Event → Prop

namespace ConcreteExecution

variable (exec : ConcreteExecution Event State Operation Value Message Process Role)

/-- The strict execution order. -/
abbrev lt := exec.eo.lt

/-- The non-strict execution order. -/
abbrev le := exec.eo.le

/-- The operation of an event. -/
abbrev op (x : Event) := (exec.tr x).op

/-- The received message of an event. -/
abbrev rcv (x : Event) := (exec.tr x).rcv

/-- The process of an event. -/
abbrev proc (x : Event) := (exec.tr x).proc

/-- The previous state of an event. -/
abbrev pre (x : Event) := (exec.tr x).pre

/-- The next state of an event. -/
abbrev post (x : Event) := (exec.tr x).post

/-- The set of messages sent by an event. -/
abbrev snd (x : Event) := (exec.tr x).snd

/-- The value returned by an event. -/
abbrev rval (x : Event) := (exec.tr x).rval

/-- An event is considered a call iff it has an operation. -/
abbrev isCall (x : Event) := (exec.tr x).op.isSome

/-- An event is considered a return iff it has a return value. -/
abbrev isReturn (x : Event) := (exec.tr x).rval.isSome

open Classical in
/-- Projecting a concrete execution on a role to obtain a trajectory. -/
noncomputable def trajectory (r : Role) :
    Trajectory {x : Event // exec.role x = r} State Operation Value Message Process where
  eo := Subtype.encodable (encA := exec.eo)
  tr := Subtype.restrict (fun x ↦ exec.role x = r) exec.tr

/-- The return event of an event according to its role's trajectory. -/
noncomputable def returnOf (x : Event) : Option Event :=
  (exec.trajectory (exec.role x)).returnOf ⟨x, rfl⟩

/-- The call event of an event according to its role's trajectory. -/
noncomputable def callOf (x : Event) : Option Event :=
  (exec.trajectory (exec.role x)).callOf ⟨x, rfl⟩

/-- The well-formedness conditions on a concrete execution. -/
structure WellFormed : Prop where
  /-- Projecting the concrete execution on each role produces a well-formed trajectory. -/
  trajectory_WellFormed (r : Role) : (exec.trajectory r).WellFormed
  /-- If a message from event `x` is delivered to event `y`, then `x` strictly precedes `y`
  and the message received by `y` is sent by `x`. -/
  del_snd_lt_rcv (x y : Event) : exec.del x y → exec.lt x y ∧
    ∃ m, exec.rcv y = some m ∧ m ∈ exec.snd x
  /-- An event can be delivered a message from at most one other event. -/
  del_sender_unique (x1 x2 y : Event) : exec.del x1 y → exec.del x2 y → x1 = x2

/-- Lemma 7.1 of [Burckhardt2014]: if all calls return immediately,
then the concrete execution is return well-formed. -/
theorem isCall_eq_isReturn_returnWellFormed (h : exec.isCall = exec.isReturn) (r : Role) :
    (exec.trajectory r).ReturnWellFormed :=
  (exec.trajectory r).isCall_eq_isReturn_returnWellFormed (funext fun x ↦ congrFun h x.val)

/-- A history contains only call events. -/
abbrev HistoryEvent := {x : Event // exec.isCall x}

/-- Extracting a history from a concrete execution by restriction to call events. -/
noncomputable def baseHistory : BaseHistory exec.HistoryEvent Operation Value Role where
  op (x : exec.HistoryEvent) := (exec.op x.val).get x.prop
  se (x : exec.HistoryEvent) := exec.role x.val
  rval (x : exec.HistoryEvent) := (exec.returnOf x.val).bind exec.rval
  rb (x y : exec.HistoryEvent) := ∃ z, exec.returnOf x.val = some z ∧ exec.lt z y.val

theorem self_le_returnOf {x z : Event} (h : exec.returnOf x = some z) : exec.le x z := by
  unfold returnOf at h
  cases hr : (exec.trajectory (exec.role x)).returnOf ⟨x, rfl⟩ with
  | none => simp [hr] at h
  | some w =>
    simp only [hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some_inj] at h
    subst h
    exact (exec.trajectory _).self_le_returnOf hr

theorem isReturn_returnOf {x z : Event} (h : exec.returnOf x = some z) : exec.isReturn z := by
  unfold returnOf at h
  cases hr : (exec.trajectory (exec.role x)).returnOf ⟨x, rfl⟩ with
  | none => simp [hr] at h
  | some w =>
    simp only [hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some_inj] at h
    subst h
    exact (exec.trajectory _).isReturn_returnOf hr

theorem rb_strict_order : IsStrictOrder exec.HistoryEvent exec.baseHistory.rb := by
  let := @Encodable.linearOrder _ exec.eo
  refine { irrefl := ?_, trans := ?_ }
  · rintro x ⟨z, hz, hlt⟩
    exact absurd hlt (not_lt.mpr (exec.self_le_returnOf hz))
  · rintro x y w ⟨z1, hz1, h1⟩ ⟨z2, hz2, h2⟩
    exact ⟨z1, hz1, h1.trans (lt_of_le_of_lt (exec.self_le_returnOf hz2) h2)⟩

theorem rb_pred_finite (x : exec.HistoryEvent) : (predecessors exec.baseHistory.rb x).Finite := by
  let := @Encodable.linearOrder _ exec.eo
  refine ((lt_finite_predecessors (en := exec.eo) x.val).preimage
    Subtype.val_injective.injOn).subset ?_
  rintro y ⟨z, hz, hlt⟩
  exact lt_of_le_of_lt (exec.self_le_returnOf hz) hlt

theorem not_rb {x y : exec.HistoryEvent} {z : Event}
    (hxy : ¬ exec.baseHistory.rb x y) (hx : exec.returnOf x.val = some z) : exec.le y z := by
  let := @Encodable.linearOrder _ exec.eo
  exact not_lt.mp fun h ↦ hxy ⟨z, hx, h⟩

theorem rb_interval_order : IsIntervalOrder exec.baseHistory.rb := by
  split_ands
  · exact exec.rb_strict_order
  · rintro x1 y1 x2 y2 ⟨⟨z1, hz1, h1⟩, ⟨z2, hz2, h2⟩⟩
    by_contra! hn
    let := @Encodable.linearOrder _ exec.eo
    have h3 : exec.le y2.val z1 := exec.not_rb hn.1 hz1
    have h4 : exec.le y1.val z2 := exec.not_rb hn.2 hz2
    exact lt_irrefl z1 (h1.trans (h4.trans_lt (h2.trans_le h3)))

theorem rb_rval_ne_none {x y : exec.HistoryEvent}
    (h : exec.baseHistory.rb x y) : exec.baseHistory.rval x ≠ none := by
  obtain ⟨z, hz, -⟩ := h
  have := exec.isReturn_returnOf hz
  simp_all [baseHistory, Option.isSome_iff_ne_none]

theorem rb_of_lt (hwf : exec.WellFormed) {x y : exec.HistoryEvent}
    (hr : exec.role x.val = exec.role y.val) (hlt : exec.lt x y) : exec.baseHistory.rb x y := by
  let := @Encodable.linearOrder _ exec.eo
  obtain ⟨z, hz, hxz, hzy⟩ := (hwf.trajectory_WellFormed (exec.role x.val)).call_return_call
    ⟨x.val, rfl⟩ ⟨y.val, hr.symm⟩ hlt x.prop y.prop
  obtain ⟨w, hw, hwz⟩ := (exec.trajectory _).returnOf_le hz hxz
  refine ⟨w.val, ?_, lt_of_le_of_lt hwz hzy⟩
  simp [returnOf, hw]

theorem so_strict_total_order (hwf : exec.WellFormed) (r : Role) :
    IsStrictTotalOrder {x : exec.HistoryEvent | exec.baseHistory.se x = r}
      (exec.baseHistory.so r) := by
  have hso := exec.rb_strict_order
  refine { trichotomous := ?_, irrefl := ?_, trans := ?_ }
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab hba
    let := @Encodable.linearOrder _ exec.eo
    rcases lt_trichotomy a.val b.val with h | h | h
    · exact absurd ⟨ha, hb, exec.rb_of_lt hwf (ha.trans hb.symm) h⟩ hab
    · exact Subtype.ext (Subtype.ext h)
    · exact absurd ⟨hb, ha, exec.rb_of_lt hwf (hb.trans ha.symm) h⟩ hba
  · rintro a ⟨-, -, h⟩
    exact hso.irrefl _ h
  · rintro a b c ⟨ha, -, h1⟩ ⟨-, hc, h2⟩
    exact ⟨ha, hc, hso.trans _ _ _ h1 h2⟩

/-- The history extracted from a concrete execution by restriction to call events
is a well-defined history. -/
noncomputable def history (hwf : exec.WellFormed) :
    History exec.HistoryEvent Operation Value Role where
  bh := exec.baseHistory
  rb_strict_order := exec.rb_strict_order
  rb_pred_finite := exec.rb_pred_finite
  rb_interval_order := exec.rb_interval_order
  rb_rval_ne_none _ _ := exec.rb_rval_ne_none
  so_strict_total_order := exec.so_strict_total_order hwf

end ConcreteExecution

end Cslib.DistributedConsistency
