/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Relation.Defs
public import Mathlib.Basic.Finite.Defs

/-! # Consistency specifications

We formalize several notions of consistency for replicated data types defined in [Burckhardt2014],
listed below in decreasing order of strength:
* Linearizability,
* Sequential consistency.
* Causal consistency,
* Basic eventual consistency,
* Quiescent consistency.

We follow [Burckhardt2014] closely in the formalization except for one detail:
instead of using an equivalence relation "same-session" to model the notion of sessions,
we use a map `se : Event → Session` and regard two events `x` and `y` to belong to the
same session iff `se x = se y`.  These two approaches are clearly equivalent and `se` is
chosen because it is easier to work with.

## References

* [*Principles of Eventual Consistency*][Burckhardt2014]
-/

@[expose] public section

namespace Cslib.DistributedConsistency

open Set Relation

variable {Event Operation Value Session : Type*}

/-- `BaseHistory` is an auxiliary definition containing all data fields of `History` below. -/
structure BaseHistory (Event Operation Value Session : Type*) where
  /-- `op` assigns each event its operation. -/
  op : Event → Operation
  /-- `se` assigns each event its session. -/
  se : Event → Session
  /-- `rval` assigns each event its return value, where `none` indicates that
  the event never returns. -/
  rval : Event → Option Value
  /-- `rb` is the "returns before" order on events. -/
  rb : Event → Event → Prop

/-- `so` (for "session order") is `rb` restricted to a single session. -/
def BaseHistory.so (h : BaseHistory Event Operation Value Session) (s : Session) :=
  restrict h.rb {x | h.se x = s}

/-- `History` extends `BaseHistory` with well-formedness conditions. -/
structure History (Event Operation Value Session : Type*)
    extends bh : BaseHistory Event Operation Value Session where
  /-- `rb` is a strict order on events (namely, it is irreflexive and transitive). -/
  rb_strict_order : IsStrictOrder Event rb
  /-- Each event has only a finite number of predecessors in the `rb` order. -/
  rb_pred_finite : ∀ x, (predecessors rb x).Finite
  /-- The `rb` order is an interval order. -/
  rb_interval_order : IsIntervalOrder rb
  /-- If an event `x` returns before another event `y`, then `x` cannot return `none`. -/
  rb_rval_ne_none : ∀ x y, rb x y → rval x ≠ none
  /-- The `so` order is a strict total order of the events of each session. -/
  so_strict_total_order : ∀ s, IsStrictTotalOrderOn {x | se x = s} (bh.so s)

/-- `AbstractExecution` extends `History` with two more orders and additional
well-formedness conditions. -/
structure AbstractExecution (Event Operation Value Session : Type*)
    extends History Event Operation Value Session where
  /-- `vis x y` means that `x` is visible to `y`. -/
  vis : Event → Event → Prop
  /-- `ar` is the arbitration order of the whole system. -/
  ar : Event → Event → Prop
  /-- The visibility order `vis` is acyclic. -/
  vis_acyclic : Acyclic vis
  /-- Each event has only a finite number of predecessors in the `vis` order. -/
  vis_pred_finite : ∀ x, (predecessors vis x).Finite
  /-- The arbitration order is a strict total order of all events. -/
  ar_strict_total_order : IsStrictTotalOrder Event ar

/-- A history satisfies a predicte `p` on abstract executions iff it can be extended
to an abstract execution satisfying `p`. -/
def History.Satisfies (h : History Event Operation Value Session)
    (p : AbstractExecution Event Operation Value Session → Prop) : Prop :=
  ∃ a : AbstractExecution Event Operation Value Session, a.toHistory = h ∧ p a

namespace AbstractExecution

/-- `ReadMyWrites` says that if two events are ordered by `so`,
then they are also ordered by `vis`. -/
def ReadMyWrites (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ s, a.so s ≤ a.vis

/-- `MonotonicReads` says that if `x` is visible to `y`, then `x` is also visible to all
successors of `y` under the `so` order. -/
def MonotonicReads (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ s x y z, a.vis x y → a.so s y z → a.vis x z

/-- `ConsistentPrefix` says that if `x` is visible to `y` in a different session,
then all predecessors of `x` in the arbitration order are also visible to `y`. -/
def ConsistentPrefix (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ x y, a.se x ≠ a.se y → a.vis x y → ∀ z, a.ar z x → a.vis z y

/-- The `happens before` order is the per-session transitive closure of the union of
the `so` and `vis` orders. -/
def hb (a : AbstractExecution Event Operation Value Session)
    (s : Session) : Event → Event → Prop :=
  TransGen fun x y ↦ a.so s x y ∨ a.vis x y

/-- `NoCircularCausality` says that the `hb` order is acyclic. -/
def NoCircularCausality (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ s, Acyclic (a.hb s)

/-- `CausalArbitration` says that if two events are ordered by `hb`,
then they are also ordered by `ar`. -/
def CausalArbitration (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ s, a.hb s ≤ a.ar

/-- `CausalVisibility` says that if two events are ordered by `hb`,
then they are also ordered by `vis`. -/
def CausalVisibility (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ s, a.hb s ≤ a.vis

/-- `Causality` is the conjunction of `CausalArbitration` and `CausalVisibility`. -/
def Causality (a : AbstractExecution Event Operation Value Session) : Prop :=
  a.CausalArbitration ∧ a.CausalVisibility

/-- `SingleOrder` says that `vis` and `ar` are the same order except that there may be
a set of events which never returns and are not visible. -/
def SingleOrder (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∃ xs : Set Event, (∀ x, x ∈ xs → a.rval x = none) ∧
    ∀ x y, a.vis x y ↔ a.ar x y ∧ ¬ x ∈ xs

/-- `RealTime` says that if two events are ordered by `rb`, then they are also ordered by `ar`. -/
def RealTime (a : AbstractExecution Event Operation Value Session) : Prop :=
  a.rb ≤ a.ar

/-- `a.nonVisibleEvents x s` is the set of events in session `s` which returns after `x`
but does not see `x`. -/
def nonVisibleEvents (a : AbstractExecution Event Operation Value Session)
    (x : Event) (s : Session) : Set Event :=
  { y | a.se y = s ∧ a.rb x y ∧ ¬ a.vis x y }

/-- `EventualVisibility` says that for any event `x` and any session `s`, there can be at most
finitely many events in `s` that return after `x` and do not see `x`.
-/
def EventualVisibility (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ x : Event, ∀ s : Session, (a.nonVisibleEvents x s).Finite

end AbstractExecution

/-- An `OperationContext` is the data used by a replicated data type to determine the
return value of an operation.  It is an abstraction of the notion of states. -/
structure OperationContext (Event Operation : Type*) where
  /-- The set of events in the operation context. -/
  events : Set Event
  /-- Operation labeling of events. -/
  op : Event → Operation
  /-- Visibility order. -/
  vis : Event → Event → Prop
  /-- Arbitration order. -/
  ar : Event → Event → Prop

/-- The notion of equivalence on `OperationContext`, which is essentially an isomorphism
that ignores the identities of events and the behavior of `op`, `vis`, and `ar` outside
the set of events in the operation context. -/
structure OperationContext.Equiv (c1 c2 : OperationContext Event Operation) where
  /-- A bijection from `c1`'s events to `c2`'s events. -/
  equiv : { x // x ∈ c1.events } ≃ { x // x ∈ c2.events }
  /-- `op` is preserved by the bijection. -/
  op_equiv : ∀ x, c1.op x.val = c2.op (equiv x).val
  /-- `vis` is preserved by the bijection. -/
  vis_equiv : ∀ x y, c1.vis x.val y.val ↔ c2.vis (equiv x).val (equiv y).val
  /-- `ar` is preserved by the bijection. -/
  ar_equiv : ∀ x y, c1.ar x.val y.val ↔ c2.ar (equiv x).val (equiv y).val

/-- The notion of a replicated data type. -/
structure ReplicatedDataType (Event Operation Value : Type*) where
  /-- `rval` takes an operation and an operation context and returns a value. -/
  rval : Operation → OperationContext Event Operation → Option Value
  /-- For any operation, `rval` must returns the same value on equivalent operation contexts. -/
  rval_equiv : ∀ o c1 c2, ∀ _ : c1.Equiv c2, rval o c1 = rval o c2

/-- For a replicated data type `d`, an operation `o` is read-only iff an event with operation `o`
can be removed from any operation context without affecting the behavior of `d`. -/
def ReplicatedDataType.ReadOnlyOp (d : ReplicatedDataType Event Operation Value)
    (o : Operation) : Prop :=
  ∀ c : OperationContext Event Operation, ∀ x ∈ c.events,
    c.op x = o → ∀ o' : Operation, d.rval o' c = d.rval o' {c with events := c.events \ {x}}

namespace AbstractExecution

/-- `a.context xs` is the operation context obtained by restricting `a` to `xs`. -/
def context (a : AbstractExecution Event Operation Value Session)
    (xs : Set Event) : OperationContext Event Operation where
  events := xs
  op := a.op
  vis := a.vis
  ar := a.ar

/-- `a.RVal d` says that the return value of any event in the abstract execution `a` is
the same as the value returned by the replicated data type `d` in the context consisting of
the predecessors of the event. -/
def RVal (a : AbstractExecution Event Operation Value Session)
    (d : ReplicatedDataType Event Operation Value) : Prop :=
  ∀ x, a.rval x = d.rval (a.op x) (a.context (predecessors a.vis x))

/-- `Linearizability` is the conjunction of `SingleOrder`, `RealTime`, and `RVal`. -/
def Linearizability (a : AbstractExecution Event Operation Value Session)
    (d : ReplicatedDataType Event Operation Value) : Prop :=
  a.SingleOrder ∧ a.RealTime ∧ a.RVal d

/-- `SequentialConsistency` is the conjunction of `SingleOrder`, `ReadMyWrites`, and `RVal`. -/
def SequentialConsistency (a : AbstractExecution Event Operation Value Session)
    (d : ReplicatedDataType Event Operation Value) : Prop :=
  a.SingleOrder ∧ a.ReadMyWrites ∧ a.RVal d

/-- `CausalConsistency` is the conjunction of `EventualVisibility`, `Causality`, and `RVal`. -/
def CausalConsistency (a : AbstractExecution Event Operation Value Session)
    (d : ReplicatedDataType Event Operation Value) : Prop :=
  a.EventualVisibility ∧ a.Causality ∧ a.RVal d

/-- `BasicEventualConsistency` is the conjunction of `EventualVisibility`, `NoCircularCausality`,
and `RVal`. -/
def BasicEventualConsistency (a : AbstractExecution Event Operation Value Session)
    (d : ReplicatedDataType Event Operation Value) : Prop :=
  a.EventualVisibility ∧ a.NoCircularCausality ∧ a.RVal d

/-- `a.updateEvents d` is the set of events in `a` whose operations are not read-only in `d` -/
def updateEvents (a : AbstractExecution Event Operation Value Session)
    (d : ReplicatedDataType Event Operation Value) : Set Event :=
  { x | ¬ d.ReadOnlyOp (a.op x) }

/-- `a.nonRvalEvents d c s` is the set of events in `a` of session `s` whose return value
does not agree with the value returned by `d` in the context `c`. -/
def nonRvalEvents (a : AbstractExecution Event Operation Value Session)
    (d : ReplicatedDataType Event Operation Value)
    (c : OperationContext Event Operation) (s : Session) : Set Event :=
  { x | a.se x = s ∧ d.rval (a.op x) c ≠ a.rval x }

/-- `a.QuiescentConsistency d` says that if the set of update events is finite, then there exists
a context `c` such that for any session, there is at most a finite set of events for which
the return values in the abstract execution `a` do not agree with the values returned by the
replicated data type `d` in the context `c`. -/
def QuiescentConsistency (a : AbstractExecution Event Operation Value Session)
    (d : ReplicatedDataType Event Operation Value) : Prop :=
  (a.updateEvents d).Finite → ∃ c, ∀ s, (a.nonRvalEvents d c s).Finite

end AbstractExecution

end Cslib.DistributedConsistency
