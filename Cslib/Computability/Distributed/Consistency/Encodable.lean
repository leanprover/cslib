/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Relation.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-! # Order theory of `Encodable`

In [Burckhardt2014], an "enumeration" is a strict total order in which every element has only
a finite number of predecessors.  We model enumerations using the type class `Encodable`,
develop its order theory, and prove that this is a faithful modeling.

## References

* [*Principles of Eventual Consistency*][Burckhardt2014]
-/

@[expose] public section

open Function Relation Set

namespace Encodable

section ToStrictWellOrder

variable {α : Type*} [en : Encodable α]

/-- Form a linear order lifting the linear order on ℕ. -/
abbrev linearOrder : LinearOrder α :=
  LinearOrder.lift' encode encode_injective

attribute [local instance] linearOrder

/-- Derive a locally finite order. -/
noncomputable abbrev locallyFiniteOrder : LocallyFiniteOrder α :=
  .ofFiniteIcc fun a b =>
    (Set.finite_Icc (encode a) (encode b)).preimage encode_injective.injOn

attribute [local instance] locallyFiniteOrder

/-- Derive an order with a `pred` (predecessor) function. -/
noncomputable abbrev predOrder : PredOrder α :=
  LinearLocallyFiniteOrder.predOrder α

/-- Derive an order with a `succ` (successor) function. -/
noncomputable abbrev succOrder : SuccOrder α :=
  LinearLocallyFiniteOrder.succOrder α

/-- `lt` is the strict order. -/
abbrev lt : α → α → Prop := linearOrder.lt

/-- `le` is the non-strict order. -/
abbrev le : α → α → Prop := linearOrder.le

/-- The predecessor function. -/
noncomputable abbrev pred : α → α := predOrder.pred

/-- The successor function. -/
noncomputable abbrev succ : α → α := succOrder.succ

/-- `lt` is a strict total order. -/
theorem lt_isStrictTotalOrder : IsStrictTotalOrder α lt :=
  @instIsStrictTotalOrderLt α linearOrder

/-- Every element has only a finite number of predecessors under `lt`. -/
theorem lt_finite_predecessors (a : α) : (predecessors lt a).Finite :=
  (finite_lt_nat (encode a)).preimage encode_injective.injOn

/-- `lt` is a well-founded order. -/
theorem lt_wellFounded : WellFounded (α := α) lt :=
  InvImage.wf encode wellFounded_lt

end ToStrictWellOrder

section OfStrictWellOrder

variable {α : Type*} {r : α → α → Prop}

/-- The rank of an element is the number of its predecessors. -/
noncomputable def rank (r : α → α → Prop) (x : α) : ℕ := (predecessors r x).ncard

/-- In a strict total order in which every element has only a finite number of predecessors,
the rank function is (strictly) monotonic. -/
theorem rank_mono (hs : IsStrictTotalOrder α r) (hf : ∀ x, (predecessors r x).Finite)
    {a b : α} (hab : r a b) : rank r a < rank r b := by
  refine ncard_lt_ncard (s := predecessors r a) ⟨fun _ hc ↦ hs.trans _ _ _ hc hab, ?_⟩ (hf b)
  exact fun h ↦ hs.irrefl a (h hab)

/-- In a strict total order in which every element has only a finite number of predecessors,
the rank function is injective. -/
theorem rank_inj (hs : IsStrictTotalOrder α r) (hf : ∀ a, (predecessors r a).Finite) :
    Injective (rank r) := by
  intro x y h
  exact hs.trichotomous x y (fun hxy ↦ (rank_mono hs hf hxy).ne h)
    (fun hyx ↦ (rank_mono hs hf hyx).ne' h)

open Classical in
/-- Constructing `Encodable` from a strict total order in which every element has only
a finite number of predecessors using the rank function. -/
@[instance_reducible]
noncomputable def ofStrictWellOrder
    (hs : IsStrictTotalOrder α r) (hf : ∀ x, (predecessors r x).Finite) :
    Encodable α where
  encode := rank r
  decode := partialInv (rank r)
  encodek := partialInv_left (rank_inj hs hf)

end OfStrictWellOrder

end Encodable
