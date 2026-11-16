/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Thomas Waring
-/

module

public import Cslib.Foundations.Relation.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-! # Enumeration

In [Burckhardt2014], an "enumeration" is a strict total order in which every element has only
a finite number of predecessors.

## References

* [*Principles of Eventual Consistency*][Burckhardt2014]
-/

@[expose] public section

open Function Relation Set
/-- We define an enumeration as a `LinearOrder` in which every element has only a finite number
of predecessors, i.e., a `LocallyFiniteOrderBot`. -/
class Enumeration (α : Type*) extends LinearOrder α, LocallyFiniteOrderBot α

namespace Enumeration

variable {α : Type*} [Enumeration α]

/-- An enumeration is a `LocallyFiniteOrder`. -/
noncomputable instance : LocallyFiniteOrder α :=
  LocallyFiniteOrder.ofFiniteIcc fun _ b =>
    (Finset.Iic b).finite_toSet.subset fun _ hx => Finset.mem_Iic.mpr hx.2

/-- An enumeration is a `PredOrder`. -/
noncomputable instance : PredOrder α := LinearLocallyFiniteOrder.predOrder α

/-- The predecessor function. -/
noncomputable abbrev pred : α → α := Order.pred

/-- An enumeration is a `SuccOrder`. -/
noncomputable instance : SuccOrder α := LinearLocallyFiniteOrder.succOrder α

/-- The successor function. -/
noncomputable abbrev succ : α → α := Order.succ

/-- `lt` is a strict total order. -/
theorem lt_isStrictTotalOrder : IsStrictTotalOrder α LT.lt :=
  inferInstance

/-- Every element has only a finite number of predecessors under `lt`. -/
theorem lt_finite_predecessors (a : α) : (predecessors LT.lt a).Finite :=
  (Finset.Iio a).finite_toSet.subset fun _ hx => Finset.mem_Iio.mpr hx

/-- `lt` is a well-founded order. -/
theorem lt_wellFounded : WellFounded (α := α) LT.lt :=
  wellFounded_lt

end Enumeration
