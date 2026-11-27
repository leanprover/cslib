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
a finite number of predecessors.  Thus we define an enumeration as a `LinearOrder` in which
every element has only a finite number of predecessors, i.e., a `LocallyFiniteOrderBot`.

## References

* [*Principles of Eventual Consistency*][Burckhardt2014]
-/

@[expose] public section

open Function Relation Set

/-- An enumeration as a `LinearOrder` in which every element has only a finite number of
predecessors, i.e., a `LocallyFiniteOrderBot`. -/
class Enumeration (α : Type*) extends LinearOrder α, LocallyFiniteOrderBot α

namespace Enumeration

variable {α : Type*} [Enumeration α]

open Classical in
/-- The restriction of an enumeration to a subtype is still an enumeration. -/
noncomputable instance instEnumerationSubtype (p : α → Prop) : Enumeration {x // p x} :=
  { (inferInstance : LinearOrder _), (inferInstance : LocallyFiniteOrderBot _) with }

/-- An enumeration is a `LocallyFiniteOrder`. -/
instance : LocallyFiniteOrder α :=
  LocallyFiniteOrder.ofIcc α (fun a b ↦ (Finset.Iic b).filter (a ≤ ·)) <| by grind

/-- An enumeration is a `PredOrder`. -/
noncomputable instance : PredOrder α := LinearLocallyFiniteOrder.predOrder α

/-- An enumeration is a `SuccOrder`. -/
noncomputable instance : SuccOrder α := LinearLocallyFiniteOrder.succOrder α

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
