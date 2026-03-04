/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding

namespace Turing

namespace Routines

variable [Inhabited α] [Fintype α]
variable {k : ℕ}

/--
A Turing machine combinator that runs `tm₁` if the first word on tape `i` exists and is non-empty,
otherwise it runs `tm₂`. -/
public def ite (i : Fin k) (tm₁ tm₂ : MultiTapeTM k (WithSep α)) :
    MultiTapeTM k (WithSep α) where
  State := PUnit
  stateFintype := inferInstance
  q₀ := PUnit.unit
  tr _ syms := sorry

@[simp, grind =]
public theorem ite_eval_list
  {i : Fin k}
  {tm₁ tm₂ : MultiTapeTM k (WithSep α)}
  {tapes : Fin k → List (List α)} :
  (ite i tm₁ tm₂).eval_list tapes =
    if (tapes i).headD [] = [] then tm₂.eval_list tapes else tm₁.eval_list tapes := by
  sorry

end Routines

end Turing
