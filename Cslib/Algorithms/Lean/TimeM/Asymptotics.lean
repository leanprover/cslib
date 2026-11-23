/-
Copyright (c) 2026 Christian Battaglia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Battaglia
-/
module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs

/-!
# Asymptotic bounds for `TimeM` costs

Mathlib's `Asymptotics.IsBigO` and `Asymptotics.IsTheta` compare two functions along a filter.
`TimeM.time` is a single cost. These definitions lift a size-indexed computation to that API.
-/

@[expose] public section

open Asymptotics Filter

namespace Cslib.Algorithms.Lean.TimeM

/-- The cost of `cost`, as a function of input size, is big-O of `g` at infinity. -/
def isBigO {α T : Type*} [Coe T ℝ] (cost : ℕ → TimeM T α) (g : ℕ → ℝ) : Prop :=
  IsBigO atTop (fun n => ((cost n).time : ℝ)) g

/-- The cost of `cost`, as a function of input size, is big-Theta of `g` at infinity. -/
def isTheta {α T : Type*} [Coe T ℝ] (cost : ℕ → TimeM T α) (g : ℕ → ℝ) : Prop :=
  IsTheta atTop (fun n => ((cost n).time : ℝ)) g

end Cslib.Algorithms.Lean.TimeM
