/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Probability.PMF

open Cslib.Probability.PMF
open scoped ENNReal

namespace CslibTests.PMF

-- A singleton sampler is the existing deterministic PMF.
example {α : Type*} (a : α) :
    uniformOfFinset {a} (Finset.singleton_nonempty a) = PMF.pure a := by
  classical
  ext b
  simp [PMF.pure_apply, eq_comm]

-- Only the specified two outcomes have mass, each with probability one half.
example (n : ℕ) :
    uniformOfFinset {2, 5} (by simp) n = if n = 2 ∨ n = 5 then 1 / 2 else 0 := by
  simp

-- Sampling a uniform four-element space and observing the lower half gives a fair bit.
example : (((uniformOfFintype (Fin 4)).map (fun n => decide (n < 2))) true).toReal = 1 / 2 := by
  norm_num [PMF.map_apply, tsum_fintype, Fin.sum_univ_succ, ENNReal.toReal_add]

end CslibTests.PMF
