/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Cslib.Computability.Circuit.Boolean.Basic
public import Cslib.Computability.Circuit.Shannon

/-!
# Shannon's lower bound for De Morgan circuits

This is the De Morgan specialization of `Cslib.Circuits.Shannon.exists_hard_function`.
Together with Lupanov's construction, it gives the asymptotically sharp gate count `2ⁿ/n`.
-/

public section

namespace Cslib.Circuits.Boolean.Shannon

/-- For all sufficiently large `n`, some Boolean function on `n` inputs requires
more than `2ⁿ/n` De Morgan gates, counting constants and negations. -/
theorem exists_hard_function :
    ∃ N : ℕ, ∀ n ≥ N, ∃ f : BooleanFunction n,
      ∀ {g} (c : Circuit signature n g 1),
        c.Computes interpretation f → 2 ^ n / (n : ℝ) < (c.size : ℝ) :=
  Circuits.Shannon.exists_hard_function interpretation (fun op => by cases op <;> simp)

end Cslib.Circuits.Boolean.Shannon
