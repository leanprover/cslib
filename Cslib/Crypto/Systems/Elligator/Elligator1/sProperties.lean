/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Basic

/-!
# s Variable Properties

In this file we introduce some generally helpful lemmas for `s` as introduced
in `Cslib.Crypto.Systems.Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1

variable {F : Type*} [Field F]
variable {s : F}

lemma s_pow_two_ne_two (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) :
    s ^ 2 ≠ 2 :=
  sub_ne_zero.mp (left_ne_zero_of_mul sq_ne_pm_two)

lemma s_pow_two_ne_neg_two (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) :
    s ^ 2 ≠ -2 := by
  have h := right_ne_zero_of_mul sq_ne_pm_two
  rwa [ne_eq, add_eq_zero_iff_eq_neg] at h

end Cslib.Crypto.Systems.Elligator.Elligator1
