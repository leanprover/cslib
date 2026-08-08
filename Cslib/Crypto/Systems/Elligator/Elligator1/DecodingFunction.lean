/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Elligator1.Map

/-!
# DecodingFunction

This file exposes the total field-to-curve map from Definition 2 of the Elligator paper under the
name `DecodingFunction`. The underlying construction is `ϕ`: it maps `t = ±1` to `(0, 1)` and,
for every other `t`, returns the coordinates constructed in Theorem 1.

## Main results

* `DecodingFunction`: the Elligator 1 decoding map `F → F × F`, obtained from the curve-valued
  map `ϕ` by forgetting its proof of curve membership.

## References

See [bernstein2013a], Section 3.2, Definition 2.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s : F}
variable {q : ℕ}

/-- The decoding function for the complete Edwards curve -/
def DecodingFunction
  (t : F)
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : F × F := ϕ t hs_ne_zero sq_ne_pm_two hq_card hq_mod

end Cslib.Crypto.Systems.Elligator.Elligator1
