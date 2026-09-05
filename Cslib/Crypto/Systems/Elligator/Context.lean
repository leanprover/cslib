/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Basic

/-!
# Bundled data and hypotheses for Elligator

Almost every statement of the Elligator 1 development repeats the same variables and the same
standing hypotheses:

* a finite field `F` whose cardinality `q` satisfies `q % 4 = 3`,
* a curve parameter `s`, sometimes with `s ≠ 0`, sometimes with `(s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0`,
* an input `t ∉ {1, -1}` or a point `P` of `E(F)`.

This file provides two independent mechanisms for getting rid of this repetition:

1. *the variables are bundled* into a small inheritance hierarchy of `structure`s carrying data
   only (`ParamData`, `InputData`, `MapData`, `PointData`), which is what makes dot notation such
   as `M.u`, `M.v`, `M.X` available;
2. *the hypotheses are unbundled* into one `class` per hypothesis (`IsCardThreeModFour`,
   `IsPrimeCard`, `IsNonzeroParam`, `IsRegularParam`), which a statement lists individually and
   which are found by instance resolution instead of being passed by hand.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator

variable {F : Type*} [Field F]

/-- The base field has cardinality `q ≡ 3 (mod 4)`. -/
class IsCardThreeModFour (F : Type*) [Fintype F] : Prop where
  /-- The cardinality of `F` is congruent to `3` modulo `4`. -/
  card_mod_four : Fintype.card F % 4 = 3

/-- The base field has prime cardinality; this is the extra assumption of Theorem 4. -/
class IsPrimeCard (F : Type*) [Fintype F] : Prop where
  /-- The cardinality of `F` is prime. -/
  card_prime : Prime (Fintype.card F)

/-- The curve parameter `s` is nonzero. -/
class IsNonzeroParam {F : Type*} [Field F] (s : F) : Prop where
  /-- The parameter `s` is nonzero. -/
  s_ne_zero : s ≠ 0

/-- The curve parameter `s` satisfies `s ^ 2 ≠ ± 2`. -/
class IsRegularParam {F : Type*} [Field F] (s : F) : Prop where
  /-- The parameter `s` satisfies `(s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0`. -/
  s_sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0

export IsCardThreeModFour (card_mod_four)
export IsPrimeCard (card_prime)
export IsNonzeroParam (s_ne_zero)
export IsRegularParam (s_sq_ne_pm_two)

/-- The curve parameter `s` of Theorem 1, bundled.

No hypotheses: the quantities `c`, `r`, `d` and the curve `E` are defined for every `s`. -/
structure ParamData (F : Type*) [Field F] where
  /-- The Elligator 1 curve parameter. -/
  s : F

/-- An admissible input `t ∉ {1, -1}` of the Elligator 1 map, bundled.

The two disequalities are data rather than hypotheses: they are exactly the subtype
`{n : F // n ≠ 1 ∧ n ≠ -1}` on which the unbundled definitions are given, i.e. the domain of `u`. -/
structure InputData (F : Type*) [Field F] where
  /-- The input of the Elligator 1 map. -/
  t : F
  /-- The input is not `1`. -/
  t_ne_one : t ≠ 1
  /-- The input is not `-1`. -/
  t_ne_neg_one : t ≠ -1

/-- A curve parameter together with an admissible input: the data of Theorem 1. -/
structure MapData (F : Type*) [Field F] extends ParamData F, InputData F

/-- A curve parameter together with a point of the plane: the data of Theorem 3. -/
structure PointData (F : Type*) [Field F] extends ParamData F where
  /-- The point. -/
  P : F × F

namespace InputData

variable (I : InputData F)

/-- The input, as an element of the subtype `{n : F // n ≠ 1 ∧ n ≠ -1}` on which the unbundled
definitions are given. -/
def tSub : {n : F // n ≠ 1 ∧ n ≠ -1} := ⟨I.t, I.t_ne_one, I.t_ne_neg_one⟩

end InputData

end Cslib.Crypto.Systems.Elligator
