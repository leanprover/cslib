/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Elligator1.Variables
public import Cslib.Crypto.Systems.Elligator.Elligator1.sProperties

/-!
# c Variable Properties

In this file we introduce some generally helpful lemmas for `c` as introduced
in `Cslib.Crypto.Systems.Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.2, Theorem 1.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1

open Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

lemma c_ne_zero (hs_ne_zero : s ≠ 0) (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    c s ≠ 0 := by
  unfold c
  exact div_ne_zero (two_ne_zero hq_card hq_mod) (pow_ne_zero 2 hs_ne_zero)

omit [Fintype F] in
lemma c_ne_one (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) :
    c s ≠ 1 := by
  unfold c
  exact div_ne_one_of_ne (s_pow_two_ne_two sq_ne_pm_two).symm

omit [Fintype F] in
lemma c_sub_one_ne_zero (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) :
    c s - 1 ≠ 0 :=
  sub_ne_zero.2 (c_ne_one sq_ne_pm_two)

omit [Fintype F] in
lemma c_ne_neg_one (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) : (c s) ≠ -1 := by
  unfold c
  intro h
  have heq : s ^ 2 = -2 := by grind
  have hne := s_pow_two_ne_neg_two sq_ne_pm_two
  contradiction

omit [Fintype F] in
lemma c_add_one_ne_zero (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0) :
    (c s) + 1 ≠ 0 := by
  intro hceq
  have hc_ne_neg_one  := c_ne_neg_one sq_ne_pm_two
  rw [← add_left_inj (-1)] at hceq
  ring_nf at hceq
  contradiction

lemma c_mul_sub_one_mul_add_one_ne_zero
    (hs_ne_zero : s ≠ 0) (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    let c := c s
    c * (c - 1) * (c + 1) ≠ 0 := by
  unfold c
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact c_ne_zero hs_ne_zero hq_card hq_mod
    · exact c_sub_one_ne_zero sq_ne_pm_two
  · exact c_add_one_ne_zero sq_ne_pm_two

lemma s_pow_two_eq_two_div_c
    (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
    s ^ 2 = 2 / (c s) := by
  unfold c
  have h := two_ne_zero hq_card hq_mod
  field_simp

end Cslib.Crypto.Systems.Elligator.Elligator1
