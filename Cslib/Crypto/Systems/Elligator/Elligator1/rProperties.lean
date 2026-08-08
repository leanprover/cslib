/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Elligator1.Variables
public import Cslib.Crypto.Systems.Elligator.Elligator1.cProperties

/-!
# r Variable Properties

In this file we introduce some generally helpful lemmas for `r` as introduced
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

lemma r_ne_zero (hs_ne_zero : s ≠ 0) (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
  : (r s) ≠ 0 := by
    intro h
    let c := c s
    change c + 1 / c = 0 at h
    have hcneg : c = (-1 : F) / c := by grind
    have hcpow : c^2 = -1 := by
      calc
        c^2 = -1 / c * c := by grind
        _ = -1 := by
          nth_rw 1 [← neg_one_mul 1]
          ring_nf
          rw [mul_inv_cancel₀ (c_ne_zero hs_ne_zero hq_card hq_mod)]
    have hsq : IsSquare (-1 : F) := by
      rw [← hcpow, pow_two]
      apply IsSquare.mul_self c
    exact false_of_isSquare_neg_one hq_card hq_mod hsq

lemma four_add_r_ne_zero
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : 4 + (r s) ≠ 0 := by
    intro h_contra
    have hc_ne_zero : c s ≠ 0 := c_ne_zero hs_ne_zero hq_card hq_mod
    -- Step 1: clear `1/c` from `r`'s definition.
    have h_quad : (c s) ^ 2 + 4 * (c s) + 1 = 0 := by
      unfold r at h_contra
      field_simp at h_contra
      linear_combination h_contra
    -- Step 2: substitute `c = 2/s²`, clear denominators — `(s²+4)² = 12`.
    set a : F := s ^ 2 + 4 with ha_def
    have ha_sq : a ^ 2 = 12 := by
      unfold c at h_quad
      field_simp at h_quad
      linear_combination h_quad  -- verify exact coefficient
    -- Step 3: halving, `u² = 3`.
    set u : F := a / 2 with hu_def
    have hu_sq : u ^ 2 = 3 := by
      rw [hu_def, div_pow, ha_sq]
      grind
    -- Step 4: `2u = a`, so `u² - 2u + 1 = 3 - a + 1 = -s²`, giving `((u-1)/s)² = -1`.
    have hu_eq_a : 2 * u = a := by
      rw [hu_def, mul_div_left_comm, div_self (FiniteFieldBasic.two_ne_zero hq_card hq_mod)]
      rw [mul_one]
    have h_neg_one_sq : (-1 : F) = ((u - 1) / s) ^ 2 := by
      rw [div_pow, eq_div_iff (pow_ne_zero 2 hs_ne_zero)]
      simp_all
      grind
    exact neg_one_non_square hq_card hq_mod ⟨_, h_neg_one_sq.trans (sq _)⟩

lemma r_sq_sub_two_eq_c_sq_add_inv_c_sq
  (hs_ne_zero : s ≠ 0) (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) :
  let r := r s
  let c := c s
  (r^2 - 2) = c^2 + 1 / c^2 := by
    intro r c
    calc
      r^2 - 2 = (c + 1 / c)^2 - 2 := by trivial
      _ = c^2 + 2 * (c * (1 / c)) + (1 / c)^2 - 2 := by grind
      _ = c^2 + 2 + 1 / c^2 - 2 := by
        ring_nf
        rw [mul_inv_cancel₀ (c_ne_zero hs_ne_zero hq_card hq_mod)]
        ring_nf
      _ = c^2 + 1 / c^2 := by ring_nf

lemma r_sub_two_ne_zero
  (hs_ne_zero : s ≠ 0)
  (sq_ne_pm_two : (s ^ 2 - 2) * (s ^ 2 + 2) ≠ 0)
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : (r s) - 2 ≠ 0 := by
    let c := c s
    have hc_ne_zero := c_ne_zero hs_ne_zero hq_card hq_mod
    change (c + 1 / c) - 2 ≠ 0
    have hceq : (c + 1 / c) - 2 = (c - 1)^2 / c := by grind
    rw [hceq]
    apply div_ne_zero (by grind [c_ne_one ]) hc_ne_zero

end Cslib.Crypto.Systems.Elligator.Elligator1
