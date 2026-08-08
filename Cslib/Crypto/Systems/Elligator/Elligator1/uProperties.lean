/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/
module

public import Cslib.Crypto.Systems.Elligator.Elligator1.Variables

/-!
# u Variable Properties

In this file we introduce some generally helpful lemmas for `u` as introduced in
`Cslib.Crypto.Systems.Elligator.Elligator1.Variables`.

## References

See [bernstein2013a], Section 3.2.
-/

@[expose] public section

namespace Cslib.Crypto.Systems.Elligator.Elligator1

open Elligator.FiniteFieldBasic

variable {F : Type*} [Field F] [Fintype F]
variable {s : F}
variable {q : ℕ}

omit [Fintype F] in
lemma u_ne_zero (t : {n : F // n ≠ 1 ∧ n ≠ -1}) : u t ≠ (0 : F) :=
  div_ne_zero (one_sub_t_ne_zero t) (one_add_t_ne_zero t)

omit [Fintype F] in
lemma u_comparison (t : {n : F // n ≠ 1 ∧ n ≠ -1}) :
  let t1 := t.val
  let t2 := -t1
  let u1 := u t
  let u2 := u ⟨t2, neg_t_ne_one_and_neg_t_ne_neg_one t⟩
  u2 = 1 / u1 := by
    intro t1 t2 u1 u2
    calc
      u2 = (1 - t2) / (1 + t2) := by simp [u2, u]
     _ = (1 + t) / (1 - t) := by simp [t2, t1]; ring_nf
     _ = 1 / u1 := by simp [u1, u]

omit [Fintype F] in
@[simp]
lemma u_of_zero :
  let u := u ⟨(0 : F), by simp⟩
  u = 1 := by simp [u]

lemma one_add_u_ne_zero
  (t : {n : F // n ≠ 1 ∧ n ≠ -1})
  (hq_card : Fintype.card F = q)
  (hq_mod : q % 4 = 3)
  : 1 + (u t) ≠ 0 := by
    unfold u
    rw [add_div' _ _ _ (one_add_t_ne_zero t)]
    norm_num
    constructor
    · exact two_ne_zero hq_card hq_mod
    · exact one_add_t_ne_zero t

end Cslib.Crypto.Systems.Elligator.Elligator1
