/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl, Matthias Güdemann
-/
module

public import Cslib.Crypto.Systems.Elligator.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Finite Field Basic

In this file we introduce some generally helpful lemmas for the finite field `F` with
`q` fulfilling `IsPrimePow`/`Prime`, `Fintype.card F = q` and `q % 4 = 3`.

The assumption `IsPrimePow q` of [bernstein2013a] never has to be stated: by
`card_isPrimePow` it is a consequence of `Fintype.card F = q`, so `q` ranges over exactly the
prime powers congruent to `3` modulo `4`. Conversely, `prime_of_natCast_surjective` shows that
representing field elements by the naturals `0, 1, …, q - 1`, as the string encoding of
Section 3.4 does, is possible only when `q` is prime.

## References

See [bernstein2013a] for the original account on this specifc finite field.
-/

@[expose] public section

variable {F : Type*} [Field F] [Fintype F]

namespace Cslib.Crypto.Systems.Elligator.FiniteFieldBasic

/-- The cardinality of a finite field is always a prime power.

This is why no statement of this development has to assume `IsPrimePow q`: the hypothesis
`Fintype.card F = q` already forces `q` to be a prime power, so all results proved for a finite
field `F` with `Fintype.card F = q` and `q % 4 = 3` are exactly the results of [Bernstein2013a]
for an arbitrary prime power `q ≡ 3 (mod 4)`. -/
lemma card_isPrimePow {q : ℕ} (hq_card : Fintype.card F = q) : IsPrimePow q := by
  rw [← hq_card]
  exact FiniteField.isPrimePow_card F

lemma two_ne_zero (hq_mod : Fintype.card F % 4 = 3) : (2 : F) ≠ 0 := by
  intro h
  -- turn `(2 : F) = 0` into a divisibility statement about the characteristic
  have hdvd : ringChar F ∣ 2 := (CharP.cast_eq_zero_iff F (ringChar F) 2).mp h
  -- ringChar F ∣ 2 and ringChar F ≠ 1 (F is nontrivial) forces ringChar F = 2
  have hp : ringChar F = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hchar | hchar
    · exact absurd hchar (CharP.char_ne_one F (ringChar F))
    · exact hchar
  have hchar : CharP F 2 := by
    rw [← hp]
    exact ringChar.charP F
  -- a finite field of characteristic 2 has cardinality a power of 2
  obtain ⟨n, -, hcard⟩ := FiniteField.card F 2
  have hqeq : Fintype.card F = 2 ^ (n : ℕ) := by rw [hcard]
  have hdvd2 : (2 : ℕ) ∣ Fintype.card F := by
    rw [hqeq]
    exact dvd_pow_self 2 n.pos.ne'
  -- q even contradicts q % 4 = 3
  omega

lemma four_ne_zero (hq_mod : Fintype.card F % 4 = 3) : (4 : F) ≠ 0 := by
  have hnum : (4 : F) = 2 * 2 := by norm_num
  rw [hnum]
  apply mul_ne_zero <;> exact two_ne_zero hq_mod

lemma ringChar_ne_two (hq_mod : Fintype.card F % 4 = 3) : ringChar F ≠ 2 := by
  intro hchar
  apply two_ne_zero hq_mod
  have hcon : (2 : F) = 0 := (ringChar.spec F 2).mpr (by rw [hchar])
  exact hcon

lemma neg_one_non_square (hq_mod : Fintype.card F % 4 = 3) :
    ¬IsSquare (-1 : F) := by
  intro hsq
  apply FiniteField.isSquare_neg_one_iff.mp at hsq
  contradiction

/-- If some algebraic identity would force `-1` to be a square, contradiction - `-1` is never
a square when `q % 4 = 3`. A common closing step for the `r`/`d` nonvanishing proofs. -/
lemma false_of_isSquare_neg_one (hq_mod : Fintype.card F % 4 = 3)
    (h : IsSquare (-1 : F)) : False := neg_one_non_square hq_mod h

-- TODO fix omits
omit [Fintype F] in
lemma one_sub_t_ne_zero (t : {n : F // n ≠ 1 ∧ n ≠ -1}) : (1 : F) - t.val ≠ 0 :=
  sub_ne_zero.mpr t.prop.1.symm

omit [Fintype F] in
lemma one_add_t_ne_zero (t : {n : F // n ≠ 1 ∧ n ≠ -1}) : (1 : F) + t.val ≠ 0 := by
  intro h
  rw [add_comm] at h
  exact t.prop.2 (eq_neg_of_add_eq_zero_left h)

omit [Fintype F] in
lemma neg_t_ne_one_and_neg_t_ne_neg_one (t : { t : F // t ≠ 1 ∧ t ≠ -1}) :
    -t.val ≠ 1 ∧ -t.val ≠ -1 := by
  constructor
  · intro h
    apply t.prop.2
    have := congrArg Neg.neg h
    simpa using this
  · intro h
    apply t.prop.1
    have := congrArg Neg.neg h
    simpa using this

omit [Fintype F] in
lemma not_t_ne_one_and_t_ne_neg_one (t : { t : F // t = 1 ∨  t = -1}) :
    ¬(t.val ≠ 1 ∧ t.val ≠ -1) := by
  rcases t.prop with th | th <;> simp [th]

omit [Field F] in
lemma one_add_q_div_four_mul_two_eq_one_add_q_div_two (hq_mod : Fintype.card F % 4 = 3) :
    ((1 + Fintype.card F) / 4 * 2) = (1 + Fintype.card F) / 2 := by
  omega

end Cslib.Crypto.Systems.Elligator.FiniteFieldBasic
