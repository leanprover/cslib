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
variable {q : ℕ}

namespace Cslib.Crypto.Systems.Elligator.FiniteFieldBasic

/-- The cardinality of a finite field is always a prime power.

This is why no statement of this development has to assume `IsPrimePow q`: the hypothesis
`Fintype.card F = q` already forces `q` to be a prime power, so all results proved for a finite
field `F` with `Fintype.card F = q` and `q % 4 = 3` are exactly the results of [bernstein2013a]
for an arbitrary prime power `q ≡ 3 (mod 4)`. -/
lemma card_isPrimePow (hq_card : Fintype.card F = q) : IsPrimePow q := by
  rw [← hq_card]
  exact FiniteField.isPrimePow_card F

omit [Field F] in
lemma q_odd (hq_mod : q % 4 = 3) : Odd q := by
  rw [Nat.odd_iff]
  omega

omit [Field F] in
lemma q_sub_one_div_two_odd (hq_mod : q % 4 = 3) : Odd ((q - 1) / 2) := by
  rw [Nat.odd_iff]
  omega

omit [Field F] in
lemma q_sub_one_even (hq_mod : q % 4 = 3) : Even (q - 1) := by
  rw [Nat.even_iff]
  omega

omit [Fintype F] in
lemma one_ne_zero : (1 : F) ≠ 0 := by exact one_ne_zero' F

lemma q_add_one_div_four_ne_zero (hq_mod : q % 4 = 3) : (1 + q) / 4 ≠ 0 := by
  apply Nat.div_ne_zero_iff.mpr
  norm_num
  have hqle : q ≥ 3 := by lia
  exact Nat.sub_le_iff_le_add'.mp hqle

lemma q_add_one_div_two_ne_zero (hq_mod : q % 4 = 3) : (1 + q) / 2 ≠ 0 := by
  apply Nat.div_ne_zero_iff.mpr
  norm_num
  have hqle : q ≥ 2 := by lia
  exact Nat.le_add_left_of_le hqle

lemma two_ne_zero (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) : (2 : F) ≠ 0 := by
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
  have hqeq : q = 2^(n : ℕ) := by rw [← hq_card, hcard]
  have hdvd2 : (2 : ℕ) ∣ q := by
    rw [hqeq]
    exact dvd_pow_self 2 n.pos.ne'
  -- q even contradicts q % 4 = 3
  omega

lemma four_ne_zero (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) : (4 : F) ≠ 0 := by
  have hnum : (4 : F) = 2 * 2 := by norm_num
  rw [hnum]
  apply mul_ne_zero
  · exact (two_ne_zero hq_card hq_mod)
  · exact (two_ne_zero hq_card hq_mod)

lemma ringChar_ne_two (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3) : ringChar F ≠ 2 := by
  intro hchar
  apply two_ne_zero  hq_card hq_mod
  have hcon : (2 : F) = 0 := (ringChar.spec F 2).mpr (by rw [hchar])
  exact hcon

omit [Fintype F] in
lemma neg_one_ne_zero : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero

lemma neg_one_non_square (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
  : ¬IsSquare (-1 : F) := by grind [FiniteField.isSquare_neg_one_iff]

/-- If some algebraic identity would force `-1` to be a square, contradiction — `-1` is never
a square when `q % 4 = 3`. A common closing step for the `r`/`d` nonvanishing proofs. -/
lemma false_of_isSquare_neg_one (hq_card : Fintype.card F = q) (hq_mod : q % 4 = 3)
  (h : IsSquare (-1 : F)) : False := neg_one_non_square hq_card hq_mod h

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
lemma one_add_q_div_four_mul_two_eq_one_add_q_div_two (hq_mod : q % 4 = 3)
  : ((1 + q) / 4 * 2) = (1 + q) / 2 := by omega

/-- If `F` has `q` elements and `q` is prime, `q` is literally the characteristic of `F`. -/
lemma ringChar_of_F_eq_q (hq_card : Fintype.card F = q) (q_prime : Prime q) : ringChar F = q := by
  -- Every finite field's cardinality is a power of its characteristic, and the
  -- characteristic itself is prime.
  obtain ⟨n, h_char_prime, h_card_eq_pow⟩ := FiniteField.card F (ringChar F)
  have h_q_eq_pow : q = (ringChar F) ^ (n : ℕ) := by rw [← hq_card, h_card_eq_pow]
  -- In particular `ringChar F` divides `q` (the exponent `n` is at least `1`).
  have h_dvd : ringChar F ∣ q := h_q_eq_pow ▸ dvd_pow_self _ n.pos.ne'
  -- `q` is prime, so its only divisors are `1` and `q` - and a field's characteristic
  -- is never `1`, so it must be `q` itself.
  rcases (Nat.dvd_prime (Nat.prime_iff.mpr q_prime)).1 h_dvd with hchar | hchar
  · exact absurd hchar h_char_prime.ne_one
  · exact hchar

/-- The cast `Fin q → F` is injective -/
lemma fin_to_finfield_injective (hq_card : Fintype.card F = q) (q_prime : Prime q)
  : Function.Injective (fun n : Fin q => (n : F)) := by
    intro a b hab
    have h : CharP F q := by
      rw [← ringChar_of_F_eq_q hq_card q_prime]
      exact ringChar.charP F
    exact Fin.ext (CharP.natCast_injOn_Iio F q a.isLt b.isLt hab)

lemma fin_to_finfield_bijective (hq_card : Fintype.card F = q) (q_prime : Prime q) :
  Function.Bijective (fun n : Fin q => (n : F)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fin_to_finfield_injective hq_card q_prime, by rw [Fintype.card_fin, hq_card]⟩

/-- Every element of `F` is the cast of some `n : Fin q`:
this cast is injective and `Fin q` and `F` have the same cardinality, so it is bijective. -/
lemma exists_fin_cast_eq (hq_card : Fintype.card F = q) (q_prime : Prime q) (t : F) :
  ∃ n : Fin q, (n : F) = t := (fin_to_finfield_bijective hq_card q_prime).surjective t

/- Every element of F can be written as (n : F) for some n < q because Fintype.card F = q and
the natural cast n ↦ (n : F) has period equal to ringChar F = q (since q is prime),
so {(0 : F), (1 : F), ..., (q-1 : F)} gives all q distinct elements.  -/
lemma exists_nat_cast_eq
  (hq_card : Fintype.card F = q)
  (q_prime : Prime q)
  (t : F)
  : ∃ (n : ℕ), n < q ∧ (n : F) = t := by
    obtain ⟨n, hn⟩ : ∃ n : Fin q, (n : F) = t := exists_fin_cast_eq hq_card q_prime t
    exact ⟨n.val, n.isLt, hn⟩

/-- A natural number `q` is the cardinality of some finite field iff it is a prime power.

Together with `Cslib.Crypto.Systems.Elligator.FiniteFieldBasic.card_isPrimePow` this says that
the standing hypotheses `Fintype.card F = q`, `q % 4 = 3` of this development describe exactly
the setting of [bernstein2013a], Section 3.1: an arbitrary prime power `q ≡ 3 (mod 4)`. -/
lemma exists_field_card_eq_iff_isPrimePow (q : ℕ) :
  (∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = q) ↔ IsPrimePow q := by
    constructor
    · rintro ⟨F, _, _, hcard⟩
      exact card_isPrimePow hcard
    · rintro ⟨p, k, hp, hk, rfl⟩
      have hp' : Nat.Prime p := Nat.prime_iff.mpr (by exact_mod_cast hp)
      have hfact : Fact (Nat.Prime p) := ⟨hp'⟩
      have hk0 : k ≠ 0 := hk.ne'
      have htype : Fintype (GaloisField p k) := Fintype.ofFinite _
      refine ⟨GaloisField p k, inferInstance, inferInstance, ?_⟩
      have hcard := GaloisField.card p k hk0
      rw [Nat.card_eq_fintype_card] at hcard
      exact hcard

/-- If every element of `F` is the image of a natural number under the canonical cast, then the
cardinality of `F` is *prime*, not merely a *prime power*.

This is the precise reason why the string encoding `ι` of [bernstein2013a], Section 3.4, is
formalized for prime `q` only: it represents field elements by the naturals
`0, 1, ..., q - 1`, which requires the natural casts to exhaust `F`. The `ϕ` part of the
development makes no such assumption and therefore covers all *prime powers*. -/
lemma prime_of_natCast_surjective
  (hq_card : Fintype.card F = q)
  (hsurj : Function.Surjective (Nat.cast : ℕ → F))
  : q.Prime := by
    have h_char_prime : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
    -- Step 1: the cast `Fin (ringChar F) → F` is surjective.
    have h_surj : Function.Surjective (fun k : Fin (ringChar F) => ((k : ℕ) : F)) := by
      intro t
      obtain ⟨n, hn⟩ := hsurj t
      refine ⟨⟨n % ringChar F, Nat.mod_lt _ h_char_prime.pos⟩, ?_⟩
      simpa [CharP.cast_eq_mod F (ringChar F) n] using hn
    -- Step 2: the same cast is always injective below the characteristic - the defining
    -- property of `ringChar`.
    have h_inj : Function.Injective (fun k : Fin (ringChar F) => ((k : ℕ) : F)) := fun a b hab =>
      Fin.ext (CharP.natCast_injOn_Iio F (ringChar F) a.isLt b.isLt hab)
    -- Step 3: surjective gives `card F ≤ ringChar F`; injective gives `ringChar F ≤ card F`.
    -- Together, `card F = ringChar F` exactly.
    have h_le : Fintype.card F ≤ ringChar F := by simpa using Fintype.card_le_of_surjective _ h_surj
    have h_ge : ringChar F ≤ Fintype.card F := by simpa using Fintype.card_le_of_injective _ h_inj
    have h_eq : q = ringChar F := by omega
    rw [h_eq]
    exact h_char_prime

end Cslib.Crypto.Systems.Elligator.FiniteFieldBasic
