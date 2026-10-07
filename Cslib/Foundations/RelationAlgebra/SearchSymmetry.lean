/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.FastCatalogueProfiles
public import Mathlib.Data.Nat.Bitwise
public import Batteries.Data.Nat.Bitwise.Lemmas

/-!
# Partial lexicographic comparisons for canonical cycle masks

An atom permutation induces a permutation of cycle bits. Comparing the bits from most to
least significant determines whether the original mask is canonical. For partial assignments,
the checker overapproximates the possible comparison results. It can therefore reject a cube
whose masks are all noncanonical, or certify that a permutation is satisfied throughout a cube.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Search

open Code

/-- Lexicographic comparison of bounded bit sequences, with the highest index most significant. -/
def BitLexLess (left right : ℕ → Bool) (n : ℕ) : Prop :=
  ∃ i < n, left i = false ∧ right i = true ∧
    ∀ l < n, i < l → left l = right l

/-- The highest differing bit witnesses a strict numeric comparison. -/
theorem bitLexLess_of_lt {left right n : ℕ}
    (hl : left < 2 ^ n) (hr : right < 2 ^ n) (h : left < right) :
    BitLexLess (bitAt left) (bitAt right) n := by
  obtain ⟨i, hi, htop⟩ := Nat.exists_most_significant_bit (Nat.xor_ne_zero_iff.mpr h.ne)
  have hib : i < n := by
    by_contra hn
    have hl' := Code.testBit_eq_false_of_lt hl (Nat.le_of_not_gt hn)
    have hr' := Code.testBit_eq_false_of_lt hr (Nat.le_of_not_gt hn)
    simp [Nat.testBit_xor, hl', hr'] at hi
  have heq : ∀ l, i < l → left.testBit l = right.testBit l := by
    intro l hl
    have ht := htop l hl
    cases hb : left.testBit l <;> cases hc : right.testBit l <;>
      simp_all only [Nat.testBit_xor, Bool.false_bne, Bool.true_bne,
        Bool.not_false, Bool.not_true]
  have hbits : left.testBit i = false ∧ right.testBit i = true := by
    cases hli : left.testBit i <;> cases hri : right.testBit i
    · simp [Nat.testBit_xor, hli, hri] at hi
    · exact ⟨rfl, rfl⟩
    · have := Nat.lt_of_testBit i hri hli (fun l hl => (heq l hl).symm)
      omega
    · simp [Nat.testBit_xor, hli, hri] at hi
  exact ⟨i, hib, by simpa only [bitAt_eq_testBit] using hbits.1,
    by simpa only [bitAt_eq_testBit] using hbits.2,
    fun l _ hl => by simpa only [bitAt_eq_testBit] using heq l hl⟩

/-- An overapproximation of the possible comparison results. -/
structure ComparisonPossibilities where
  /-- A smaller left operand remains possible. -/
  less : Bool
  /-- Equal operands remain possible. -/
  equal : Bool
  /-- A greater left operand remains possible. -/
  greater : Bool

/-- Compare partial bit sequences, treating unknown distinct variables independently. -/
def comparisonPossibilities (same leftZero leftOne rightZero rightOne : ℕ → Bool) :
    ℕ → ComparisonPossibilities
  | 0 => ⟨false, true, false⟩
  | n + 1 =>
    if same n then comparisonPossibilities same leftZero leftOne rightZero rightOne n
    else
      let lower := comparisonPossibilities same leftZero leftOne rightZero rightOne n
      let eq := (leftZero n && rightZero n) || (leftOne n && rightOne n)
      ⟨(leftZero n && rightOne n) || (eq && lower.less),
        eq && lower.equal,
        (leftOne n && rightZero n) || (eq && lower.greater)⟩

/-- The advertised possible values include the actual value at each bounded position. -/
def CompatibleChoices (actual zero one : ℕ → Bool) (n : ℕ) : Prop :=
  ∀ i < n, (actual i = false → zero i = true) ∧ (actual i = true → one i = true)

private theorem equalBit_possible {left right leftZero leftOne rightZero rightOne : Bool}
    (hl : (left = false → leftZero = true) ∧ (left = true → leftOne = true))
    (hr : (right = false → rightZero = true) ∧ (right = true → rightOne = true))
    (he : left = right) :
    ((leftZero && rightZero) || (leftOne && rightOne)) = true := by
  cases left <;> cases right <;> simp_all

/-- Actual equality is included among the possible comparison results. -/
theorem comparisonPossibilities_equal
    {same leftZero leftOne rightZero rightOne left right : ℕ → Bool} {n : ℕ}
    (hl : CompatibleChoices left leftZero leftOne n)
    (hr : CompatibleChoices right rightZero rightOne n)
    (he : ∀ i < n, left i = right i) :
    (comparisonPossibilities same leftZero leftOne rightZero rightOne n).equal = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq := equalBit_possible (hl n (Nat.lt_succ_self n))
      (hr n (Nat.lt_succ_self n)) (he n (Nat.lt_succ_self n))
    have hlo := ih (fun i hi => hl i (Nat.lt_succ_of_lt hi))
      (fun i hi => hr i (Nat.lt_succ_of_lt hi)) (fun i hi => he i (Nat.lt_succ_of_lt hi))
    simp only [comparisonPossibilities]
    split <;> simp only [hlo, heq, Bool.true_and]

/-- An actual strict comparison is included among the possible comparison results. -/
theorem comparisonPossibilities_less
    {same leftZero leftOne rightZero rightOne left right : ℕ → Bool} {n : ℕ}
    (hl : CompatibleChoices left leftZero leftOne n)
    (hr : CompatibleChoices right rightZero rightOne n)
    (hs : ∀ i < n, same i = true → left i = right i)
    (hlt : BitLexLess left right n) :
    (comparisonPossibilities same leftZero leftOne rightZero rightOne n).less = true := by
  induction n with
  | zero => obtain ⟨i, hi, _⟩ := hlt; omega
  | succ n ih =>
    obtain ⟨i, hi, hli, hri, htop⟩ := hlt
    by_cases hin : i = n
    · subst i
      have hsame : same n = false := by
        cases h : same n
        · rfl
        · have := hs n (Nat.lt_succ_self n) h
          simp [hli, hri] at this
      have hl0 := (hl n (Nat.lt_succ_self n)).1 hli
      have hr1 := (hr n (Nat.lt_succ_self n)).2 hri
      simp [comparisonPossibilities, hsame, hl0, hr1]
    · have hin : i < n := by omega
      have hlo := ih (fun i hi => hl i (Nat.lt_succ_of_lt hi))
        (fun i hi => hr i (Nat.lt_succ_of_lt hi))
        (fun i hi => hs i (Nat.lt_succ_of_lt hi))
        ⟨i, hin, hli, hri, fun l hl => htop l (Nat.lt_succ_of_lt hl)⟩
      have heq := equalBit_possible (hl n (Nat.lt_succ_self n))
        (hr n (Nat.lt_succ_self n)) (htop n (Nat.lt_succ_self n) hin)
      simp only [comparisonPossibilities]
      split <;> simp only [hlo, heq, Bool.true_and, Bool.or_true]

private theorem comparisonPossibilities_swap
    (same leftZero leftOne rightZero rightOne : ℕ → Bool) (n : ℕ) :
    comparisonPossibilities same rightZero rightOne leftZero leftOne n =
      let original := comparisonPossibilities same leftZero leftOne rightZero rightOne n
      ⟨original.greater, original.equal, original.less⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [comparisonPossibilities]
    split
    · exact ih
    · simp only [ih, Bool.and_comm]

/-- An actual greater comparison is included among the possible comparison results. -/
theorem comparisonPossibilities_greater
    {same leftZero leftOne rightZero rightOne left right : ℕ → Bool} {n : ℕ}
    (hl : CompatibleChoices left leftZero leftOne n)
    (hr : CompatibleChoices right rightZero rightOne n)
    (hs : ∀ i < n, same i = true → left i = right i)
    (hlt : BitLexLess right left n) :
    (comparisonPossibilities same leftZero leftOne rightZero rightOne n).greater = true := by
  have h := comparisonPossibilities_less hr hl (fun i hi ht => (hs i hi ht).symm) hlt
  rw [comparisonPossibilities_swap] at h
  exact h

/-- Possible comparisons of a partial mask with its image under a cycle permutation. -/
def permutationPossibilities (r on off : ℕ) (permutation : ℕ → ℕ) :
    ComparisonPossibilities :=
  comparisonPossibilities (fun i => Nat.beq i (permutation i))
    (fun i => !bitAt on i) (fun i => !bitAt off i)
    (fun i => !bitAt on (permutation i)) (fun i => !bitAt off (permutation i)) r

/-- Every completion is strictly greater than its permuted profile. -/
def permutationConflict (r on off : ℕ) (permutation : ℕ → ℕ) : Bool :=
  let possible := permutationPossibilities r on off permutation
  !possible.less && !possible.equal

/-- Every completion is at most its permuted profile. -/
def permutationSettled (r on off : ℕ) (permutation : ℕ → ℕ) : Bool :=
  !(permutationPossibilities r on off permutation).greater

/-- Every comparison realized by a completion is included in the computed possibilities. -/
theorem permutationPossibilities_sound {r on off mask : ℕ} {permutation : ℕ → ℕ}
    (hbound : ∀ i < r, permutation i < r)
    (hon : ∀ i < r, bitAt on i = true → bitAt mask i = true)
    (hoff : ∀ i < r, bitAt off i = true → bitAt mask i = false)
    (hmask : mask < 2 ^ r) :
    let other := choiceMask (fun i : Fin r => bitAt mask (permutation i))
    let possible := permutationPossibilities r on off permutation
    (mask < other → possible.less = true) ∧
      (mask = other → possible.equal = true) ∧
        (other < mask → possible.greater = true) := by
  let other := choiceMask (fun i : Fin r => bitAt mask (permutation i))
  have hother : other < 2 ^ r := choiceMask_lt _
  have hbits (i : ℕ) (hi : i < r) : bitAt other i = bitAt mask (permutation i) :=
    bitAt_choiceMask (fun l : Fin r => bitAt mask (permutation l)) ⟨i, hi⟩
  have hl : CompatibleChoices (bitAt mask) (fun i => !bitAt on i)
      (fun i => !bitAt off i) r := by
    intro i hi
    constructor
    · intro hm
      cases hc : bitAt on i
      · simp only [hc, Bool.not_false]
      · have := hon i hi hc
        simp [hm] at this
    · intro hm
      cases hc : bitAt off i
      · simp only [hc, Bool.not_false]
      · have := hoff i hi hc
        simp [hm] at this
  have hr : CompatibleChoices (fun i => bitAt mask (permutation i))
      (fun i => !bitAt on (permutation i)) (fun i => !bitAt off (permutation i)) r :=
    fun i hi => hl (permutation i) (hbound i hi)
  have hs : ∀ i < r, Nat.beq i (permutation i) = true →
      bitAt mask i = bitAt mask (permutation i) := by
    intro i _ hi
    exact congrArg (bitAt mask) (Nat.beq_eq.mp hi)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply comparisonPossibilities_less hl hr hs
    obtain ⟨i, hi, hli, hri, htop⟩ := bitLexLess_of_lt hmask hother h
    exact ⟨i, hi, hli, (hbits i hi).symm.trans hri,
      fun l hl hlt => (htop l hl hlt).trans (hbits l hl)⟩
  · intro h
    apply comparisonPossibilities_equal hl hr
    intro i hi
    exact (congrArg (fun n => bitAt n i) h).trans (hbits i hi)
  · intro h
    apply comparisonPossibilities_greater hl hr hs
    obtain ⟨i, hi, hli, hri, htop⟩ := bitLexLess_of_lt hother hmask h
    exact ⟨i, hi, (hbits i hi).symm.trans hli, hri,
      fun l hl hlt => (hbits l hl).symm.trans (htop l hl hlt)⟩

/-- A conflict certificate excludes canonicality for every matching completion. -/
theorem permutationConflict_sound {r on off mask : ℕ} {permutation : ℕ → ℕ}
    (hbound : ∀ i < r, permutation i < r)
    (hon : ∀ i < r, bitAt on i = true → bitAt mask i = true)
    (hoff : ∀ i < r, bitAt off i = true → bitAt mask i = false)
    (hmask : mask < 2 ^ r)
    (hcheck : permutationConflict r on off permutation = true) :
    ¬mask ≤ choiceMask (fun i : Fin r => bitAt mask (permutation i)) := by
  have h := permutationPossibilities_sound hbound hon hoff hmask
  simp only [permutationConflict, Bool.and_eq_true, Bool.not_eq_true'] at hcheck
  intro hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · have := h.1 hlt
    simp [hcheck.1] at this
  · have := h.2.1 heq
    simp [hcheck.2] at this

/-- A settled comparison certifies canonicality against this permutation throughout the cube. -/
theorem permutationSettled_sound {r on off mask : ℕ} {permutation : ℕ → ℕ}
    (hbound : ∀ i < r, permutation i < r)
    (hon : ∀ i < r, bitAt on i = true → bitAt mask i = true)
    (hoff : ∀ i < r, bitAt off i = true → bitAt mask i = false)
    (hmask : mask < 2 ^ r)
    (hcheck : permutationSettled r on off permutation = true) :
    mask ≤ choiceMask (fun i : Fin r => bitAt mask (permutation i)) := by
  have h := permutationPossibilities_sound hbound hon hoff hmask
  simp only [permutationSettled, Bool.not_eq_true'] at hcheck
  by_contra hlt
  have := h.2.2 (Nat.lt_of_not_ge hlt)
  simp [hcheck] at this

end Cslib.RelationAlgebra.Search
