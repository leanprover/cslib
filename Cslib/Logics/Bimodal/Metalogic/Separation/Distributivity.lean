/-
Copyright (c) 2026 Benjamin Brastmckie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brastmckie
-/

import Cslib.Logics.Bimodal.Metalogic.Separation.Defs

set_option linter.style.emptyLine false

/-!
# Distributivity Laws (GHR94 Lemma 10.2.1)

U and S distribute over boolean connectives. These are valid over ALL
linear flows of time (not just integers).

## Key Results

- `until_distrib_or_left`: U(A v B, C) <-> U(A,C) v U(B,C)
- `since_distrib_or_left`: S(A v B, C) <-> S(A,C) v S(B,C)
- `until_distrib_and_right`: U(A, B ^ C) <-> U(A,B) ^ U(A,C)
- `since_distrib_and_right`: S(A, B ^ C) <-> S(A,B) ^ S(A,C)

## References

- GHR94, Lemma 10.2.1, p. 571
-/

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Left Distributivity (Event over Disjunction) -/

/-- U distributes over disjunction in the event argument.
    U(A v B, C) <-> U(A,C) v U(B,C). -/
theorem until_distrib_or_left
    (A B C : Formula Atom) :
    int_equiv (.untl (Formula.or A B) C)
      (Formula.or (.untl A C) (.untl B C)) := by
  intro M t
  simp only [int_truth]
  constructor
  · rintro ⟨s, hts, hAB, hguard⟩ h_not_UA
    have hnotA : ¬ int_truth M s A :=
      fun hA => h_not_UA ⟨s, hts, hA, hguard⟩
    exact ⟨s, hts, hAB hnotA, hguard⟩
  · intro h_or
    by_cases hUA :
        ∃ s, t < s ∧ int_truth M s A ∧
          ∀ r, t < r → r < s → int_truth M r C
    · obtain ⟨s, hts, hA, hC⟩ := hUA
      exact ⟨s, hts, fun hnotA =>
        absurd hA hnotA, hC⟩
    · obtain ⟨s, hts, hB, hC⟩ := h_or hUA
      exact ⟨s, hts, fun _ => hB, hC⟩

/-- S distributes over disjunction in the event argument.
    S(A v B, C) <-> S(A,C) v S(B,C). -/
theorem since_distrib_or_left
    (A B C : Formula Atom) :
    int_equiv (.snce (Formula.or A B) C)
      (Formula.or (.snce A C) (.snce B C)) := by
  intro M t
  simp only [int_truth]
  constructor
  · rintro ⟨s, hst, hAB, hguard⟩ h_not_SA
    have hnotA : ¬ int_truth M s A :=
      fun hA => h_not_SA ⟨s, hst, hA, hguard⟩
    exact ⟨s, hst, hAB hnotA, hguard⟩
  · intro h_or
    by_cases hSA :
        ∃ s, s < t ∧ int_truth M s A ∧
          ∀ r, s < r → r < t → int_truth M r C
    · obtain ⟨s, hst, hA, hC⟩ := hSA
      exact ⟨s, hst, fun hnotA =>
        absurd hA hnotA, hC⟩
    · obtain ⟨s, hst, hB, hC⟩ := h_or hSA
      exact ⟨s, hst, fun _ => hB, hC⟩

/-! ## Right Distributivity (Guard over Conjunction) -/

/-- U distributes over conjunction in the guard argument.
    U(A, B ^ C) <-> U(A,B) ^ U(A,C).
    Uses linearity of the time order. -/
theorem until_distrib_and_right
    (A B C : Formula Atom) :
    int_equiv (.untl A (Formula.and B C))
      (Formula.and (.untl A B) (.untl A C)) := by
  intro M t
  simp only [int_truth]
  constructor
  · rintro ⟨s, hts, hA, hBC⟩
    intro h_imp
    apply h_imp
    · exact ⟨s, hts, hA, fun r hr1 hr2 => by
        have := hBC r hr1 hr2
        by_contra hnotB
        exact this (fun hB _ => hnotB hB)⟩
    · exact ⟨s, hts, hA, fun r hr1 hr2 => by
        have := hBC r hr1 hr2
        by_contra hnotC
        exact this (fun _ hC => hnotC hC)⟩
  · intro h_and
    by_contra h_not
    apply h_and
    intro ⟨s1, hts1, hA1, hB⟩
    intro ⟨s2, hts2, hA2, hC⟩
    apply h_not
    by_cases hle : s1 ≤ s2
    · exact ⟨s1, hts1, hA1,
        fun r hr1 hr2 => by
          intro h_imp_BC
          apply h_imp_BC
          · exact hB r hr1 hr2
          · exact hC r hr1
              (lt_of_lt_of_le hr2 hle)⟩
    · push_neg at hle
      exact ⟨s2, hts2, hA2,
        fun r hr1 hr2 => by
          intro h_imp_BC
          apply h_imp_BC
          · exact hB r hr1 (lt_trans hr2 hle)
          · exact hC r hr1 hr2⟩

/-- S distributes over conjunction in the guard argument.
    S(A, B ^ C) <-> S(A,B) ^ S(A,C). -/
theorem since_distrib_and_right
    (A B C : Formula Atom) :
    int_equiv (.snce A (Formula.and B C))
      (Formula.and (.snce A B) (.snce A C)) := by
  intro M t
  simp only [int_truth]
  constructor
  · rintro ⟨s, hst, hA, hBC⟩
    intro h_imp
    apply h_imp
    · exact ⟨s, hst, hA, fun r hr1 hr2 => by
        have := hBC r hr1 hr2
        by_contra hnotB
        exact this (fun hB _ => hnotB hB)⟩
    · exact ⟨s, hst, hA, fun r hr1 hr2 => by
        have := hBC r hr1 hr2
        by_contra hnotC
        exact this (fun _ hC => hnotC hC)⟩
  · intro h_and
    by_contra h_not
    apply h_and
    intro ⟨s1, hst1, hA1, hB⟩
    intro ⟨s2, hst2, hA2, hC⟩
    apply h_not
    by_cases hle : s2 ≤ s1
    · exact ⟨s1, hst1, hA1,
        fun r hr1 hr2 => by
          intro h_imp_BC
          apply h_imp_BC
          · exact hB r hr1 hr2
          · exact hC r
              (lt_of_le_of_lt hle hr1) hr2⟩
    · push_neg at hle
      exact ⟨s2, hst2, hA2,
        fun r hr1 hr2 => by
          intro h_imp_BC
          apply h_imp_BC
          · exact hB r (lt_trans hle hr1) hr2
          · exact hC r hr1 hr2⟩

end Cslib.Logic.Bimodal.Metalogic.Separation
