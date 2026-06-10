/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Separation.Defs
public import Cslib.Logics.Bimodal.Metalogic.Separation.Duality
public import Cslib.Logics.Bimodal.Metalogic.Separation.IntHelpers

set_option linter.style.emptyLine false

/-!
# Negation Equivalences (GHR94 Lemma 10.2.2)

## References

- GHR94, Lemma 10.2.2, p. 572
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Separation

variable {Atom : Type*}

/-- not U(A,B) <-> G(not A) v U(not A ^ not B, not A) -/
theorem neg_until_equiv
    (A B : Cslib.Logic.Bimodal.Formula Atom) :
    intEquiv
      (Cslib.Logic.Bimodal.Formula.neg (.untl A B))
      (Cslib.Logic.Bimodal.Formula.or
        (Cslib.Logic.Bimodal.Formula.allFuture
          (Cslib.Logic.Bimodal.Formula.neg A))
        (.untl
          (Cslib.Logic.Bimodal.Formula.and
            (Cslib.Logic.Bimodal.Formula.neg A)
            (Cslib.Logic.Bimodal.Formula.neg B))
          (Cslib.Logic.Bimodal.Formula.neg A))) := by
  intro M t
  rw [int_truth_neg, int_truth_or,
    int_truth_allFuture]
  -- Goal: ¬ intTruth M t (untl A B) ↔
  --   (∀ w > t, ¬intTruth M w A) ∨
  --   intTruth M t (untl (and (neg A) (neg B))
  --     (neg A))
  constructor
  · intro hnotU
    by_cases hG : ∀ w : ℤ, t < w →
        ¬ intTruth M w A
    · left; exact fun w hw =>
        (int_truth_neg M w A).mpr (hG w hw)
    · right
      push_neg at hG
      obtain ⟨w, hwt, hwA⟩ := hG
      have hexA : ∃ n, t < n ∧
          intTruth M n A := ⟨w, hwt, hwA⟩
      obtain ⟨u, htu, hAu, hminA⟩ :=
        Int.exists_least_above' hexA
      have hexnotB :
          ∃ r, t < r ∧ r < u ∧
            ¬ intTruth M r B := by
        by_contra hall; push_neg at hall
        exact hnotU ⟨u, htu, hAu,
          fun r hr1 hr2 => hall r hr1 hr2⟩
      have hexnotB' :
          ∃ n, t < n ∧
            ¬ intTruth M n B := by
        obtain ⟨r, hr1, _, hr3⟩ := hexnotB
        exact ⟨r, hr1, hr3⟩
      obtain ⟨m, htm, hnotBm, hminB⟩ :=
        Int.exists_least_above' hexnotB'
      have hmu : m < u := by
        obtain ⟨r, hr1, hr2, hr3⟩ := hexnotB
        by_contra hge; push_neg at hge
        exact hminB r hr1 (by omega) hr3
      refine ⟨m, htm, ?_, ?_⟩
      · rw [int_truth_and, int_truth_neg,
          int_truth_neg]
        exact ⟨fun hAm =>
          hminA m htm hmu hAm, hnotBm⟩
      · intro r htr hrm
        rw [int_truth_neg]
        exact hminA r htr
          (lt_trans hrm hmu)
  · intro hrhs huntl
    obtain ⟨u, htu, hAu, hBguard⟩ := huntl
    rcases hrhs with hG |
        ⟨m, htm, hAB, hnotAguard⟩
    · have := (int_truth_neg M u A).mp
        (hG u htu)
      exact this hAu
    · rw [int_truth_and, int_truth_neg,
        int_truth_neg] at hAB
      obtain ⟨hnotAm, hnotBm⟩ := hAB
      rcases lt_trichotomy m u with
        hmu | hmu | hmu
      · exact hnotBm (hBguard m htm hmu)
      · exact hnotAm (hmu ▸ hAu)
      · have := (int_truth_neg M u A).mp
          (hnotAguard u htu hmu)
        exact this hAu

/-- not S(A,B) <-> H(not A) v S(not A ^ not B, not A) -/
theorem neg_since_equiv
    (A B : Cslib.Logic.Bimodal.Formula Atom) :
    intEquiv
      (Cslib.Logic.Bimodal.Formula.neg (.snce A B))
      (Cslib.Logic.Bimodal.Formula.or
        (Cslib.Logic.Bimodal.Formula.allPast
          (Cslib.Logic.Bimodal.Formula.neg A))
        (.snce
          (Cslib.Logic.Bimodal.Formula.and
            (Cslib.Logic.Bimodal.Formula.neg A)
            (Cslib.Logic.Bimodal.Formula.neg B))
          (Cslib.Logic.Bimodal.Formula.neg A))) := by
  intro M t
  rw [int_truth_neg, int_truth_or,
    int_truth_allPast]
  constructor
  · intro hnotS
    by_cases hH : ∀ w : ℤ, w < t →
        ¬ intTruth M w A
    · left; exact fun w hw =>
        (int_truth_neg M w A).mpr (hH w hw)
    · right
      push_neg at hH
      obtain ⟨w, hwt, hwA⟩ := hH
      have hexA : ∃ n, n < t ∧
          intTruth M n A := ⟨w, hwt, hwA⟩
      obtain ⟨u, hut, hAu, hmaxA⟩ :=
        Int.exists_greatest_below' hexA
      have hexnotB :
          ∃ r, u < r ∧ r < t ∧
            ¬ intTruth M r B := by
        by_contra hall; push_neg at hall
        exact hnotS ⟨u, hut, hAu,
          fun r hr1 hr2 => hall r hr1 hr2⟩
      have hexnotB' :
          ∃ n, n < t ∧
            ¬ intTruth M n B := by
        obtain ⟨r, _, hr2, hr3⟩ := hexnotB
        exact ⟨r, hr2, hr3⟩
      obtain ⟨m, hmt, hnotBm, hmaxB⟩ :=
        Int.exists_greatest_below' hexnotB'
      have hum : u < m := by
        obtain ⟨r, hr1, hr2, hr3⟩ := hexnotB
        by_contra hge; push_neg at hge
        exact (hmaxB r (by omega) hr2) hr3
      refine ⟨m, hmt, ?_, ?_⟩
      · rw [int_truth_and, int_truth_neg,
          int_truth_neg]
        exact ⟨fun hAm =>
          hmaxA m hum hmt hAm, hnotBm⟩
      · intro r hmr hrt
        rw [int_truth_neg]
        exact hmaxA r
          (lt_trans hum hmr) hrt
  · intro hrhs hsnce
    obtain ⟨u, hut, hAu, hBguard⟩ := hsnce
    rcases hrhs with hH |
        ⟨m, hmt, hAB, hnotAguard⟩
    · have := (int_truth_neg M u A).mp
        (hH u hut)
      exact this hAu
    · rw [int_truth_and, int_truth_neg,
        int_truth_neg] at hAB
      obtain ⟨hnotAm, hnotBm⟩ := hAB
      rcases lt_trichotomy u m with
        hum | hum | hum
      · exact hnotBm (hBguard m hum hmt)
      · exact hnotAm (hum ▸ hAu)
      · have := (int_truth_neg M u A).mp
          (hnotAguard u hum hut)
        exact this hAu

end Cslib.Logic.Bimodal.Metalogic.Separation
