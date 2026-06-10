/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Separation.Defs
public import Cslib.Logics.Bimodal.Metalogic.Separation.Eliminations
public import Cslib.Logics.Bimodal.Metalogic.Separation.NegationEquiv

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

/-!
# K+/K- Operators and Q-Lemma for Dedekind-Complete Integer Orders

K+/K- definitions, Q-lemma (forward and backward), Q_Z syntactic properties,
and Case 3 equivalence for Z.
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal
open Classical

variable {Atom : Type*}

/-! ## K-plus, K-minus, Gamma Definitions -/

/-- K+(q) = not(U(top, not q)). Here top = neg bot = (bot -> bot). -/
def K_plus (q : Formula Atom) : Formula Atom :=
  Formula.neg (.untl (Formula.neg .bot) (Formula.neg q))

/-- K-(q) = not(S(top, not q)). -/
def K_minus (q : Formula Atom) : Formula Atom :=
  Formula.neg (.snce (Formula.neg .bot) (Formula.neg q))

/-- Gamma+(B) = not(K+(not B)) and K-(not B). -/
def Gamma_plus (B : Formula Atom) : Formula Atom :=
  Formula.and (Formula.neg (K_plus (Formula.neg B))) (K_minus (Formula.neg B))

/-- Gamma-(B) = not(K-(not B)) and K+(not B). -/
def Gamma_minus (B : Formula Atom) : Formula Atom :=
  Formula.and (Formula.neg (K_minus (Formula.neg B))) (K_plus (Formula.neg B))

/-! ## K+/K- Triviality on Z -/

/-- K+(q) is always false on integer time. -/
theorem K_plus_bot_on_Z (q : Formula Atom) (M : IntStructure Atom) (t : ℤ) :
    ¬ intTruth M t (K_plus q) := by
  simp only [K_plus, Formula.neg]
  intro h
  apply h
  refine ⟨t + 1, by omega, id, fun r htr hrs => ?_⟩
  exfalso; omega

/-- K-(q) is always false on integer time. -/
theorem K_minus_bot_on_Z (q : Formula Atom) (M : IntStructure Atom) (t : ℤ) :
    ¬ intTruth M t (K_minus q) := by
  simp only [K_minus, Formula.neg]
  intro h
  apply h
  refine ⟨t - 1, by omega, id, fun r hrs hrt => ?_⟩
  exfalso; omega

/-- Gamma+(B) is always false on integer time. -/
theorem Gamma_plus_bot_on_Z (B : Formula Atom) (M : IntStructure Atom) (t : ℤ) :
    ¬ intTruth M t (Gamma_plus B) := by
  simp only [Gamma_plus]
  intro h
  apply h
  intro _ hKm
  exact K_minus_bot_on_Z (Formula.neg B) M t hKm

/-- Gamma-(B) is always false on integer time. -/
theorem Gamma_minus_bot_on_Z (B : Formula Atom) (M : IntStructure Atom) (t : ℤ) :
    ¬ intTruth M t (Gamma_minus B) := by
  simp only [Gamma_minus]
  intro h
  apply h
  intro _ hKp
  exact K_plus_bot_on_Z (Formula.neg B) M t hKp

/-! ## Q-Lemma for Z (GHR94 Lemma 10.3.6 specialized) -/

/-- Q(A,B,C) on Z: the simplified Dedekind Q function.
    B or A or not(S(C, not A)) -/
def Q_Z (A B C : Formula Atom) : Formula Atom :=
  Formula.or (Formula.or B A) (Formula.neg (.snce C (Formula.neg A)))

/-! ## Q-Lemma Forward Direction -/

set_option maxHeartbeats 800000 in
-- Ported from BimodalLogic, heartbeats needed for case analysis
/-- Q-lemma forward direction for Z. -/
theorem Q_lemma_Z_fwd (A B C : Formula Atom) (M : IntStructure Atom) (t0 t1 : ℤ)
    (_ht : t0 < t1)
    (hguard : ∀ z : ℤ, t0 < z → z < t1 →
      (intTruth M z C → intTruth M z (.untl A B)))
    (hinit : intTruth M t0 (.untl A B)) :
    ∀ z : ℤ, t0 < z → z < t1 → intTruth M z (Q_Z A B C) := by
  intro z hz0 hz1
  rw [Q_Z, int_truth_or, int_truth_or, int_truth_neg]
  by_cases hS : intTruth M z (.snce C (Formula.neg A))
  · obtain ⟨u, huz, hCu, hnotA_guard⟩ := hS
    by_cases hut0 : t0 < u
    · have hut1 : u < t1 := lt_trans huz hz1
      obtain ⟨w, huw, hAw, hBgd⟩ := hguard u hut0 hut1 hCu
      by_cases hwz : w ≤ z
      · rcases eq_or_lt_of_le hwz with rfl | hwz'
        · exact Or.inl (Or.inr hAw)
        · exact absurd hAw ((int_truth_neg M w A).mp (hnotA_guard w huw hwz'))
      · push_neg at hwz
        exact Or.inl (Or.inl (hBgd z huz hwz))
    · push_neg at hut0
      obtain ⟨w, ht0w, hAw, hBgd⟩ := hinit
      by_cases hwz : w ≤ z
      · rcases eq_or_lt_of_le hwz with rfl | hwz'
        · exact Or.inl (Or.inr hAw)
        · have huw' : u < w := lt_of_le_of_lt hut0 ht0w
          exact absurd hAw ((int_truth_neg M w A).mp (hnotA_guard w huw' hwz'))
      · push_neg at hwz
        exact Or.inl (Or.inl (hBgd z hz0 hwz))
  · exact Or.inr hS

/-! ## Q-Lemma Backward Direction -/

set_option maxHeartbeats 1600000 in
-- Ported from BimodalLogic, heartbeats needed for complex case analysis
/-- Q-lemma backward direction for Z. -/
theorem Q_lemma_Z_bwd (A B C : Formula Atom) (M : IntStructure Atom) (t0 t1 : ℤ)
    (_ht : t0 < t1)
    (hQ : ∀ z : ℤ, t0 < z → z < t1 → intTruth M z (Q_Z A B C))
    (hend : intTruth M t1 A
          ∨ intTruth M t1 (Formula.and B (.untl A B))) :
    ∀ z : ℤ, t0 < z → z < t1 →
      (intTruth M z C → intTruth M z (.untl A B)) := by
  intro z hz0 hz1 hCz
  by_cases hA_exists : ∃ w : ℤ, z < w ∧ w ≤ t1 ∧ intTruth M w A
  · haveI : DecidablePred (fun w => intTruth M w A) := Classical.decPred _
    obtain ⟨w₀, hw₀⟩ := hA_exists
    have hex : ∃ n, z < n ∧ intTruth M n A := ⟨w₀, hw₀.1, hw₀.2.2⟩
    obtain ⟨y, hzy, hAy, hmin⟩ := Int.exists_least_above hex
    refine ⟨y, hzy, hAy, fun r hzr hry => ?_⟩
    have hnotAr : ¬ intTruth M r A := hmin r hzr hry
    have hyt1 : y ≤ t1 := by
      by_contra h; push_neg at h
      exact hmin w₀ hw₀.1 (lt_of_le_of_lt hw₀.2.1 h) hw₀.2.2
    have hrt1 : r < t1 := lt_of_lt_of_le hry hyt1
    have hrt0 : t0 < r := lt_trans hz0 hzr
    have hQr := hQ r hrt0 hrt1
    rw [Q_Z, int_truth_or, int_truth_or, int_truth_neg] at hQr
    rcases hQr with (hBr | hAr) | hnotS
    · exact hBr
    · exact absurd hAr hnotAr
    · exfalso; apply hnotS
      refine ⟨z, hzr, hCz, fun r' hr'z hr'r => ?_⟩
      exact hmin r' hr'z (lt_trans hr'r hry)
  · push_neg at hA_exists
    have hB_interval : ∀ r, z < r → r < t1 → intTruth M r B := by
      intro r hzr hrt1
      have hnotAr := hA_exists r hzr (le_of_lt hrt1)
      have hQr := hQ r (lt_trans hz0 hzr) hrt1
      rw [Q_Z, int_truth_or, int_truth_or, int_truth_neg] at hQr
      rcases hQr with (hBr | hAr) | hnotS
      · exact hBr
      · exact absurd hAr hnotAr
      · exfalso; apply hnotS
        refine ⟨z, hzr, hCz, fun r' hr'z hr'r => ?_⟩
        exact hA_exists r' hr'z (le_of_lt (lt_trans hr'r hrt1))
    rcases hend with hAt1 | hBUt1
    · exact absurd hAt1 (hA_exists t1 hz1 (le_refl t1))
    · have ⟨hBt1, hUt1⟩ := (int_truth_and M t1 _ _).mp hBUt1
      obtain ⟨w, ht1w, hAw, hBgd_w⟩ := hUt1
      refine ⟨w, lt_trans hz1 ht1w, hAw, fun r hzr hrw => ?_⟩
      rcases lt_trichotomy r t1 with hrt1 | hrt1 | hrt1
      · exact hB_interval r hzr hrt1
      · exact hrt1 ▸ hBt1
      · exact hBgd_w r hrt1 hrw

/-! ## Q_Z Syntactic Properties -/

/-- Q_Z(A,B,C) is U-free when A, B, C are U-free. -/
theorem Q_Z_U_free (A B C : Formula Atom)
    (hA : isUFree A = true) (hB : isUFree B = true) (hC : isUFree C = true) :
    isUFree (Q_Z A B C) = true := by
  simp [Q_Z, isUFree, hA, hB, hC]

/-- Q_Z(A,B,C) has noSNestedInU when A, B, C do. -/
theorem Q_Z_no_S_nested (A B C : Formula Atom)
    (hA : noSNestedInU A) (hB : noSNestedInU B) (hC : noSNestedInU C) :
    noSNestedInU (Q_Z A B C) := by
  simp only [Q_Z, Formula.or, Formula.neg]
  repeat (first | constructor | exact hA | exact hB | exact hC | trivial)

/-! ## Case 3 General Equivalence (GHR94 Lemma 10.3.11.3 for Z) -/

/-- General alpha for Case 3: a v (~q ^ S(a, q) ^ (q v U(A,B))) -/
def case3_alpha (a q A B : Formula Atom) : Formula Atom :=
  Formula.or a
    (Formula.and (Formula.and (Formula.neg q) (.snce a q))
      (Formula.or q (.untl A B)))

/-- Case 3 RHS for general event a -/
def case3_rhs (a q A B : Formula Atom) : Formula Atom :=
  let al := case3_alpha a q A B
  let qz := Q_Z A B (Formula.neg q)
  Formula.or (Formula.or
    (.snce a q)
    (Formula.and (.snce al qz)
      (Formula.or A (Formula.and B (.untl A B)))))
    (.snce (Formula.and (Formula.and A (Formula.or q (.untl A B)))
             (.snce al qz))
           q)

/-! ### Backward Direction: case3_rhs -> S(a, q v U(A,B)) -/

set_option maxHeartbeats 1600000 in
-- Ported from BimodalLogic
/-- Case 3 backward direction. -/
theorem case3_equiv_Z_bwd (a q A B : Formula Atom) (M : IntStructure Atom) (t : ℤ)
    (h : intTruth M t (case3_rhs a q A B)) :
    intTruth M t (.snce a (Formula.or q (.untl A B))) := by
  simp only [case3_rhs] at h
  rcases (int_truth_or M t _ _).mp h with h12 | h3
  · rcases (int_truth_or M t _ _).mp h12 with h1 | h2
    · obtain ⟨s, hst, ha_s, hq_guard⟩ := h1
      exact ⟨s, hst, ha_s, fun r hrs hrt =>
        (int_truth_or M r _ _).mpr (Or.inl (hq_guard r hrs hrt))⟩
    · have ⟨hSalpha, hABU⟩ := (int_truth_and M t _ _).mp h2
      obtain ⟨v, hvt, halpha_v, hQZ_guard⟩ := hSalpha
      simp only [case3_alpha] at halpha_v
      rcases (int_truth_or M v _ _).mp halpha_v with ha_v | halpha2
      · have hend_for_Q : intTruth M t A ∨ intTruth M t (Formula.and B (.untl A B)) := by
          rcases (int_truth_or M t _ _).mp hABU with hA | hBU
          · exact Or.inl hA
          · exact Or.inr hBU
        have hvt_lt : v < t := hvt
        have hCimplU := Q_lemma_Z_bwd A B (Formula.neg q) M v t hvt_lt hQZ_guard hend_for_Q
        refine ⟨v, hvt, ha_v, fun r hvr hrt => ?_⟩
        rw [int_truth_or]
        by_cases hqr : intTruth M r q
        · exact Or.inl hqr
        · exact Or.inr (hCimplU r hvr hrt hqr)
      · have ⟨hnq_and_Saq, hqU_v⟩ := (int_truth_and M v _ _).mp halpha2
        have ⟨_hnq_v, hSaq_v⟩ := (int_truth_and M v _ _).mp hnq_and_Saq
        obtain ⟨s, hsv, ha_s, hq_sv⟩ := hSaq_v
        have hend_for_Q : intTruth M t A ∨ intTruth M t (Formula.and B (.untl A B)) := by
          rcases (int_truth_or M t _ _).mp hABU with hA | hBU
          · exact Or.inl hA
          · exact Or.inr hBU
        have hCimplU := Q_lemma_Z_bwd A B (Formula.neg q) M v t hvt hQZ_guard hend_for_Q
        refine ⟨s, lt_trans hsv hvt, ha_s, fun r hsr hrt => ?_⟩
        rw [int_truth_or]
        rcases lt_trichotomy r v with hrv | hrv | hrv
        · exact Or.inl (hq_sv r hsr hrv)
        · subst hrv; exact (int_truth_or M r _ _).mp hqU_v
        · by_cases hqr : intTruth M r q
          · exact Or.inl hqr
          · exact Or.inr (hCimplU r hrv hrt hqr)
  · obtain ⟨u, hut, hevent_u, hq_guard⟩ := h3
    have ⟨hA_qU, hSalpha_u⟩ := (int_truth_and M u _ _).mp hevent_u
    have ⟨hA_u, hqU_u⟩ := (int_truth_and M u _ _).mp hA_qU
    obtain ⟨v, hvu, halpha_v, hQZ_vu⟩ := hSalpha_u
    simp only [case3_alpha] at halpha_v
    rcases (int_truth_or M v _ _).mp halpha_v with ha_v | halpha2
    · have hend_u : intTruth M u A ∨ intTruth M u (Formula.and B (.untl A B)) :=
        Or.inl hA_u
      have hCimplU := Q_lemma_Z_bwd A B (Formula.neg q) M v u hvu hQZ_vu hend_u
      refine ⟨v, lt_trans hvu hut, ha_v, fun r hvr hrt => ?_⟩
      rw [int_truth_or]
      rcases lt_trichotomy r u with hru | hru | hru
      · by_cases hqr : intTruth M r q
        · exact Or.inl hqr
        · exact Or.inr (hCimplU r hvr hru hqr)
      · subst hru; exact (int_truth_or M r _ _).mp hqU_u
      · exact Or.inl (hq_guard r hru hrt)
    · have ⟨hnq_and_Saq, _hqU_v⟩ := (int_truth_and M v _ _).mp halpha2
      have ⟨_hnq_v, hSaq_v⟩ := (int_truth_and M v _ _).mp hnq_and_Saq
      obtain ⟨s, hsv, ha_s, hq_sv⟩ := hSaq_v
      have hend_u : intTruth M u A ∨ intTruth M u (Formula.and B (.untl A B)) :=
        Or.inl hA_u
      have hCimplU := Q_lemma_Z_bwd A B (Formula.neg q) M v u hvu hQZ_vu hend_u
      refine ⟨s, lt_trans hsv (lt_trans hvu hut), ha_s, fun r hsr hrt => ?_⟩
      rw [int_truth_or]
      rcases lt_trichotomy r v with hrv | hrv | hrv
      · exact Or.inl (hq_sv r hsr hrv)
      · subst hrv
        rcases (int_truth_or M r _ _).mp _hqU_v with hqv | hUv
        · exact Or.inl hqv
        · exact Or.inr hUv
      · rcases lt_trichotomy r u with hru | hru | hru
        · by_cases hqr : intTruth M r q
          · exact Or.inl hqr
          · exact Or.inr (hCimplU r hrv hru hqr)
        · subst hru; exact (int_truth_or M r _ _).mp hqU_u
        · exact Or.inl (hq_guard r hru hrt)

/-! ### Forward Direction: S(a, q v U(A,B)) -> case3_rhs -/

set_option maxHeartbeats 3200000 in
-- Ported from BimodalLogic, heartbeats needed for complex case analysis
/-- Case 3 forward direction. -/
theorem case3_equiv_Z_fwd (a q A B : Formula Atom) (M : IntStructure Atom) (t : ℤ)
    (h : intTruth M t (.snce a (Formula.or q (.untl A B)))) :
    intTruth M t (case3_rhs a q A B) := by
  obtain ⟨s, hst, ha_s, hguard⟩ := h
  by_cases hq_all : ∀ r, s < r → r < t → intTruth M r q
  · simp only [case3_rhs]
    apply (int_truth_or M t _ _).mpr; left; apply (int_truth_or M t _ _).mpr; left
    exact ⟨s, hst, ha_s, hq_all⟩
  · push_neg at hq_all
    obtain ⟨f, hsf, hft, hnqf⟩ := hq_all
    haveI : DecidablePred (fun r => ¬intTruth M r q) := Classical.decPred _
    have hex_fail : ∃ n, s < n ∧ ¬intTruth M n q := ⟨f, hsf, hnqf⟩
    obtain ⟨f₀, hsf₀, hnqf₀, hf₀_min⟩ := Int.exists_least_above hex_fail
    have hq_left : ∀ r, s < r → r < f₀ → intTruth M r q := by
      intro r hsr hrf₀; by_contra hnq; exact hf₀_min r hsr hrf₀ hnq
    have hf₀t : f₀ < t := by
      by_contra hle; push_neg at hle
      have hff₀ : f < f₀ := lt_of_lt_of_le hft hle
      exact hf₀_min f hsf hff₀ hnqf
    by_cases hq_right : ∀ r, f₀ < r → r < t → intTruth M r q
    · have hqU_f₀ := hguard f₀ hsf₀ hf₀t
      have hU_f₀ : intTruth M f₀ (.untl A B) := by
        rcases (int_truth_or M f₀ _ _).mp hqU_f₀ with hq | hU
        · exact absurd hq hnqf₀
        · exact hU
      have hU_f₀_copy := hU_f₀
      obtain ⟨w, hf₀w, hAw, hBguard_w⟩ := hU_f₀_copy
      have hSaq_f₀ : intTruth M f₀ (.snce a q) :=
        ⟨s, hsf₀, ha_s, hq_left⟩
      have halpha_f₀ : intTruth M f₀ (case3_alpha a q A B) := by
        simp only [case3_alpha]
        apply (int_truth_or M f₀ _ _).mpr; right
        exact (int_truth_and M f₀ _ _).mpr
          ⟨(int_truth_and M f₀ _ _).mpr ⟨hnqf₀, hSaq_f₀⟩, hqU_f₀⟩
      have hQ_on_interval : ∀ z, f₀ < z → z < t → intTruth M z (Q_Z A B (Formula.neg q)) := by
        apply Q_lemma_Z_fwd A B (Formula.neg q) M f₀ t hf₀t
        · intro z hz0 hz1 hC
          exact absurd (hq_right z hz0 hz1) hC
        · exact hU_f₀
      have hSalpha_t : intTruth M t (.snce (case3_alpha a q A B) (Q_Z A B (Formula.neg q))) :=
        ⟨f₀, hf₀t, halpha_f₀, hQ_on_interval⟩
      rcases le_or_gt w t with hwt | htw
      · rcases eq_or_lt_of_le hwt with rfl | hwt'
        · simp only [case3_rhs]
          apply (int_truth_or M w _ _).mpr; left; apply (int_truth_or M w _ _).mpr; right
          exact (int_truth_and M w _ _).mpr ⟨hSalpha_t, (int_truth_or M w _ _).mpr (Or.inl hAw)⟩
        · have hqw : intTruth M w q := hq_right w hf₀w hwt'
          have hqU_w : intTruth M w (Formula.or q (.untl A B)) :=
            (int_truth_or M w _ _).mpr (Or.inl hqw)
          have hSalpha_w : intTruth M w (.snce (case3_alpha a q A B) (Q_Z A B (Formula.neg q))) :=
            ⟨f₀, hf₀w, halpha_f₀, fun z hz1 hz2 => hQ_on_interval z hz1 (lt_trans hz2 hwt')⟩
          have hevent_w : intTruth M w (Formula.and (Formula.and A (Formula.or q (.untl A B)))
               (.snce (case3_alpha a q A B) (Q_Z A B (Formula.neg q)))) :=
            (int_truth_and M w _ _).mpr ⟨(int_truth_and M w _ _).mpr ⟨hAw, hqU_w⟩, hSalpha_w⟩
          simp only [case3_rhs]
          apply (int_truth_or M t _ _).mpr; right
          exact ⟨w, hwt', hevent_w, fun r hwr hrt => hq_right r (lt_trans hf₀w hwr) hrt⟩
      · have hBt : intTruth M t B := hBguard_w t hf₀t htw
        have hUt : intTruth M t (.untl A B) :=
          ⟨w, htw, hAw, fun r htr hrw => hBguard_w r (lt_trans hf₀t htr) hrw⟩
        simp only [case3_rhs]
        apply (int_truth_or M t _ _).mpr; left; apply (int_truth_or M t _ _).mpr; right
        exact (int_truth_and M t _ _).mpr ⟨hSalpha_t, (int_truth_or M t _ _).mpr (Or.inr ((int_truth_and M t _ _).mpr ⟨hBt, hUt⟩))⟩
    · push_neg at hq_right
      obtain ⟨f₁, hf₀f₁, hf₁t, hnqf₁⟩ := hq_right
      haveI : DecidablePred (fun r => ¬intTruth M r q) := Classical.decPred _
      have hex_fail2 : ∃ n, n < t ∧ ¬intTruth M n q := ⟨f₁, hf₁t, hnqf₁⟩
      obtain ⟨g, hgt, hnqg, hg_max⟩ := Int.exists_greatest_below hex_fail2
      have hq_after_g : ∀ r, g < r → r < t → intTruth M r q := by
        intro r hgr hrt; by_contra hnq; exact hg_max r hgr hrt hnq
      have hf₀g : f₀ ≤ g := by
        by_contra hlt; push_neg at hlt
        exact hg_max f₀ hlt hf₀t hnqf₀
      have hsg : s < g := lt_of_lt_of_le hsf₀ hf₀g
      have hU_g : intTruth M g (.untl A B) := by
        have := hguard g hsg hgt
        rcases (int_truth_or M g _ _).mp this with hq | hU
        · exact absurd hq hnqg
        · exact hU
      obtain ⟨w, hgw, hAw, hBguard_w⟩ := hU_g
      have hSaq_f₀ : intTruth M f₀ (.snce a q) :=
        ⟨s, hsf₀, ha_s, hq_left⟩
      have hqU_f₀ := hguard f₀ hsf₀ hf₀t
      have halpha_f₀ : intTruth M f₀ (case3_alpha a q A B) := by
        simp only [case3_alpha]
        apply (int_truth_or M f₀ _ _).mpr; right
        exact (int_truth_and M f₀ _ _).mpr
          ⟨(int_truth_and M f₀ _ _).mpr ⟨hnqf₀, hSaq_f₀⟩, hqU_f₀⟩
      have hguard_full : ∀ z, f₀ < z → z < t → (intTruth M z (Formula.neg q) → intTruth M z (.untl A B)) := by
        intro z hf₀z hzt hnqz
        have hsz : s < z := lt_trans hsf₀ hf₀z
        rcases (int_truth_or M z _ _).mp (hguard z hsz hzt) with hq | hU
        · exact absurd hq hnqz
        · exact hU
      have hU_f₀ : intTruth M f₀ (.untl A B) := by
        rcases (int_truth_or M f₀ _ _).mp hqU_f₀ with hq | hU
        · exact absurd hq hnqf₀
        · exact hU
      have hQ_full : ∀ z, f₀ < z → z < t → intTruth M z (Q_Z A B (Formula.neg q)) :=
        Q_lemma_Z_fwd A B (Formula.neg q) M f₀ t hf₀t hguard_full hU_f₀
      have hSalpha_t : intTruth M t (.snce (case3_alpha a q A B) (Q_Z A B (Formula.neg q))) :=
        ⟨f₀, hf₀t, halpha_f₀, hQ_full⟩
      rcases le_or_gt w t with hwt | htw
      · rcases eq_or_lt_of_le hwt with rfl | hwt'
        · simp only [case3_rhs]
          apply (int_truth_or M w _ _).mpr; left; apply (int_truth_or M w _ _).mpr; right
          exact (int_truth_and M w _ _).mpr ⟨hSalpha_t, (int_truth_or M w _ _).mpr (Or.inl hAw)⟩
        · have hqw : intTruth M w q := hq_after_g w hgw hwt'
          have hqU_w : intTruth M w (Formula.or q (.untl A B)) :=
            (int_truth_or M w _ _).mpr (Or.inl hqw)
          have hSalpha_w : intTruth M w (.snce (case3_alpha a q A B) (Q_Z A B (Formula.neg q))) :=
            ⟨f₀, lt_of_le_of_lt hf₀g hgw, halpha_f₀,
              fun z hz1 hz2 => hQ_full z hz1 (lt_trans hz2 hwt')⟩
          have hevent_w : intTruth M w (Formula.and (Formula.and A (Formula.or q (.untl A B)))
               (.snce (case3_alpha a q A B) (Q_Z A B (Formula.neg q)))) :=
            (int_truth_and M w _ _).mpr ⟨(int_truth_and M w _ _).mpr ⟨hAw, hqU_w⟩, hSalpha_w⟩
          simp only [case3_rhs]
          apply (int_truth_or M t _ _).mpr; right
          exact ⟨w, hwt', hevent_w, fun r hwr hrt => hq_after_g r (lt_trans hgw hwr) hrt⟩
      · have hBt : intTruth M t B := hBguard_w t hgt htw
        have hUt : intTruth M t (.untl A B) :=
          ⟨w, htw, hAw, fun r htr hrw => hBguard_w r (lt_trans hgt htr) hrw⟩
        simp only [case3_rhs]
        apply (int_truth_or M t _ _).mpr; left; apply (int_truth_or M t _ _).mpr; right
        exact (int_truth_and M t _ _).mpr ⟨hSalpha_t, (int_truth_or M t _ _).mpr (Or.inr ((int_truth_and M t _ _).mpr ⟨hBt, hUt⟩))⟩

/-- Case 3 general equivalence for Z. -/
theorem case3_equiv_Z_general (a q A B : Formula Atom) :
    intEquiv (.snce a (Formula.or q (.untl A B))) (case3_rhs a q A B) :=
  fun M t => ⟨case3_equiv_Z_fwd a q A B M t, case3_equiv_Z_bwd a q A B M t⟩

end Cslib.Logic.Bimodal.Metalogic.Separation
