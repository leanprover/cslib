/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Cslib.Logics.Bimodal.Metalogic.Separation.Defs
import Cslib.Logics.Bimodal.Metalogic.Separation.NegationEquiv
import Cslib.Logics.Bimodal.Metalogic.Separation.Distributivity
import Cslib.Logics.Bimodal.Metalogic.Separation.IntHelpers

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

/-!
# Elimination Cases (GHR94 Lemma 10.2.3)

The eight elimination cases that form the core of the separation proof.
Each case eliminates a nested U from under an S, producing an equivalent
formula where U(A,B) appears only at top level (not under S).

## References

- GHR94, Lemma 10.2.3, pp. 572-580
-/

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal
open Classical

variable {Atom : Type*}

/-! ## Helper Lemmas -/

theorem u_free_s_free_imp_separated (φ : Formula Atom)
    (hu : is_U_free φ = true) (hs : is_S_free φ = true) :
    is_syntactically_separated φ = true := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp a b ih1 ih2 =>
    simp [is_syntactically_separated, is_U_free, is_S_free] at *
    exact ⟨ih1 hu.1 hs.1, ih2 hu.2 hs.2⟩
  | box _ => rfl
  | untl _ _ => simp [is_U_free] at hu
  | snce _ _ => simp [is_S_free] at hs

/-- U-free + S-free → separable. Public version for use across files. -/
theorem u_free_s_free_is_separable (φ : Formula Atom)
    (hu : is_U_free φ = true) (hs : is_S_free φ = true) :
    is_separable φ :=
  ⟨φ, u_free_s_free_imp_separated φ hu hs, int_equiv_refl φ⟩

theorem neg_separated {φ : Formula Atom} (h : is_syntactically_separated φ = true) :
    is_syntactically_separated (Formula.neg φ) = true := by
  simp [Formula.neg, is_syntactically_separated, h]

theorem and_separated {φ ψ : Formula Atom}
    (h1 : is_syntactically_separated φ = true) (h2 : is_syntactically_separated ψ = true) :
    is_syntactically_separated (Formula.and φ ψ) = true := by
  simp [Formula.and, Formula.neg, is_syntactically_separated, h1, h2]

/-! ## Case 1 -/

/-- The separated equivalent of S(a ∧ U(A,B), q) from Case 1.
    Structure: (S(a,q) ∧ S(a,B) ∧ B ∧ U(A,B)) ∨ (A ∧ S(a,B) ∧ S(a,q)) ∨ S(A∧q∧S(a,B)∧S(a,q), q) -/
def case1_psi (a q A B : Formula Atom) : Formula Atom :=
  Formula.or (Formula.or
    (Formula.and (Formula.and (Formula.and (.snce a q) (.snce a B)) B) (.untl A B))
    (Formula.and (Formula.and A (.snce a B)) (.snce a q)))
    (.snce (Formula.and (Formula.and (Formula.and A q) (.snce a B)) (.snce a q)) q)

set_option maxHeartbeats 800000 in
theorem elim_case_1 (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (ha' : is_S_free a = true) (_hq' : is_S_free q = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    ∃ psi : Formula Atom,
      int_equiv (.snce (Formula.and a (.untl A B)) q) psi ∧
      is_syntactically_separated psi = true := by
  refine ⟨case1_psi a q A B, ?_, ?_⟩
  · intro M t
    simp only [case1_psi]
    constructor
    · intro ⟨s, hst, hand, hq_guard⟩
      have ⟨ha_s, huntl⟩ := (int_truth_and M s a (.untl A B)).mp hand
      obtain ⟨u, hsu, hAu, hB_guard⟩ := huntl
      rcases lt_trichotomy u t with hut | hut | hut
      · apply (int_truth_or M t _ _).mpr; right
        refine ⟨u, hut, ?_, fun r hur hrt => hq_guard r (lt_trans hsu hur) hrt⟩
        rw [int_truth_and, int_truth_and, int_truth_and]
        exact ⟨⟨⟨hAu, hq_guard u hsu hut⟩, ⟨s, hsu, ha_s, hB_guard⟩⟩,
               ⟨s, hsu, ha_s, fun r hsr hru => hq_guard r hsr (lt_trans hru hut)⟩⟩
      · subst hut
        apply (int_truth_or M u _ _).mpr; left; apply (int_truth_or M u _ _).mpr; right
        rw [int_truth_and, int_truth_and]
        exact ⟨⟨hAu, ⟨s, hst, ha_s, hB_guard⟩⟩, ⟨s, hst, ha_s, hq_guard⟩⟩
      · apply (int_truth_or M t _ _).mpr; left; apply (int_truth_or M t _ _).mpr; left
        rw [int_truth_and, int_truth_and, int_truth_and]
        exact ⟨⟨⟨⟨s, hst, ha_s, hq_guard⟩,
               ⟨s, hst, ha_s, fun r hsr hrt => hB_guard r hsr (lt_trans hrt hut)⟩⟩,
               hB_guard t hst hut⟩,
               ⟨u, hut, hAu, fun r htr hru => hB_guard r (lt_trans hst htr) hru⟩⟩
    · intro hrhs
      rcases (int_truth_or M t _ _).mp hrhs with h12 | h3
      · rcases (int_truth_or M t _ _).mp h12 with hd1 | hd2
        · rw [int_truth_and, int_truth_and, int_truth_and] at hd1
          obtain ⟨⟨⟨⟨s₁, hs₁t, ha₁, hq₁⟩, ⟨s₂, hs₂t, ha₂, hB₂⟩⟩, hBt⟩,
                  ⟨u, htu, hAu, hBu⟩⟩ := hd1
          by_cases hle : s₁ ≤ s₂
          · refine ⟨s₂, hs₂t, (int_truth_and M s₂ a (.untl A B)).mpr ⟨ha₂,
              u, lt_trans hs₂t htu, hAu, fun r hrs hru => ?_⟩,
              fun r hrs hrt => hq₁ r (lt_of_le_of_lt hle hrs) hrt⟩
            rcases lt_trichotomy r t with hrt | hrt | hrt
            · exact hB₂ r hrs hrt
            · exact hrt ▸ hBt
            · exact hBu r hrt hru
          · push_neg at hle
            refine ⟨s₁, hs₁t, (int_truth_and M s₁ a (.untl A B)).mpr ⟨ha₁,
              u, lt_trans hs₁t htu, hAu, fun r hrs hru => ?_⟩, hq₁⟩
            rcases lt_trichotomy r t with hrt | hrt | hrt
            · exact hB₂ r (lt_trans hle hrs) hrt
            · exact hrt ▸ hBt
            · exact hBu r hrt hru
        · rw [int_truth_and, int_truth_and] at hd2
          obtain ⟨⟨hAt, ⟨s₁, hs₁t, ha₁, hB₁⟩⟩, ⟨s₂, hs₂t, ha₂, hq₂⟩⟩ := hd2
          by_cases hle : s₁ ≤ s₂
          · exact ⟨s₂, hs₂t, (int_truth_and M s₂ a (.untl A B)).mpr ⟨ha₂,
              t, hs₂t, hAt, fun r hrs hrt => hB₁ r (lt_of_le_of_lt hle hrs) hrt⟩, hq₂⟩
          · push_neg at hle
            exact ⟨s₁, hs₁t, (int_truth_and M s₁ a (.untl A B)).mpr ⟨ha₁, t, hs₁t, hAt, hB₁⟩,
              fun r hr1 hr2 => hq₂ r (lt_trans hle hr1) hr2⟩
      · obtain ⟨w, hwt, hw_and, hq_rest⟩ := h3
        rw [int_truth_and, int_truth_and, int_truth_and] at hw_and
        obtain ⟨⟨⟨hAw, hqw⟩, ⟨s₁, hs₁w, ha₁, hB₁⟩⟩, ⟨s₂, hs₂w, ha₂, hq₂⟩⟩ := hw_and
        by_cases hle : s₁ ≤ s₂
        · refine ⟨s₂, lt_trans hs₂w hwt, (int_truth_and M s₂ a (.untl A B)).mpr ⟨ha₂,
            w, hs₂w, hAw, fun r hrs hrw => hB₁ r (lt_of_le_of_lt hle hrs) hrw⟩,
            fun r hrs hrt => ?_⟩
          rcases lt_trichotomy r w with hrw | hrw | hrw
          · exact hq₂ r hrs hrw
          · exact hrw ▸ hqw
          · exact hq_rest r hrw hrt
        · push_neg at hle
          refine ⟨s₁, lt_trans hs₁w hwt, (int_truth_and M s₁ a (.untl A B)).mpr ⟨ha₁,
            w, hs₁w, hAw, hB₁⟩, fun r hrs hrt => ?_⟩
          rcases lt_trichotomy r w with hrw | hrw | hrw
          · exact hq₂ r (lt_trans hle hrs) hrw
          · exact hrw ▸ hqw
          · exact hq_rest r hrw hrt
  · simp [case1_psi, Formula.and, Formula.or, Formula.neg,
          is_syntactically_separated, is_U_free, ha, hq, hA, hB, hA', hB']
    exact ⟨u_free_s_free_imp_separated B hB hB',
           u_free_s_free_imp_separated A hA hA'⟩

/-! ## Generalized Case 1: S(a ^ U(A,B), q) without S-free a, q requirements

  The generalized version drops BOTH `is_S_free a` and `is_S_free q` from Case 1.
  This enables handling the snce case of Lemma 10.2.5 where the event and guard
  come from abstracted separated formulas (which are U-free but not S-free).

  The proof is identical to `elim_case_1` because the separation check for
  `case1_psi` never uses S-freeness of a or q:
  - `a` and `q` appear only under `snce` nodes, where U-freeness is the requirement
  - Only `A` and `B` need S-freeness (they appear under `untl` and as standalone
    terms where `u_free_s_free_imp_separated` is applied)
-/

set_option maxHeartbeats 800000 in
theorem elim_case_1_gen (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    ∃ psi : Formula Atom,
      int_equiv (.snce (Formula.and a (.untl A B)) q) psi ∧
      is_syntactically_separated psi = true := by
  refine ⟨case1_psi a q A B, ?_, ?_⟩
  · intro M t
    simp only [case1_psi]
    constructor
    · intro ⟨s, hst, hand, hq_guard⟩
      have ⟨ha_s, huntl⟩ := (int_truth_and M s a (.untl A B)).mp hand
      obtain ⟨u, hsu, hAu, hB_guard⟩ := huntl
      rcases lt_trichotomy u t with hut | hut | hut
      · apply (int_truth_or M t _ _).mpr; right
        refine ⟨u, hut, ?_, fun r hur hrt => hq_guard r (lt_trans hsu hur) hrt⟩
        rw [int_truth_and, int_truth_and, int_truth_and]
        exact ⟨⟨⟨hAu, hq_guard u hsu hut⟩, ⟨s, hsu, ha_s, hB_guard⟩⟩,
               ⟨s, hsu, ha_s, fun r hsr hru => hq_guard r hsr (lt_trans hru hut)⟩⟩
      · subst hut
        apply (int_truth_or M u _ _).mpr; left; apply (int_truth_or M u _ _).mpr; right
        rw [int_truth_and, int_truth_and]
        exact ⟨⟨hAu, ⟨s, hst, ha_s, hB_guard⟩⟩, ⟨s, hst, ha_s, hq_guard⟩⟩
      · apply (int_truth_or M t _ _).mpr; left; apply (int_truth_or M t _ _).mpr; left
        rw [int_truth_and, int_truth_and, int_truth_and]
        exact ⟨⟨⟨⟨s, hst, ha_s, hq_guard⟩,
               ⟨s, hst, ha_s, fun r hsr hrt => hB_guard r hsr (lt_trans hrt hut)⟩⟩,
               hB_guard t hst hut⟩,
               ⟨u, hut, hAu, fun r htr hru => hB_guard r (lt_trans hst htr) hru⟩⟩
    · intro hrhs
      rcases (int_truth_or M t _ _).mp hrhs with h12 | h3
      · rcases (int_truth_or M t _ _).mp h12 with hd1 | hd2
        · rw [int_truth_and, int_truth_and, int_truth_and] at hd1
          obtain ⟨⟨⟨⟨s₁, hs₁t, ha₁, hq₁⟩, ⟨s₂, hs₂t, ha₂, hB₂⟩⟩, hBt⟩,
                  ⟨u, htu, hAu, hBu⟩⟩ := hd1
          by_cases hle : s₁ ≤ s₂
          · refine ⟨s₂, hs₂t, (int_truth_and M s₂ a (.untl A B)).mpr ⟨ha₂,
              u, lt_trans hs₂t htu, hAu, fun r hrs hru => ?_⟩,
              fun r hrs hrt => hq₁ r (lt_of_le_of_lt hle hrs) hrt⟩
            rcases lt_trichotomy r t with hrt | hrt | hrt
            · exact hB₂ r hrs hrt
            · exact hrt ▸ hBt
            · exact hBu r hrt hru
          · push_neg at hle
            refine ⟨s₁, hs₁t, (int_truth_and M s₁ a (.untl A B)).mpr ⟨ha₁,
              u, lt_trans hs₁t htu, hAu, fun r hrs hru => ?_⟩, hq₁⟩
            rcases lt_trichotomy r t with hrt | hrt | hrt
            · exact hB₂ r (lt_trans hle hrs) hrt
            · exact hrt ▸ hBt
            · exact hBu r hrt hru
        · rw [int_truth_and, int_truth_and] at hd2
          obtain ⟨⟨hAt, ⟨s₁, hs₁t, ha₁, hB₁⟩⟩, ⟨s₂, hs₂t, ha₂, hq₂⟩⟩ := hd2
          by_cases hle : s₁ ≤ s₂
          · exact ⟨s₂, hs₂t, (int_truth_and M s₂ a (.untl A B)).mpr ⟨ha₂,
              t, hs₂t, hAt, fun r hrs hrt => hB₁ r (lt_of_le_of_lt hle hrs) hrt⟩, hq₂⟩
          · push_neg at hle
            exact ⟨s₁, hs₁t, (int_truth_and M s₁ a (.untl A B)).mpr ⟨ha₁, t, hs₁t, hAt, hB₁⟩,
              fun r hr1 hr2 => hq₂ r (lt_trans hle hr1) hr2⟩
      · obtain ⟨w, hwt, hw_and, hq_rest⟩ := h3
        rw [int_truth_and, int_truth_and, int_truth_and] at hw_and
        obtain ⟨⟨⟨hAw, hqw⟩, ⟨s₁, hs₁w, ha₁, hB₁⟩⟩, ⟨s₂, hs₂w, ha₂, hq₂⟩⟩ := hw_and
        by_cases hle : s₁ ≤ s₂
        · refine ⟨s₂, lt_trans hs₂w hwt, (int_truth_and M s₂ a (.untl A B)).mpr ⟨ha₂,
            w, hs₂w, hAw, fun r hrs hrw => hB₁ r (lt_of_le_of_lt hle hrs) hrw⟩,
            fun r hrs hrt => ?_⟩
          rcases lt_trichotomy r w with hrw | hrw | hrw
          · exact hq₂ r hrs hrw
          · exact hrw ▸ hqw
          · exact hq_rest r hrw hrt
        · push_neg at hle
          refine ⟨s₁, lt_trans hs₁w hwt, (int_truth_and M s₁ a (.untl A B)).mpr ⟨ha₁,
            w, hs₁w, hAw, hB₁⟩, fun r hrs hrt => ?_⟩
          rcases lt_trichotomy r w with hrw | hrw | hrw
          · exact hq₂ r (lt_trans hle hrs) hrw
          · exact hrw ▸ hqw
          · exact hq_rest r hrw hrt
  · simp [case1_psi, Formula.and, Formula.or, Formula.neg,
          is_syntactically_separated, is_U_free, ha, hq, hA, hB, hA', hB']
    exact ⟨u_free_s_free_imp_separated B hB hB',
           u_free_s_free_imp_separated A hA hA'⟩

set_option maxHeartbeats 800000 in
/-- case1_psi is int_equiv to S(a∧U, q) and syntactically separated.
    This is the non-existential form of elim_case_1_gen for direct formula access. -/
theorem case1_psi_properties (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    int_equiv (.snce (Formula.and a (.untl A B)) q) (case1_psi a q A B) ∧
    is_syntactically_separated (case1_psi a q A B) = true := by
  refine ⟨?_, ?_⟩
  · intro M t
    simp only [case1_psi]
    constructor
    · intro ⟨s, hst, hand, hq_guard⟩
      have ⟨ha_s, huntl⟩ := (int_truth_and M s a (.untl A B)).mp hand
      obtain ⟨u, hsu, hAu, hB_guard⟩ := huntl
      rcases lt_trichotomy u t with hut | hut | hut
      · apply (int_truth_or M t _ _).mpr; right
        refine ⟨u, hut, ?_, fun r hur hrt => hq_guard r (lt_trans hsu hur) hrt⟩
        rw [int_truth_and, int_truth_and, int_truth_and]
        exact ⟨⟨⟨hAu, hq_guard u hsu hut⟩, ⟨s, hsu, ha_s, hB_guard⟩⟩,
               ⟨s, hsu, ha_s, fun r hsr hru => hq_guard r hsr (lt_trans hru hut)⟩⟩
      · subst hut
        apply (int_truth_or M u _ _).mpr; left; apply (int_truth_or M u _ _).mpr; right
        rw [int_truth_and, int_truth_and]
        exact ⟨⟨hAu, ⟨s, hst, ha_s, hB_guard⟩⟩, ⟨s, hst, ha_s, hq_guard⟩⟩
      · apply (int_truth_or M t _ _).mpr; left; apply (int_truth_or M t _ _).mpr; left
        rw [int_truth_and, int_truth_and, int_truth_and]
        exact ⟨⟨⟨⟨s, hst, ha_s, hq_guard⟩,
               ⟨s, hst, ha_s, fun r hsr hrt => hB_guard r hsr (lt_trans hrt hut)⟩⟩,
               hB_guard t hst hut⟩,
               ⟨u, hut, hAu, fun r htr hru => hB_guard r (lt_trans hst htr) hru⟩⟩
    · intro hrhs
      rcases (int_truth_or M t _ _).mp hrhs with h12 | h3
      · rcases (int_truth_or M t _ _).mp h12 with hd1 | hd2
        · rw [int_truth_and, int_truth_and, int_truth_and] at hd1
          obtain ⟨⟨⟨⟨s₁, hs₁t, ha₁, hq₁⟩, ⟨s₂, hs₂t, ha₂, hB₂⟩⟩, hBt⟩,
                  ⟨u, htu, hAu, hBu⟩⟩ := hd1
          by_cases hle : s₁ ≤ s₂
          · refine ⟨s₂, hs₂t, (int_truth_and M s₂ a (.untl A B)).mpr ⟨ha₂,
              u, lt_trans hs₂t htu, hAu, fun r hrs hru => ?_⟩,
              fun r hrs hrt => hq₁ r (lt_of_le_of_lt hle hrs) hrt⟩
            rcases lt_trichotomy r t with hrt | hrt | hrt
            · exact hB₂ r hrs hrt
            · exact hrt ▸ hBt
            · exact hBu r hrt hru
          · push_neg at hle
            refine ⟨s₁, hs₁t, (int_truth_and M s₁ a (.untl A B)).mpr ⟨ha₁,
              u, lt_trans hs₁t htu, hAu, fun r hrs hru => ?_⟩, hq₁⟩
            rcases lt_trichotomy r t with hrt | hrt | hrt
            · exact hB₂ r (lt_trans hle hrs) hrt
            · exact hrt ▸ hBt
            · exact hBu r hrt hru
        · rw [int_truth_and, int_truth_and] at hd2
          obtain ⟨⟨hAt, ⟨s₁, hs₁t, ha₁, hB₁⟩⟩, ⟨s₂, hs₂t, ha₂, hq₂⟩⟩ := hd2
          by_cases hle : s₁ ≤ s₂
          · exact ⟨s₂, hs₂t, (int_truth_and M s₂ a (.untl A B)).mpr ⟨ha₂,
              t, hs₂t, hAt, fun r hrs hrt => hB₁ r (lt_of_le_of_lt hle hrs) hrt⟩, hq₂⟩
          · push_neg at hle
            exact ⟨s₁, hs₁t, (int_truth_and M s₁ a (.untl A B)).mpr ⟨ha₁, t, hs₁t, hAt, hB₁⟩,
              fun r hr1 hr2 => hq₂ r (lt_trans hle hr1) hr2⟩
      · obtain ⟨w, hwt, hw_and, hq_rest⟩ := h3
        rw [int_truth_and, int_truth_and, int_truth_and] at hw_and
        obtain ⟨⟨⟨hAw, hqw⟩, ⟨s₁, hs₁w, ha₁, hB₁⟩⟩, ⟨s₂, hs₂w, ha₂, hq₂⟩⟩ := hw_and
        by_cases hle : s₁ ≤ s₂
        · refine ⟨s₂, lt_trans hs₂w hwt, (int_truth_and M s₂ a (.untl A B)).mpr ⟨ha₂,
            w, hs₂w, hAw, fun r hrs hrw => hB₁ r (lt_of_le_of_lt hle hrs) hrw⟩,
            fun r hrs hrt => ?_⟩
          rcases lt_trichotomy r w with hrw | hrw | hrw
          · exact hq₂ r hrs hrw
          · exact hrw ▸ hqw
          · exact hq_rest r hrw hrt
        · push_neg at hle
          refine ⟨s₁, lt_trans hs₁w hwt, (int_truth_and M s₁ a (.untl A B)).mpr ⟨ha₁,
            w, hs₁w, hAw, hB₁⟩, fun r hrs hrt => ?_⟩
          rcases lt_trichotomy r w with hrw | hrw | hrw
          · exact hq₂ r (lt_trans hle hrs) hrw
          · exact hrw ▸ hqw
          · exact hq_rest r hrw hrt
  · simp [case1_psi, Formula.and, Formula.or, Formula.neg,
          is_syntactically_separated, is_U_free, ha, hq, hA, hB, hA', hB']
    exact ⟨u_free_s_free_imp_separated B hB hB',
           u_free_s_free_imp_separated A hA hA'⟩

/-! ## GHR94-Faithful Case 2: S(a ^ not U(A,B), q) — preserves single U-type

  GHR94 Lemma 10.2.3, item 2 (p. 574). The output is:
    [S(a, q ∧ ¬A) ∧ ¬A ∧ ¬U(A,B)]        ← d1: neg U(A,B) preserved as unit
    ∨ [¬A ∧ ¬B ∧ S(a, ¬A ∧ q)]            ← d2: U-free
    ∨ S(¬A ∧ ¬B ∧ q ∧ S(a, ¬A ∧ q), q)    ← d3: U-free

  The ONLY U in the output is U(A,B) inside ¬U(A,B) in d1.
  Disjuncts d2 and d3 are completely U-free.
  This preserves has_single_U_type for A, B.
-/

/-- The GHR94-faithful output formula for Case 2: S(a ∧ ¬U(A,B), q).
    d1 ∨ d2 ∨ d3 as described above. -/
def case2_psi (a q A B : Formula Atom) : Formula Atom :=
  -- d1: S(a, q ∧ ¬A) ∧ ¬A ∧ ¬U(A,B)
  let d1 := Formula.and (Formula.and
    (.snce a (Formula.and q (Formula.neg A)))
    (Formula.neg A))
    (Formula.neg (.untl A B))
  -- d2: ¬A ∧ ¬B ∧ S(a, ¬A ∧ q)
  let d2 := Formula.and (Formula.and (Formula.neg A) (Formula.neg B))
    (.snce a (Formula.and (Formula.neg A) q))
  -- d3: S(¬A ∧ ¬B ∧ q ∧ S(a, ¬A ∧ q), q)
  let d3 := .snce (Formula.and (Formula.and (Formula.and
    (Formula.neg A) (Formula.neg B)) q)
    (.snce a (Formula.and (Formula.neg A) q))) q
  Formula.or (Formula.or d1 d2) d3

set_option maxHeartbeats 3200000 in
/-- case2_psi is int_equiv to S(a∧¬U, q) and syntactically separated.
    This is the non-existential form of elim_case_2_gen for direct formula access. -/
theorem case2_psi_properties (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    int_equiv (.snce (Formula.and a (Formula.neg (.untl A B))) q) (case2_psi a q A B) ∧
    is_syntactically_separated (case2_psi a q A B) = true := by
  simp only [case2_psi]
  let d1 := Formula.and (Formula.and
    (.snce a (Formula.and q (Formula.neg A)))
    (Formula.neg A))
    (Formula.neg (.untl A B))
  let d2 := Formula.and (Formula.and (Formula.neg A) (Formula.neg B))
    (.snce a (Formula.and (Formula.neg A) q))
  let d3 := Formula.snce (Formula.and (Formula.and (Formula.and
    (Formula.neg A) (Formula.neg B)) q)
    (.snce a (Formula.and (Formula.neg A) q))) q
  refine ⟨?_, ?_⟩
  · -- Equivalence proof
    intro M t; constructor
    · -- Forward: S(a ∧ ¬U(A,B), q) at t → d1 ∨ d2 ∨ d3
      intro ⟨s, hst, hand, hqg⟩
      have ⟨ha_s, hnotU_s⟩ := (int_truth_and M s _ _).mp hand
      -- Apply neg_until_equiv at s: ¬U(A,B) ↔ G(¬A) ∨ U(¬A∧¬B, ¬A)
      rcases (int_truth_or M s _ _).mp ((neg_until_equiv A B M s).mp hnotU_s) with hGA | hU'
      · -- G branch: G_s(¬A) → d1
        have hGA_unf := (int_truth_all_future M s (Formula.neg A)).mp hGA
        have hA_t : ¬ int_truth M t A := (int_truth_neg M t A).mp (hGA_unf t hst)
        have hnotU_t : ¬ int_truth M t (.untl A B) := by
          intro ⟨u, htu, hAu, _⟩; exact ((int_truth_neg M u A).mp (hGA_unf u (lt_trans hst htu))) hAu
        have hS_qnA : int_truth M t (.snce a (Formula.and q (Formula.neg A))) :=
          ⟨s, hst, ha_s, fun r hr1 hr2 =>
            (int_truth_and M r q (Formula.neg A)).mpr ⟨hqg r hr1 hr2, hGA_unf r hr1⟩⟩
        apply (int_truth_or M t _ _).mpr; left; apply (int_truth_or M t _ _).mpr; left
        exact (int_truth_and M t _ _).mpr ⟨(int_truth_and M t _ _).mpr ⟨hS_qnA, hA_t⟩, hnotU_t⟩
      · -- U' branch: U_s(¬A∧¬B, ¬A) → d2 or d3
        obtain ⟨u, hsu, hABu, hnA_guard⟩ := hU'
        have ⟨hnotA_u, hnotB_u⟩ := (int_truth_and M u _ _).mp hABu
        have hnotA_u' : ¬ int_truth M u A := (int_truth_neg M u A).mp hnotA_u
        have hnotB_u' : ¬ int_truth M u B := (int_truth_neg M u B).mp hnotB_u
        rcases lt_trichotomy u t with hut | hut | hut
        · -- u < t: d3 — event at u, guard q on (u,t)
          have hS_inner : int_truth M u (.snce a (Formula.and (Formula.neg A) q)) :=
            ⟨s, hsu, ha_s, fun r hr1 hr2 =>
              (int_truth_and M r _ _).mpr ⟨hnA_guard r hr1 hr2, hqg r hr1 (lt_trans hr2 hut)⟩⟩
          have hq_u : int_truth M u q := hqg u hsu hut
          apply (int_truth_or M t _ _).mpr; right
          exact ⟨u, hut, (int_truth_and M u _ _).mpr
            ⟨(int_truth_and M u _ _).mpr ⟨(int_truth_and M u _ _).mpr ⟨hnotA_u, hnotB_u⟩, hq_u⟩,
             hS_inner⟩,
            fun r hr1 hr2 => hqg r (lt_trans hsu hr1) hr2⟩
        · -- u = t: d2
          have hS_nAq : int_truth M t (.snce a (Formula.and (Formula.neg A) q)) :=
            ⟨s, hst, ha_s, fun r hr1 hr2 =>
              (int_truth_and M r _ _).mpr ⟨hnA_guard r hr1 (hut ▸ hr2), hqg r hr1 hr2⟩⟩
          apply (int_truth_or M t _ _).mpr; left; apply (int_truth_or M t _ _).mpr; right
          exact (int_truth_and M t _ _).mpr ⟨(int_truth_and M t _ _).mpr ⟨hut ▸ hnotA_u, hut ▸ hnotB_u⟩, hS_nAq⟩
        · -- u > t: d1 — ¬U(A,B) at t follows from ¬A on (s,u) and ¬A∧¬B at u
          have hnotA_t : ¬ int_truth M t A := (int_truth_neg M t A).mp (hnA_guard t hst hut)
          have hnotU_t : ¬ int_truth M t (.untl A B) := by
            intro ⟨v, htv, hAv, hBguard⟩
            rcases lt_trichotomy v u with hvu | hvu | hvu
            · exact ((int_truth_neg M v A).mp (hnA_guard v (lt_trans hst htv) hvu)) hAv
            · exact hnotA_u' (hvu ▸ hAv)
            · exact hnotB_u' (hBguard u hut hvu)
          have hS_qnA : int_truth M t (.snce a (Formula.and q (Formula.neg A))) :=
            ⟨s, hst, ha_s, fun r hr1 hr2 =>
              (int_truth_and M r _ _).mpr ⟨hqg r hr1 hr2, hnA_guard r hr1 (lt_trans hr2 hut)⟩⟩
          apply (int_truth_or M t _ _).mpr; left; apply (int_truth_or M t _ _).mpr; left
          exact (int_truth_and M t _ _).mpr ⟨(int_truth_and M t _ _).mpr ⟨hS_qnA, hnotA_t⟩, hnotU_t⟩
    · -- Backward: d1 ∨ d2 ∨ d3 → S(a ∧ ¬U(A,B), q)
      intro h
      rcases (int_truth_or M t _ _).mp h with h12 | h3
      · rcases (int_truth_or M t _ _).mp h12 with hd1 | hd2
        · -- d1: S(a, q∧¬A) ∧ ¬A ∧ ¬U(A,B) at t
          rw [int_truth_and, int_truth_and] at hd1
          obtain ⟨⟨⟨s, hst, ha_s, hguard⟩, hA_t⟩, hnotU_t⟩ := hd1
          have hnotU_s : ¬ int_truth M s (.untl A B) := by
            intro ⟨u, hsu, hAu, hBguard⟩
            have hnA_on : ∀ r, s < r → r < t → ¬ int_truth M r A :=
              fun r hr1 hr2 => (int_truth_neg M r A).mp ((int_truth_and M r q (Formula.neg A)).mp (hguard r hr1 hr2)).2
            rcases lt_trichotomy u t with hut | hut | hut
            · exact hnA_on u hsu hut hAu
            · exact hA_t (hut ▸ hAu)
            · exact hnotU_t ⟨u, hut, hAu, fun r htr hru => hBguard r (lt_trans hst htr) hru⟩
          exact ⟨s, hst, (int_truth_and M s _ _).mpr ⟨ha_s, hnotU_s⟩,
            fun r hr1 hr2 => ((int_truth_and M r q (Formula.neg A)).mp (hguard r hr1 hr2)).1⟩
        · -- d2: ¬A ∧ ¬B ∧ S(a, ¬A∧q) at t
          rw [int_truth_and, int_truth_and] at hd2
          obtain ⟨⟨hnotA_t, hnotB_t⟩, ⟨s, hst, ha_s, hguard⟩⟩ := hd2
          have hnotU_s : ¬ int_truth M s (.untl A B) := by
            intro ⟨u, hsu, hAu, hBguard⟩
            have hnA_on : ∀ r, s < r → r < t → ¬ int_truth M r A :=
              fun r hr1 hr2 => (int_truth_neg M r A).mp ((int_truth_and M r _ _).mp (hguard r hr1 hr2)).1
            rcases lt_trichotomy u t with hut | hut | hut
            · exact hnA_on u hsu hut hAu
            · exact ((int_truth_neg M t A).mp hnotA_t) (hut ▸ hAu)
            · exact ((int_truth_neg M t B).mp hnotB_t) (hBguard t hst hut)
          exact ⟨s, hst, (int_truth_and M s _ _).mpr ⟨ha_s, hnotU_s⟩,
            fun r hr1 hr2 => ((int_truth_and M r _ _).mp (hguard r hr1 hr2)).2⟩
      · -- d3: S(¬A∧¬B∧q∧S(a,¬A∧q), q) at t
        obtain ⟨w, hwt, hw_event, hq_rest⟩ := h3
        rw [int_truth_and, int_truth_and, int_truth_and] at hw_event
        obtain ⟨⟨⟨hnotA_w, hnotB_w⟩, hq_w⟩, ⟨s, hsw, ha_s, hguard_inner⟩⟩ := hw_event
        have hnotU_s : ¬ int_truth M s (.untl A B) := by
          intro ⟨u, hsu, hAu, hBguard⟩
          have hnA_on : ∀ r, s < r → r < w → ¬ int_truth M r A :=
            fun r hr1 hr2 => (int_truth_neg M r A).mp ((int_truth_and M r _ _).mp (hguard_inner r hr1 hr2)).1
          rcases lt_trichotomy u w with huw | huw | huw
          · exact hnA_on u hsu huw hAu
          · exact ((int_truth_neg M w A).mp hnotA_w) (huw ▸ hAu)
          · exact ((int_truth_neg M w B).mp hnotB_w) (hBguard w hsw huw)
        exact ⟨s, lt_trans hsw hwt, (int_truth_and M s _ _).mpr ⟨ha_s, hnotU_s⟩,
          fun r hr1 hr2 => by
            rcases lt_trichotomy r w with hrw | hrw | hrw
            · exact ((int_truth_and M r _ _).mp (hguard_inner r hr1 hrw)).2
            · exact hrw ▸ hq_w
            · exact hq_rest r hrw hr2⟩
  · -- Separation check
    have hsep_A : is_syntactically_separated A = true := u_free_s_free_imp_separated A hA hA'
    have hsep_B : is_syntactically_separated B = true := u_free_s_free_imp_separated B hB hB'
    simp only [d1, d2, d3, Formula.or, Formula.and, Formula.neg,
      is_syntactically_separated, is_U_free, is_S_free, ha, hq, hA, hB, hA', hB',
      Bool.true_and, Bool.and_true, hsep_A, hsep_B]

set_option maxHeartbeats 3200000 in
/-- Case 2 generalized: S(a ∧ ¬U(A,B), q) → separated equivalent.
    Delegates to `case2_psi_properties` (non-existential form). -/
theorem elim_case_2_gen (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    ∃ psi : Formula Atom,
      int_equiv (.snce (Formula.and a (Formula.neg (.untl A B))) q) psi ∧
      is_syntactically_separated psi = true :=
  ⟨case2_psi a q A B, case2_psi_properties a q A B ha hq hA hB hA' hB'⟩

/-! ## Case 2: S(a ^ not U(A,B), q) -/

/-- Case 2 with S-free a, q: delegates to `elim_case_2_gen`. -/
theorem elim_case_2 (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (_ha' : is_S_free a = true) (_hq' : is_S_free q = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    ∃ psi : Formula Atom,
      int_equiv (.snce (Formula.and a (Formula.neg (.untl A B))) q) psi ∧
      is_syntactically_separated psi = true :=
  elim_case_2_gen a q A B ha hq hA hB hA' hB'

/-! ## Case 3: S(a, q v U(A,B)) -/

set_option maxHeartbeats 1200000 in
theorem elim_case_3 (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (ha' : is_S_free a = true) (hq' : is_S_free q = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    ∃ psi : Formula Atom,
      int_equiv (.snce a (Formula.or q (.untl A B))) psi ∧
      is_syntactically_separated psi = true := by
  have haq_Uf : is_U_free (Formula.and (Formula.neg a) (Formula.neg q)) = true := by
    simp [Formula.and, Formula.neg, is_U_free, ha, hq]
  have haq_Sf : is_S_free (Formula.and (Formula.neg a) (Formula.neg q)) = true := by
    simp [Formula.and, Formula.neg, is_S_free, ha', hq']
  have ha_neg_Uf : is_U_free (Formula.neg a) = true := by simp [Formula.neg, is_U_free, ha]
  have ha_neg_Sf : is_S_free (Formula.neg a) = true := by simp [Formula.neg, is_S_free, ha']
  obtain ⟨psi2, hequiv2, hsep2⟩ := elim_case_2
    (Formula.and (Formula.neg a) (Formula.neg q)) (Formula.neg a) A B
    haq_Uf ha_neg_Uf hA hB haq_Sf ha_neg_Sf hA' hB'
  have hsep_H : is_syntactically_separated (.all_past (Formula.neg a)) = true := by
    simp only [is_syntactically_separated_all_past, Formula.neg, is_U_free, ha, Bool.and_true]
  refine ⟨Formula.and (Formula.neg (.all_past (Formula.neg a))) (Formula.neg psi2), ?_, ?_⟩
  · intro M t; constructor
    · intro hS
      obtain ⟨s, hst, ha_s, hqU_guard⟩ := hS
      refine (int_truth_and M t _ _).mpr ⟨(int_truth_neg M t _).mpr
        (fun hH => (int_truth_all_past M t _).mp hH s hst ha_s), (int_truth_neg M t _).mpr ?_⟩
      intro hpsi2
      obtain ⟨s2, hs2t, hand2, hguard2⟩ := (hequiv2 M t).mpr hpsi2
      have ⟨haq2, hnotU2⟩ := (int_truth_and M s2 _ _).mp hand2
      have hna2 := ((int_truth_and M s2 _ _).mp haq2).1
      have hnq2 := ((int_truth_and M s2 _ _).mp haq2).2
      have hs_le : s ≤ s2 := by by_contra h; push_neg at h; exact hguard2 s h hst ha_s
      rcases eq_or_lt_of_le hs_le with heq | hlt
      · exact hna2 (heq ▸ ha_s)
      · rcases (int_truth_or M s2 _ _).mp (hqU_guard s2 hlt hs2t) with hq2 | hU2
        · exact hnq2 hq2
        · exact hnotU2 hU2
    · intro hand
      have ⟨hnotH, hnotPsi2⟩ := (int_truth_and M t _ _).mp hand
      have hnotH' := (int_truth_neg M t _).mp hnotH
      have hnotPsi2' := (int_truth_neg M t _).mp hnotPsi2
      have hnotS2 : ¬ int_truth M t (.snce (Formula.and (Formula.and (Formula.neg a) (Formula.neg q)) (Formula.neg (.untl A B))) (Formula.neg a)) :=
        fun hS2 => hnotPsi2' ((hequiv2 M t).mp hS2)
      by_contra hnotS
      rcases (int_truth_or M t _ _).mp ((neg_since_equiv a (Formula.or q (.untl A B)) M t).mp hnotS) with hH | hS_neg
      · exact hnotH' hH
      · obtain ⟨s, hst, hevent, hguard⟩ := hS_neg
        have ⟨hna_s, hnotQU_s⟩ := (int_truth_and M s _ _).mp hevent
        have hnotQ_s : ¬ int_truth M s q :=
          fun h => ((int_truth_neg M s _).mp hnotQU_s) ((int_truth_or M s _ _).mpr (Or.inl h))
        have hnotU_s : ¬ int_truth M s (.untl A B) :=
          fun h => ((int_truth_neg M s _).mp hnotQU_s) ((int_truth_or M s _ _).mpr (Or.inr h))
        exact hnotS2 ⟨s, hst, (int_truth_and M s _ _).mpr
          ⟨(int_truth_and M s _ _).mpr ⟨hna_s, hnotQ_s⟩, hnotU_s⟩, hguard⟩
  · exact and_separated (neg_separated hsep_H) (neg_separated hsep2)

/-! ## Case 4: S(a, q v not U(A,B)) -/

set_option maxHeartbeats 1200000 in
theorem elim_case_4 (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (ha' : is_S_free a = true) (hq' : is_S_free q = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    ∃ psi : Formula Atom,
      int_equiv (.snce a (Formula.or q (Formula.neg (.untl A B)))) psi ∧
      is_syntactically_separated psi = true := by
  have haq_Uf : is_U_free (Formula.and (Formula.neg a) (Formula.neg q)) = true := by
    simp [Formula.and, Formula.neg, is_U_free, ha, hq]
  have haq_Sf : is_S_free (Formula.and (Formula.neg a) (Formula.neg q)) = true := by
    simp [Formula.and, Formula.neg, is_S_free, ha', hq']
  have ha_neg_Uf : is_U_free (Formula.neg a) = true := by simp [Formula.neg, is_U_free, ha]
  have ha_neg_Sf : is_S_free (Formula.neg a) = true := by simp [Formula.neg, is_S_free, ha']
  obtain ⟨psi1, hequiv1, hsep1⟩ := elim_case_1
    (Formula.and (Formula.neg a) (Formula.neg q)) (Formula.neg a) A B
    haq_Uf ha_neg_Uf hA hB haq_Sf ha_neg_Sf hA' hB'
  have hsep_H : is_syntactically_separated (.all_past (Formula.neg a)) = true := by
    simp only [is_syntactically_separated_all_past, Formula.neg, is_U_free, ha, Bool.and_true]
  refine ⟨Formula.and (Formula.neg (.all_past (Formula.neg a))) (Formula.neg psi1), ?_, ?_⟩
  · intro M t; constructor
    · intro hS
      obtain ⟨s, hst, ha_s, hguard_S⟩ := hS
      refine (int_truth_and M t _ _).mpr ⟨(int_truth_neg M t _).mpr
        (fun hH => (int_truth_all_past M t _).mp hH s hst ha_s), (int_truth_neg M t _).mpr ?_⟩
      intro hpsi1
      obtain ⟨s1, hs1t, hevent1, hguard1⟩ := (hequiv1 M t).mpr hpsi1
      have ⟨haq1, hU1⟩ := (int_truth_and M s1 _ _).mp hevent1
      have hna1 := ((int_truth_and M s1 _ _).mp haq1).1
      have hnq1 := ((int_truth_and M s1 _ _).mp haq1).2
      have hs_le : s ≤ s1 := by by_contra h; push_neg at h; exact hguard1 s h hst ha_s
      rcases eq_or_lt_of_le hs_le with heq | hlt
      · exact hna1 (heq ▸ ha_s)
      · rcases (int_truth_or M s1 _ _).mp (hguard_S s1 hlt hs1t) with hq1 | hnotU1
        · exact hnq1 hq1
        · exact ((int_truth_neg M s1 _).mp hnotU1) hU1
    · intro hand
      have ⟨hnotH, hnotPsi1⟩ := (int_truth_and M t _ _).mp hand
      have hnotH' := (int_truth_neg M t _).mp hnotH
      have hnotPsi1' := (int_truth_neg M t _).mp hnotPsi1
      have hnotS1 : ¬ int_truth M t (.snce (Formula.and (Formula.and (Formula.neg a) (Formula.neg q)) (.untl A B)) (Formula.neg a)) :=
        fun hS1 => hnotPsi1' ((hequiv1 M t).mp hS1)
      by_contra hnotS
      rcases (int_truth_or M t _ _).mp ((neg_since_equiv a (Formula.or q (Formula.neg (.untl A B))) M t).mp hnotS) with hH | hS_neg
      · exact hnotH' hH
      · obtain ⟨s, hst, hevent, hguard⟩ := hS_neg
        have ⟨hna_s, hnotG⟩ := (int_truth_and M s _ _).mp hevent
        have hnotQ_s : ¬ int_truth M s q :=
          fun h => ((int_truth_neg M s _).mp hnotG) ((int_truth_or M s _ _).mpr (Or.inl h))
        have hU_s : int_truth M s (.untl A B) := by
          by_contra hnotU
          exact ((int_truth_neg M s _).mp hnotG)
            ((int_truth_or M s _ _).mpr (Or.inr ((int_truth_neg M s _).mpr hnotU)))
        exact hnotS1 ⟨s, hst, (int_truth_and M s _ _).mpr
          ⟨(int_truth_and M s _ _).mpr ⟨hna_s, hnotQ_s⟩, hU_s⟩, hguard⟩
  · exact and_separated (neg_separated hsep_H) (neg_separated hsep1)

/-- Case 3 generalized: drops S-free requirements on a, q. Only needs S-free A, B.
    The proof replaces elim_case_2 with elim_case_2_gen. -/
theorem elim_case_3_gen (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    ∃ psi : Formula Atom,
      int_equiv (.snce a (Formula.or q (.untl A B))) psi ∧
      is_syntactically_separated psi = true := by
  have haq_Uf : is_U_free (Formula.and (Formula.neg a) (Formula.neg q)) = true := by
    simp [is_U_free, ha, hq]
  have ha_neg_Uf : is_U_free (Formula.neg a) = true := by simp [is_U_free, ha]
  obtain ⟨psi2, hequiv2, hsep2⟩ := elim_case_2_gen
    (Formula.and (Formula.neg a) (Formula.neg q)) (Formula.neg a) A B
    haq_Uf ha_neg_Uf hA hB hA' hB'
  have hsep_H : is_syntactically_separated (.all_past (Formula.neg a)) = true := by
    simp only [is_syntactically_separated_all_past, Formula.neg, is_U_free, ha, Bool.and_true]
  refine ⟨Formula.and (Formula.neg (.all_past (Formula.neg a))) (Formula.neg psi2), ?_, ?_⟩
  · intro M t; constructor
    · intro hS
      obtain ⟨s, hst, ha_s, hqU_guard⟩ := hS
      refine (int_truth_and M t _ _).mpr ⟨(int_truth_neg M t _).mpr
        (fun hH => (int_truth_all_past M t _).mp hH s hst ha_s), (int_truth_neg M t _).mpr ?_⟩
      intro hpsi2
      obtain ⟨s2, hs2t, hand2, hguard2⟩ := (hequiv2 M t).mpr hpsi2
      have ⟨haq2, hnotU2⟩ := (int_truth_and M s2 _ _).mp hand2
      have hna2 := ((int_truth_and M s2 _ _).mp haq2).1
      have hnq2 := ((int_truth_and M s2 _ _).mp haq2).2
      have hs_le : s ≤ s2 := by by_contra h; push_neg at h; exact hguard2 s h hst ha_s
      rcases eq_or_lt_of_le hs_le with heq | hlt
      · exact hna2 (heq ▸ ha_s)
      · rcases (int_truth_or M s2 _ _).mp (hqU_guard s2 hlt hs2t) with hq2 | hU2
        · exact hnq2 hq2
        · exact hnotU2 hU2
    · intro hand
      have ⟨hnotH, hnotPsi2⟩ := (int_truth_and M t _ _).mp hand
      have hnotH' := (int_truth_neg M t _).mp hnotH
      have hnotPsi2' := (int_truth_neg M t _).mp hnotPsi2
      have hnotS2 : ¬ int_truth M t (.snce (Formula.and (Formula.and (Formula.neg a) (Formula.neg q)) (Formula.neg (.untl A B))) (Formula.neg a)) :=
        fun hS2 => hnotPsi2' ((hequiv2 M t).mp hS2)
      by_contra hnotS
      rcases (int_truth_or M t _ _).mp ((neg_since_equiv a (Formula.or q (.untl A B)) M t).mp hnotS) with hH | hS_neg
      · exact hnotH' hH
      · obtain ⟨s, hst, hevent, hguard⟩ := hS_neg
        have ⟨hna_s, hnotQU_s⟩ := (int_truth_and M s _ _).mp hevent
        have hnotQ_s : ¬ int_truth M s q :=
          fun h => ((int_truth_neg M s _).mp hnotQU_s) ((int_truth_or M s _ _).mpr (Or.inl h))
        have hnotU_s : ¬ int_truth M s (.untl A B) :=
          fun h => ((int_truth_neg M s _).mp hnotQU_s) ((int_truth_or M s _ _).mpr (Or.inr h))
        exact hnotS2 ⟨s, hst, (int_truth_and M s _ _).mpr
          ⟨(int_truth_and M s _ _).mpr ⟨hna_s, hnotQ_s⟩, hnotU_s⟩, hguard⟩
  · exact and_separated (neg_separated hsep_H) (neg_separated hsep2)

set_option maxHeartbeats 1200000 in
/-- Case 4 generalized: drops S-free requirements on a, q. Only needs S-free A, B.
    The proof replaces elim_case_1 with elim_case_1_gen. -/
theorem elim_case_4_gen (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    ∃ psi : Formula Atom,
      int_equiv (.snce a (Formula.or q (Formula.neg (.untl A B)))) psi ∧
      is_syntactically_separated psi = true := by
  have haq_Uf : is_U_free (Formula.and (Formula.neg a) (Formula.neg q)) = true := by
    simp [is_U_free, ha, hq]
  have ha_neg_Uf : is_U_free (Formula.neg a) = true := by simp [is_U_free, ha]
  obtain ⟨psi1, hequiv1, hsep1⟩ := elim_case_1_gen
    (Formula.and (Formula.neg a) (Formula.neg q)) (Formula.neg a) A B
    haq_Uf ha_neg_Uf hA hB hA' hB'
  have hsep_H : is_syntactically_separated (.all_past (Formula.neg a)) = true := by
    simp only [is_syntactically_separated_all_past, Formula.neg, is_U_free, ha, Bool.and_true]
  refine ⟨Formula.and (Formula.neg (.all_past (Formula.neg a))) (Formula.neg psi1), ?_, ?_⟩
  · intro M t; constructor
    · intro hS
      obtain ⟨s, hst, ha_s, hguard_S⟩ := hS
      refine (int_truth_and M t _ _).mpr ⟨(int_truth_neg M t _).mpr
        (fun hH => (int_truth_all_past M t _).mp hH s hst ha_s), (int_truth_neg M t _).mpr ?_⟩
      intro hpsi1
      obtain ⟨s1, hs1t, hevent1, hguard1⟩ := (hequiv1 M t).mpr hpsi1
      have ⟨haq1, hU1⟩ := (int_truth_and M s1 _ _).mp hevent1
      have hna1 := ((int_truth_and M s1 _ _).mp haq1).1
      have hnq1 := ((int_truth_and M s1 _ _).mp haq1).2
      have hs_le : s ≤ s1 := by by_contra h; push_neg at h; exact hguard1 s h hst ha_s
      rcases eq_or_lt_of_le hs_le with heq | hlt
      · exact hna1 (heq ▸ ha_s)
      · rcases (int_truth_or M s1 _ _).mp (hguard_S s1 hlt hs1t) with hq1 | hnotU1
        · exact hnq1 hq1
        · exact ((int_truth_neg M s1 _).mp hnotU1) hU1
    · intro hand
      have ⟨hnotH, hnotPsi1⟩ := (int_truth_and M t _ _).mp hand
      have hnotH' := (int_truth_neg M t _).mp hnotH
      have hnotPsi1' := (int_truth_neg M t _).mp hnotPsi1
      have hnotS1 : ¬ int_truth M t (.snce (Formula.and (Formula.and (Formula.neg a) (Formula.neg q)) (.untl A B)) (Formula.neg a)) :=
        fun hS1 => hnotPsi1' ((hequiv1 M t).mp hS1)
      by_contra hnotS
      rcases (int_truth_or M t _ _).mp ((neg_since_equiv a (Formula.or q (Formula.neg (.untl A B))) M t).mp hnotS) with hH | hS_neg
      · exact hnotH' hH
      · obtain ⟨s, hst, hevent, hguard⟩ := hS_neg
        have ⟨hna_s, hnotG⟩ := (int_truth_and M s _ _).mp hevent
        have hnotQ_s : ¬ int_truth M s q :=
          fun h => ((int_truth_neg M s _).mp hnotG) ((int_truth_or M s _ _).mpr (Or.inl h))
        have hU_s : int_truth M s (.untl A B) := by
          by_contra hnotU
          exact ((int_truth_neg M s _).mp hnotG)
            ((int_truth_or M s _ _).mpr (Or.inr ((int_truth_neg M s _).mpr hnotU)))
        exact hnotS1 ⟨s, hst, (int_truth_and M s _ _).mpr
          ⟨(int_truth_and M s _ _).mpr ⟨hna_s, hnotQ_s⟩, hU_s⟩, hguard⟩
  · exact and_separated (neg_separated hsep_H) (neg_separated hsep1)

/-! ## Case 5: S(a ^ U(A,B), q v U(A,B))

  Case 5 eliminates U(A,B) from a Since formula where U(A,B) appears
  in BOTH the event and guard positions.

  ### GHR94 Error on Integer Time

  GHR94 (p.370) gives an explicit formula for Case 5 that is INCORRECT
  for integer (discrete) time.

  **Resolution**: Cases 5-8 are proved using the separation theorem
  (`all_formulas_separable` from Hierarchy.lean), which establishes that
  every formula is separable via junction-depth induction (oracle-free).
-/

-- Note: Cases 5-8 are now proved in NormalForm.lean using `all_formulas_separable` from Hierarchy.lean.

/-! ## Separability Helpers -/

theorem is_separable_of_equiv {φ ψ : Formula Atom} (h : int_equiv φ ψ)
    (hs : is_separable ψ) : is_separable φ := by
  obtain ⟨χ, hχ_sep, hχ_equiv⟩ := hs
  exact ⟨χ, hχ_sep, int_equiv_trans h hχ_equiv⟩

theorem or_separable {φ ψ : Formula Atom}
    (h1 : is_separable φ) (h2 : is_separable ψ) : is_separable (Formula.or φ ψ) := by
  obtain ⟨φ', hφ', heφ⟩ := h1
  obtain ⟨ψ', hψ', heψ⟩ := h2
  refine ⟨Formula.or φ' ψ', ?_, ?_⟩
  · simp [is_syntactically_separated, hφ', hψ']
  · intro M t; constructor
    · intro h; rcases (int_truth_or M t _ _).mp h with hp | hq
      · exact (int_truth_or M t _ _).mpr (Or.inl ((heφ M t).mp hp))
      · exact (int_truth_or M t _ _).mpr (Or.inr ((heψ M t).mp hq))
    · intro h; rcases (int_truth_or M t _ _).mp h with hp | hq
      · exact (int_truth_or M t _ _).mpr (Or.inl ((heφ M t).mpr hp))
      · exact (int_truth_or M t _ _).mpr (Or.inr ((heψ M t).mpr hq))

theorem neg_separable {φ : Formula Atom}
    (h : is_separable φ) : is_separable (Formula.neg φ) := by
  obtain ⟨φ', hφ', heφ⟩ := h
  refine ⟨Formula.neg φ', neg_separated hφ', ?_⟩
  intro M t; constructor
  · intro hn hp; exact hn ((heφ M t).mpr hp)
  · intro hn hp; exact hn ((heφ M t).mp hp)

theorem and_separable {φ ψ : Formula Atom}
    (h1 : is_separable φ) (h2 : is_separable ψ) : is_separable (Formula.and φ ψ) := by
  obtain ⟨φ', hφ', heφ⟩ := h1
  obtain ⟨ψ', hψ', heψ⟩ := h2
  refine ⟨Formula.and φ' ψ', and_separated hφ' hψ', ?_⟩
  intro M t; constructor
  · intro h; rw [int_truth_and] at h ⊢
    exact ⟨(heφ M t).mp h.1, (heψ M t).mp h.2⟩
  · intro h; rw [int_truth_and] at h ⊢
    exact ⟨(heφ M t).mpr h.1, (heψ M t).mpr h.2⟩

theorem imp_separable {φ ψ : Formula Atom}
    (h1 : is_separable φ) (h2 : is_separable ψ) : is_separable (Formula.imp φ ψ) := by
  obtain ⟨φ', hφ', heφ⟩ := h1
  obtain ⟨ψ', hψ', heψ⟩ := h2
  refine ⟨Formula.imp φ' ψ', ?_, ?_⟩
  · simp [is_syntactically_separated, hφ', hψ']
  · intro M t; constructor
    · intro h hp; exact (heψ M t).mp (h ((heφ M t).mpr hp))
    · intro h hp; exact (heψ M t).mpr (h ((heφ M t).mp hp))

/-- Since-event splitting by classical LEM on an arbitrary formula:
    S(a, guard) ↔ S(a ^ φ, guard) ∨ S(a ^ ¬φ, guard) -/
theorem since_event_split (a φ guard : Formula Atom) :
    int_equiv (.snce a guard)
      (Formula.or (.snce (Formula.and a φ) guard)
                  (.snce (Formula.and a (Formula.neg φ)) guard)) := by
  intro M t; constructor
  · intro ⟨s, hst, ha, hg⟩
    by_cases hφ : int_truth M s φ
    · exact (int_truth_or M t _ _).mpr (Or.inl ⟨s, hst, (int_truth_and M s _ _).mpr ⟨ha, hφ⟩, hg⟩)
    · exact (int_truth_or M t _ _).mpr (Or.inr ⟨s, hst, (int_truth_and M s _ _).mpr ⟨ha, hφ⟩, hg⟩)
  · intro h; rcases (int_truth_or M t _ _).mp h with ⟨s, hst, hand, hg⟩ | ⟨s, hst, hand, hg⟩
    · exact ⟨s, hst, ((int_truth_and M s _ _).mp hand).1, hg⟩
    · exact ⟨s, hst, ((int_truth_and M s _ _).mp hand).1, hg⟩

/-- Guard weakening: S(event, stronger_guard) → S(event, weaker_guard) when
    stronger_guard implies weaker_guard pointwise. -/
theorem since_guard_weaken {event guard₁ guard₂ : Formula Atom}
    (h : ∀ M : IntStructure Atom, ∀ t : ℤ, int_truth M t guard₁ → int_truth M t guard₂)
    {M : IntStructure Atom} {t : ℤ} :
    int_truth M t (.snce event guard₁) → int_truth M t (.snce event guard₂) := by
  rintro ⟨s, hst, he, hg⟩
  exact ⟨s, hst, he, fun r hr1 hr2 => h M r (hg r hr1 hr2)⟩

/-! ## Cases 6-8

  Cases 6-8 involve ¬U(A,B) in the event and/or guard. Like Case 5,
  the explicit formulas are affected by the GHR94 discrete-time error.
  Their existence is proved via `all_formulas_separable` in NormalForm.lean.

  Case 6: S(a ^ ¬U(A,B), q ∨ U(A,B))
  Case 7: S(a ^ U(A,B), q ∨ ¬U(A,B))
  Case 8: S(a ^ ¬U(A,B), q ∨ ¬U(A,B))
-/

-- Note: Cases 6-8 theorems are now in NormalForm.lean (proved via all_formulas_separable).

end Cslib.Logic.Bimodal.Metalogic.Separation
