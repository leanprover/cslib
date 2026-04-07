/-
Copyright (c) 2026 Akhilesh Balaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.DA.Congr
public import Cslib.Computability.Languages.RegularLanguage
public import Cslib.Computability.Languages.Congruences.RightCongruence
public import Mathlib.Computability.Language
public import Mathlib.Data.Fintype.Card
public import Mathlib.CategoryTheory.Iso

@[expose] public section

/-! # All three subparts of the Myhill-Nerode Theorem for DFAs

(1) `L` regular iff. `∼_L` has a finite number of equivalence classes `N`.
(2) `N` is the number of states in the minimal DFA accepting `L`.
(3) The minimal DFA is unique up to unique isomorphism. That is, for any
    minimal DFA acceptor, there exists exactly one isomorphism from it to the
    following one:

  > Let each equivalence class `⟦ x ⟧` correspond to a state, and let state
  transitions be `a : ⟦ x ⟧ → ⟦ x a ⟧` for each `a ∈ Σ`.
  Let the starting state be `⟦ ϵ ⟧`, and the accepting states be `⟦ x ⟧` where
  `x ∈ L`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
* [T. Malkin, *COMS W3261: Computer Science Theory, Handout 3: The Myhill-Nerode Theorem
   and Implications*][Malkin2024]
-/

namespace Cslib

open Cslib
open scoped RightCongruence

open Language

namespace Automata.DA
open Acceptor

variable {α : Type} {l m : Language α}

def NerodeCongruence (l : Language α) : RightCongruence α where
  r x y := ∀ z, x ++ z ∈ l ↔ y ++ z ∈ l
  iseqv := ⟨fun _ _ => Iff.rfl, fun h z => (h z).symm, fun h_1 h_2 z => (h_1 z).trans (h_2 z)⟩
  right_cov := ⟨fun a {x y} (h : ∀ z, x ++ z ∈ l ↔ y ++ z ∈ l) z =>
    List.append_assoc x a z ▸ List.append_assoc y a z ▸ h (a ++ z)⟩

def NerodeCongruence.toFinAcc (l : Language α) : 
    DA.FinAcc (Quotient (NerodeCongruence l).eq) α :=
  letI c := NerodeCongruence l
  { c.toDA with
    accept := {q | Quotient.lift (fun x => x ∈ l) (by
      intro x y hxy
      simpa using hxy []) q} }

@[simp, scoped grind =]
theorem nerodecongruence_to_finacc_acc (l : Language α) :
    language (NerodeCongruence.toFinAcc l) = l := by
      ext x
      simp [NerodeCongruence.toFinAcc, language, Acceptor.Accepts]
      exact Iff.of_eq rfl

theorem nerodecongruence_accepts_apply
    (M : DA.FinAcc State α) (x y : List α) :
    (NerodeCongruence (language M)).r x y ↔
      ∀ z,
        M.mtr (M.mtr M.start x) z ∈ M.accept ↔
        M.mtr (M.mtr M.start y) z ∈ M.accept := by
  simp only [FLTS.mtr, ← List.foldl_append]
  rfl

theorem IsRegular.finite_range_nerode_quotient (h : l.IsRegular) :
    Finite (Quotient (NerodeCongruence l).eq) := by
  rcases IsRegular.iff_dfa.mp h with ⟨State, hFin, M, hM⟩
  rw [← hM]
  apply Finite.of_surjective
    (fun s : State => Quotient.mk (NerodeCongruence (language M)).eq
      (Classical.epsilon (fun x => M.mtr M.start x = s)))
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    exact ⟨M.mtr M.start x, Quotient.sound (by
      change (NerodeCongruence (language M)).r _ x
      rw [nerodecongruence_accepts_apply]
      intro z
      have heps : M.mtr M.start (Classical.epsilon
          (fun y => M.mtr M.start y = M.mtr M.start x)) = M.mtr M.start x :=
        @Classical.epsilon_spec _ (fun y => M.mtr M.start y = M.mtr M.start x) ⟨x, rfl⟩
      rw [heps])⟩

-- Myhill-Nerode (1)
@[simp, scoped grind =]
theorem IsRegular_iff_finite_eqv_cls_wrt_nerode {l : Language α} :
    l.IsRegular ↔ Finite (Quotient (NerodeCongruence l).eq) := by
    constructor
    · intro h
      exact IsRegular.finite_range_nerode_quotient h
    · intro h
      refine IsRegular.iff_dfa.mpr ⟨Quotient (NerodeCongruence l).eq, h,
          NerodeCongruence.toFinAcc l, nerodecongruence_to_finacc_acc l⟩
--

@[simp]
theorem lower_bound_num_states_dfa_acc {l : Language α} {M : DA.FinAcc States α}
  {ws : Finset (List α)} (hws : ∀ x ∈ ws, ∀ y ∈ ws, x ≠ y → ¬(NerodeCongruence l).r x y)
  (hM : language M = l) [Fintype States] :
    Fintype.card States ≥ ws.card := by
    classical
    by_contra h
    simp only [ge_iff_le, not_le] at h
    by_cases h_card : ws.card ≤ 1
    · exact (lt_of_lt_of_le h (le_trans h_card
      (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨M.start⟩)))).false
    · obtain ⟨x, hx, y, hy, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h
        (fun x _ => Finset.mem_univ (M.mtr M.start x))
      rw [← hM] at hws
      exact hws x hx y hy hne
        ((nerodecongruence_accepts_apply M x y).mpr (fun z => heq ▸ Iff.rfl))

-- Myhill-Nerode (2)
@[simp]
theorem minimum_dfa_states_eq_num_eqv_clss_nerode {M : DA.FinAcc States α}
  [Fintype States] [Fintype (Quotient (NerodeCongruence (language M)).eq)] :
    Fintype.card States ≥ Fintype.card (Quotient (NerodeCongruence (language M)).eq) := by
      classical
      let ws : Finset (List α) := Finset.univ.image
                (Quotient.out : Quotient (NerodeCongruence (language M)).eq → List α)
      have hws : ∀ x ∈ ws, ∀ y ∈ ws, x ≠ y → ¬(NerodeCongruence (language M)).r x y := by
        simp only [ws, Finset.mem_image, Finset.mem_univ, true_and]
        rintro _ ⟨qx, rfl⟩ _ ⟨qy, rfl⟩ hne h
        exact hne (by simpa using Quotient.sound h)
      have card_hws_eq_num_eqv_clss : ws.card = Fintype.card
                (Quotient (NerodeCongruence (language M)).eq) := by
        simp [ws, Finset.card_image_of_injective _ Quotient.out_injective]
      exact card_hws_eq_num_eqv_clss ▸ lower_bound_num_states_dfa_acc hws rfl
--

def IsMinimalAutomaton (M : DA.FinAcc States α)
  [Fintype States] [Fintype (Quotient (NerodeCongruence (language M)).eq)] :=
    Fintype.card States = Fintype.card (Quotient (NerodeCongruence (language M)).eq)

-- Myhill-Nerode (3)
/- L and two minimal DFAs M and N accepting L ~> Iso M N -/
@[simp]
theorem unique_minimal_dfa (M : DA.FinAcc States_M α) [Fintype States_M]
  [Fintype (Quotient (NerodeCongruence (language M)).eq)] (hMin : IsMinimalAutomaton M) :
    ∃! φ : States_M ≃ Quotient (NerodeCongruence (language M)).eq,
      ∀ x, φ (M.mtr M.start x) = ⟦x⟧ := by
  sorry
--

end Automata.DA
end Cslib
