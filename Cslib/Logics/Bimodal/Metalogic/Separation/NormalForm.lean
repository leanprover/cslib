/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Separation.Eliminations
public import Cslib.Logics.Bimodal.Metalogic.Separation.Distributivity
public import Cslib.Logics.Bimodal.Metalogic.Separation.DedekindZ.Cases

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# Normal Form Reduction (GHR94 Lemma 10.2.4)

Proves that any formula `S(C, F)` where C and F contain a single U-formula type
U(A,B) (with A, B S-free) at top level only is separable. This uses the 8
elimination cases (Cases 1-4 proved, Cases 5-8 via DedekindZ) to decompose the
Since formula into separable components.
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal
open Classical

variable {Atom : Type*} [DecidableEq Atom]

/-! ## Separability of U-free Formulas -/

/-- A formula that is both U-free and S-free is syntactically separated. -/
theorem u_free_s_free_separated (φ : Formula Atom)
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

/-- A formula that is both U-free and S-free is separable. -/
theorem u_free_s_free_separable (φ : Formula Atom)
    (hu : is_U_free φ = true) (hs : is_S_free φ = true) :
    is_separable φ :=
  ⟨φ, u_free_s_free_separated φ hu hs, int_equiv_refl φ⟩

/-- A syntactically separated formula is separable (trivially). -/
theorem separated_imp_separable (φ : Formula Atom)
    (h : is_syntactically_separated φ = true) :
    is_separable φ :=
  ⟨φ, h, int_equiv_refl φ⟩

/-! ## Case Wrappers -/

/-- Helper: S(a ^ U(A,B), q) is separable when a, q, A, B are U-free and S-free.
    This is Case 1. -/
theorem case1_separable (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (ha' : is_S_free a = true) (hq' : is_S_free q = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce (Formula.and a (.untl A B)) q) := by
  obtain ⟨psi, hequiv, hsep⟩ := elim_case_1 a q A B ha hq hA hB ha' hq' hA' hB'
  exact ⟨psi, hsep, hequiv⟩

/-- Helper: S(a ^ ¬U(A,B), q) is separable. Case 2. -/
theorem case2_separable (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (ha' : is_S_free a = true) (hq' : is_S_free q = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B))) q) := by
  obtain ⟨psi, hequiv, hsep⟩ := elim_case_2 a q A B ha hq hA hB ha' hq' hA' hB'
  exact ⟨psi, hsep, hequiv⟩

/-- Helper: S(a, q ∨ U(A,B)) is separable. Case 3. -/
theorem case3_separable (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (ha' : is_S_free a = true) (hq' : is_S_free q = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce a (Formula.or q (.untl A B))) := by
  obtain ⟨psi, hequiv, hsep⟩ := elim_case_3 a q A B ha hq hA hB ha' hq' hA' hB'
  exact ⟨psi, hsep, hequiv⟩

/-- Helper: S(a, q ∨ ¬U(A,B)) is separable. Case 4. -/
theorem case4_separable (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (ha' : is_S_free a = true) (hq' : is_S_free q = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce a (Formula.or q (Formula.neg (.untl A B)))) := by
  obtain ⟨psi, hequiv, hsep⟩ := elim_case_4 a q A B ha hq hA hB ha' hq' hA' hB'
  exact ⟨psi, hsep, hequiv⟩

/-- Helper: S(a ^ U(A,B), q ∨ U(A,B)) is separable. Case 5. -/
theorem case5_separable (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (ha' : is_S_free a = true) (hq' : is_S_free q = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce (Formula.and a (.untl A B)) (Formula.or q (.untl A B))) :=
  case5_separable_Z a q A B ha hq hA hB ha' hq' hA' hB'

/-- Helper: S(a ^ ¬U(A,B), q ∨ U(A,B)) is separable. Case 6. -/
theorem case6_separable (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (ha' : is_S_free a = true) (hq' : is_S_free q = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B)))
      (Formula.or q (.untl A B))) :=
  case6_separable_Z a q A B ha hq hA hB ha' hq' hA' hB'

/-- Helper: S(a ^ U(A,B), q ∨ ¬U(A,B)) is separable. Case 7. -/
theorem case7_separable (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (ha' : is_S_free a = true) (hq' : is_S_free q = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce (Formula.and a (.untl A B))
      (Formula.or q (Formula.neg (.untl A B)))) :=
  case7_separable_Z a q A B ha hq hA hB ha' hq' hA' hB'

/-- Helper: S(a ^ ¬U(A,B), q ∨ ¬U(A,B)) is separable. Case 8. -/
theorem case8_separable (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (ha' : is_S_free a = true) (hq' : is_S_free q = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B)))
      (Formula.or q (Formula.neg (.untl A B)))) :=
  case8_separable_Z a q A B ha hq hA hB ha' hq' hA' hB'

/-! ## Generalized Case Wrappers (dropping S-free a, q) -/

/-- Case 1 generalized: S(a ^ U(A,B), q) is separable with U-free a, q and S-free A, B. -/
theorem case1_separable_gen (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce (Formula.and a (.untl A B)) q) := by
  obtain ⟨psi, hequiv, hsep⟩ := elim_case_1_gen a q A B ha hq hA hB hA' hB'
  exact ⟨psi, hsep, hequiv⟩

/-- Case 2 generalized: S(a ^ ¬U(A,B), q) is separable. -/
theorem case2_separable_gen (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B))) q) := by
  obtain ⟨psi, hequiv, hsep⟩ := elim_case_2_gen a q A B ha hq hA hB hA' hB'
  exact ⟨psi, hsep, hequiv⟩

/-- Case 3 generalized: S(a, q ∨ U(A,B)) is separable. -/
theorem case3_separable_gen (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce a (Formula.or q (.untl A B))) := by
  obtain ⟨psi, hequiv, hsep⟩ := elim_case_3_gen a q A B ha hq hA hB hA' hB'
  exact ⟨psi, hsep, hequiv⟩

/-- Case 4 generalized: S(a, q ∨ ¬U(A,B)) is separable. -/
theorem case4_separable_gen (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce a (Formula.or q (Formula.neg (.untl A B)))) := by
  obtain ⟨psi, hequiv, hsep⟩ := elim_case_4_gen a q A B ha hq hA hB hA' hB'
  exact ⟨psi, hsep, hequiv⟩

/-- Case 5 generalized: S(a ^ U(A,B), q ∨ U(A,B)) is separable. -/
theorem case5_separable_gen' (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce (Formula.and a (.untl A B)) (Formula.or q (.untl A B))) :=
  case5_separable_Z_gen a q A B ha hq hA hB hA' hB'

/-- Case 6 generalized: S(a ^ ¬U(A,B), q ∨ U(A,B)) is separable. -/
theorem case6_separable_gen' (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B)))
      (Formula.or q (.untl A B))) :=
  case6_separable_Z_gen a q A B ha hq hA hB hA' hB'

/-- Case 7 generalized: S(a ^ U(A,B), q ∨ ¬U(A,B)) is separable. -/
theorem case7_separable_gen' (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce (Formula.and a (.untl A B))
      (Formula.or q (Formula.neg (.untl A B)))) :=
  case7_separable_Z_gen a q A B ha hq hA hB hA' hB'

/-- Case 8 generalized: S(a ^ ¬U(A,B), q ∨ ¬U(A,B)) is separable. -/
theorem case8_separable_gen' (a q A B : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hA : is_U_free A = true) (hB : is_U_free B = true)
    (hA' : is_S_free A = true) (hB' : is_S_free B = true) :
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B)))
      (Formula.or q (Formula.neg (.untl A B)))) :=
  case8_separable_Z_gen a q A B ha hq hA hB hA' hB'

/-- Lemma 10.2.4 generalized (all 8 cases): only requires U-free a, q and S-free A, B. -/
theorem lemma_10_2_4_gen (a q A B : Formula Atom)
    (ha_uf : is_U_free a = true) (hq_uf : is_U_free q = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true) :
    is_separable (.snce (Formula.and a (.untl A B)) q) ∧
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B))) q) ∧
    is_separable (.snce a (Formula.or q (.untl A B))) ∧
    is_separable (.snce a (Formula.or q (Formula.neg (.untl A B)))) ∧
    is_separable (.snce (Formula.and a (.untl A B)) (Formula.or q (.untl A B))) ∧
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B))) (Formula.or q (.untl A B))) ∧
    is_separable (.snce (Formula.and a (.untl A B)) (Formula.or q (Formula.neg (.untl A B)))) ∧
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B))) (Formula.or q (Formula.neg (.untl A B)))) :=
  ⟨case1_separable_gen a q A B ha_uf hq_uf hA_uf hB_uf hA_sf hB_sf,
   case2_separable_gen a q A B ha_uf hq_uf hA_uf hB_uf hA_sf hB_sf,
   case3_separable_gen a q A B ha_uf hq_uf hA_uf hB_uf hA_sf hB_sf,
   case4_separable_gen a q A B ha_uf hq_uf hA_uf hB_uf hA_sf hB_sf,
   case5_separable_gen' a q A B ha_uf hq_uf hA_uf hB_uf hA_sf hB_sf,
   case6_separable_gen' a q A B ha_uf hq_uf hA_uf hB_uf hA_sf hB_sf,
   case7_separable_gen' a q A B ha_uf hq_uf hA_uf hB_uf hA_sf hB_sf,
   case8_separable_gen' a q A B ha_uf hq_uf hA_uf hB_uf hA_sf hB_sf⟩

/-! ## Guard Splitting and Event Decomposition -/

/-- Since-guard splitting by classical LEM on an arbitrary formula:
    S(event, guard) ↔ S(event, (guard ∧ φ) ∨ (guard ∧ ¬φ)). -/
theorem guard_lem_equiv (event guard φ : Formula Atom) :
    int_equiv (.snce event guard)
      (.snce event (Formula.or (Formula.and guard φ) (Formula.and guard (Formula.neg φ)))) := by
  intro M t; constructor
  · rintro ⟨s, hst, he, hg⟩
    refine ⟨s, hst, he, fun r hr1 hr2 => ?_⟩
    have hgr := hg r hr1 hr2
    by_cases hφ : int_truth M r φ
    · exact (int_truth_or M r _ _).mpr (Or.inl ((int_truth_and M r _ _).mpr ⟨hgr, hφ⟩))
    · exact (int_truth_or M r _ _).mpr (Or.inr ((int_truth_and M r _ _).mpr ⟨hgr, hφ⟩))
  · rintro ⟨s, hst, he, hg⟩
    refine ⟨s, hst, he, fun r hr1 hr2 => ?_⟩
    rcases (int_truth_or M r _ _).mp (hg r hr1 hr2) with h | h
    · exact ((int_truth_and M r _ _).mp h).1
    · exact ((int_truth_and M r _ _).mp h).1

/-! ## Main Lemma 10.2.4 Assembly -/

/-- Lemma 10.2.4 (simplified): S(a, q) where a, q are U-free is separable. -/
theorem snce_u_free_separable (a q : Formula Atom)
    (ha_uf : is_U_free a = true) (hq_uf : is_U_free q = true) :
    is_separable (.snce a q) := by
  exact ⟨.snce a q, by simp [is_syntactically_separated, ha_uf, hq_uf], int_equiv_refl _⟩

/-- Lemma 10.2.4 base: S(a, q) with U-free/S-free a, q is separable. -/
theorem lemma_10_2_4_base (a q : Formula Atom)
    (ha_uf : is_U_free a = true) (hq_uf : is_U_free q = true)
    (ha_sf : is_S_free a = true) (hq_sf : is_S_free q = true) :
    is_separable (.snce a q) :=
  ⟨.snce a q, by simp [is_syntactically_separated, ha_uf, hq_uf], int_equiv_refl _⟩

/-- Lemma 10.2.4 (Cases 5-8 combined). -/
theorem lemma_10_2_4_both_cases (a q A B : Formula Atom)
    (ha_uf : is_U_free a = true) (hq_uf : is_U_free q = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (ha_sf : is_S_free a = true) (hq_sf : is_S_free q = true)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true) :
    is_separable (.snce (Formula.and a (.untl A B)) (Formula.or q (.untl A B))) ∧
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B))) (Formula.or q (.untl A B))) ∧
    is_separable (.snce (Formula.and a (.untl A B)) (Formula.or q (Formula.neg (.untl A B)))) ∧
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B))) (Formula.or q (Formula.neg (.untl A B)))) :=
  ⟨case5_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf,
   case6_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf,
   case7_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf,
   case8_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf⟩

/-- Lemma 10.2.4 (Full): All 8 case forms are separable. -/
theorem lemma_10_2_4 (a q A B : Formula Atom)
    (ha_uf : is_U_free a = true) (hq_uf : is_U_free q = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (ha_sf : is_S_free a = true) (hq_sf : is_S_free q = true)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true) :
    is_separable (.snce (Formula.and a (.untl A B)) q) ∧
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B))) q) ∧
    is_separable (.snce a (Formula.or q (.untl A B))) ∧
    is_separable (.snce a (Formula.or q (Formula.neg (.untl A B)))) ∧
    is_separable (.snce (Formula.and a (.untl A B)) (Formula.or q (.untl A B))) ∧
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B))) (Formula.or q (.untl A B))) ∧
    is_separable (.snce (Formula.and a (.untl A B)) (Formula.or q (Formula.neg (.untl A B)))) ∧
    is_separable (.snce (Formula.and a (Formula.neg (.untl A B))) (Formula.or q (Formula.neg (.untl A B)))) :=
  ⟨case1_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf,
   case2_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf,
   case3_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf,
   case4_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf,
   case5_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf,
   case6_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf,
   case7_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf,
   case8_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf⟩

/-! ## Decomposition Theorems -/

/-- Event-split separability: if both U and ¬U branches are separable, the whole is. -/
theorem since_event_split_separable (a A B phi : Formula Atom)
    (h_pos : is_separable (.snce (Formula.and a (.untl A B)) phi))
    (h_neg : is_separable (.snce (Formula.and a (Formula.neg (.untl A B))) phi)) :
    is_separable (.snce a phi) := by
  have hsplit := since_event_split a (.untl A B) phi
  exact is_separable_of_equiv hsplit (or_separable h_pos h_neg)

/-- S(a, q) with U-free a and q, U(A,B) only appears after event-split. -/
theorem snce_single_U_event_only (a q A B : Formula Atom)
    (ha_uf : is_U_free a = true) (hq_uf : is_U_free q = true)
    (_ : is_U_free A = true) (_ : is_U_free B = true)
    (ha_sf : is_S_free a = true) (hq_sf : is_S_free q = true)
    (_ : is_S_free A = true) (_ : is_S_free B = true) :
    is_separable (.snce a q) :=
  lemma_10_2_4_base a q ha_uf hq_uf ha_sf hq_sf

/-- S(a, q ∨ U(A,B)) is separable via Case 3. -/
theorem snce_single_U_guard_pos (a q A B : Formula Atom)
    (ha_uf : is_U_free a = true) (hq_uf : is_U_free q = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (ha_sf : is_S_free a = true) (hq_sf : is_S_free q = true)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true) :
    is_separable (.snce a (Formula.or q (.untl A B))) :=
  case3_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf

/-- S(a, q ∨ ¬U(A,B)) is separable via Case 4. -/
theorem snce_single_U_guard_neg (a q A B : Formula Atom)
    (ha_uf : is_U_free a = true) (hq_uf : is_U_free q = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (ha_sf : is_S_free a = true) (hq_sf : is_S_free q = true)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true) :
    is_separable (.snce a (Formula.or q (Formula.neg (.untl A B)))) :=
  case4_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf

/-- Lemma 10.2.4 (Complete): S(a, q ∨ U(A,B)) via event-split into Cases 5 + 6. -/
theorem lemma_10_2_4_guard_with_U (a q A B : Formula Atom)
    (ha_uf : is_U_free a = true) (hq_uf : is_U_free q = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (ha_sf : is_S_free a = true) (hq_sf : is_S_free q = true)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true) :
    is_separable (.snce a (Formula.or q (.untl A B))) := by
  exact since_event_split_separable a A B (Formula.or q (.untl A B))
    (case5_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf)
    (case6_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf)

/-- Lemma 10.2.4 (Complete): S(a, q ∨ ¬U(A,B)) via event-split into Cases 7 + 8. -/
theorem lemma_10_2_4_guard_with_neg_U (a q A B : Formula Atom)
    (ha_uf : is_U_free a = true) (hq_uf : is_U_free q = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (ha_sf : is_S_free a = true) (hq_sf : is_S_free q = true)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true) :
    is_separable (.snce a (Formula.or q (Formula.neg (.untl A B)))) := by
  exact since_event_split_separable a A B (Formula.or q (Formula.neg (.untl A B)))
    (case7_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf)
    (case8_separable a q A B ha_uf hq_uf hA_uf hB_uf ha_sf hq_sf hA_sf hB_sf)

end Cslib.Logic.Bimodal.Metalogic.Separation
