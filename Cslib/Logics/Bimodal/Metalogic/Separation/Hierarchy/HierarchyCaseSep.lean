/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyDefs

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedDecidableInType false

/-!
# Case-specific is_separable_with_U_type theorems

Extracted from HierarchyCompletion.lean to break a circular dependency
(HierarchyCompletion imports HierarchyInduction, which needs these theorems).

These theorems do NOT depend on HierarchyInduction.
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal

variable {Atom : Type*} [DecidableEq Atom]

/-- has_single_U_type for case1_psi when a, q, A, B are U-free. -/
private theorem case1_psi_has_single_U_type (a q x y : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hx : is_U_free x = true) (hy : is_U_free y = true) :
    has_single_U_type (case1_psi a q x y) x y := by
  simp only [case1_psi, Formula.or, Formula.and, Formula.neg, has_single_U_type]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  all_goals (try exact u_free_has_single_U_type ha)
  all_goals (try exact u_free_has_single_U_type hq)
  all_goals (try exact u_free_has_single_U_type hx)
  all_goals (try exact u_free_has_single_U_type hy)
  all_goals (try trivial)
  all_goals (try exact ⟨rfl, rfl⟩)
  all_goals (try exact ⟨trivial, trivial⟩)
  all_goals simp_all [has_single_U_type, is_U_free,
    u_free_has_single_U_type ha, u_free_has_single_U_type hq,
    u_free_has_single_U_type hx, u_free_has_single_U_type hy]

/-- has_single_U_type for case2_psi when a, q, A, B are U-free. -/
private theorem case2_psi_has_single_U_type (a q x y : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hx : is_U_free x = true) (hy : is_U_free y = true) :
    has_single_U_type (case2_psi a q x y) x y := by
  delta case2_psi
  simp only [Formula.or, Formula.and, Formula.neg, has_single_U_type]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  all_goals (try exact u_free_has_single_U_type ha)
  all_goals (try exact u_free_has_single_U_type hq)
  all_goals (try exact u_free_has_single_U_type hx)
  all_goals (try exact u_free_has_single_U_type hy)
  all_goals (try trivial)
  all_goals (try exact ⟨trivial, trivial⟩)
  all_goals (try exact ⟨⟨trivial, trivial⟩, trivial⟩)
  all_goals (try exact ⟨u_free_has_single_U_type hx, trivial⟩)
  all_goals (try exact ⟨u_free_has_single_U_type hq, trivial⟩)
  all_goals (try exact ⟨u_free_has_single_U_type hy, trivial⟩)
  all_goals simp_all [has_single_U_type, is_U_free,
    u_free_has_single_U_type ha, u_free_has_single_U_type hq,
    u_free_has_single_U_type hx, u_free_has_single_U_type hy]

/-! ### Case-specific is_separable_with_U_type -/

set_option maxHeartbeats 800000 in
/-- Case 1 with U-type preservation: S(a∧U(A,B), q) is separable_with_U_type. -/
theorem case1_sep_with_U_type_gen (a q x y : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hx : is_U_free x = true) (hy : is_U_free y = true)
    (hx' : is_S_free x = true) (hy' : is_S_free y = true) :
    is_separable_with_U_type (.snce (Formula.and a (.untl x y)) q) x y := by
  have ⟨hequiv, hsep⟩ := case1_psi_properties a q x y ha hq hx hy hx' hy'
  exact ⟨case1_psi a q x y, hsep, hequiv,
    case1_psi_has_single_U_type a q x y ha hq hx hy⟩

set_option maxHeartbeats 3200000 in
/-- Case 2 with U-type preservation: S(a∧¬U(A,B), q) is separable_with_U_type. -/
theorem case2_sep_with_U_type_gen (a q x y : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hx : is_U_free x = true) (hy : is_U_free y = true)
    (hx' : is_S_free x = true) (hy' : is_S_free y = true) :
    is_separable_with_U_type (.snce (Formula.and a (Formula.neg (.untl x y))) q) x y := by
  have ⟨hequiv, hsep⟩ := case2_psi_properties a q x y ha hq hx hy hx' hy'
  exact ⟨case2_psi a q x y, hsep, hequiv,
    case2_psi_has_single_U_type a q x y ha hq hx hy⟩

/-! ### Combined Helpers with U-type Preservation -/

set_option maxHeartbeats 800000 in
/-- S(COMBINED ∧ U(A,B), guard) is separable_with_U_type A B when COMBINED
    satisfies untl_under_bool_only and guard is U-free. -/
theorem snce_combined_U_sep_with_U_type
    (combined guard : Formula Atom) (x y : Formula Atom)
    (hx : is_U_free x = true) (hy : is_U_free y = true)
    (hx' : is_S_free x = true) (hy' : is_S_free y = true)
    (hg_uf : is_U_free guard = true)
    (h_bool : untl_under_bool_only combined x y) :
    is_separable_with_U_type (.snce (Formula.and combined (.untl x y)) guard) x y := by
  let combined' := replace_untl_with_top combined x y
  have h_uf : is_U_free combined' = true := replace_U_free_of_bool combined x y h_bool
  have h_congr := snce_event_congr_with_U combined combined' guard x y
    (fun m t hU => replace_correct_bool combined x y m t h_bool hU)
  apply is_separable_with_U_type_of_equiv h_congr
  have ⟨hequiv, hsep⟩ := case1_psi_properties combined' guard x y h_uf hg_uf hx hy hx' hy'
  exact ⟨case1_psi combined' guard x y, hsep, hequiv,
    case1_psi_has_single_U_type combined' guard x y h_uf hg_uf hx hy⟩

set_option maxHeartbeats 3200000 in
/-- S(COMBINED ∧ ¬U(A,B), guard) is separable_with_U_type A B when COMBINED
    satisfies untl_under_bool_only and guard is U-free. -/
theorem snce_combined_notU_sep_with_U_type
    (combined guard : Formula Atom) (x y : Formula Atom)
    (hx : is_U_free x = true) (hy : is_U_free y = true)
    (hx' : is_S_free x = true) (hy' : is_S_free y = true)
    (hg_uf : is_U_free guard = true)
    (h_bool : untl_under_bool_only combined x y) :
    is_separable_with_U_type (.snce (Formula.and combined (Formula.neg (.untl x y))) guard) x y := by
  let combined' := replace_untl_with_bot combined x y
  have h_uf : is_U_free combined' = true := replace_bot_U_free_of_bool combined x y h_bool
  have h_congr := snce_event_congr_with_notU combined combined' guard x y
    (fun m t hnotU => replace_correct_bot combined x y m t h_bool hnotU)
  apply is_separable_with_U_type_of_equiv h_congr
  have ⟨hequiv, hsep⟩ := case2_psi_properties combined' guard x y h_uf hg_uf hx hy hx' hy'
  exact ⟨case2_psi combined' guard x y, hsep, hequiv,
    case2_psi_has_single_U_type combined' guard x y h_uf hg_uf hx hy⟩

/-! ### Private helpers for Cases 5-8 -/

/-- Helper: and_left_congr for int_equiv. -/
private theorem and_left_congr_hier {φ₁ φ₂ ψ : Formula Atom} (h : int_equiv φ₁ φ₂) :
    int_equiv (Formula.and φ₁ ψ) (Formula.and φ₂ ψ) := by
  intro m t; constructor
  · intro h'; have ⟨hφ, hψ⟩ := int_truth_and_iff.mp h'
    exact int_truth_and_iff.mpr ⟨(h m t).mp hφ, hψ⟩
  · intro h'; have ⟨hφ, hψ⟩ := int_truth_and_iff.mp h'
    exact int_truth_and_iff.mpr ⟨(h m t).mpr hφ, hψ⟩

/-- snce preserves int_equiv (local copy). -/
private theorem snce_congr_local {φ₁ ψ₁ φ₂ ψ₂ : Formula Atom}
    (h1 : int_equiv φ₁ φ₂) (h2 : int_equiv ψ₁ ψ₂) :
    int_equiv (.snce φ₁ ψ₁) (.snce φ₂ ψ₂) := by
  intro m t; constructor
  · rintro ⟨s, hst, hφ, hψ⟩
    exact ⟨s, hst, (h1 m s).mp hφ, fun r hr1 hr2 => (h2 m r).mp (hψ r hr1 hr2)⟩
  · rintro ⟨s, hst, hφ, hψ⟩
    exact ⟨s, hst, (h1 m s).mpr hφ, fun r hr1 hr2 => (h2 m r).mpr (hψ r hr1 hr2)⟩

/-- Helper: snce_event_congr for int_equiv (event only). -/
private theorem snce_event_congr_hier {φ₁ φ₂ ψ : Formula Atom} (h : int_equiv φ₁ φ₂) :
    int_equiv (.snce φ₁ ψ) (.snce φ₂ ψ) :=
  snce_congr_local h (int_equiv_refl ψ)

/-! ### Cases 5-8 with U-type Preservation -/

set_option maxHeartbeats 1600000 in
/-- Case 5 with U-type: S(a∧U(A,B), q∨U(A,B)) is separable_with_U_type A B. -/
theorem case5_sep_with_U_type_Z_gen (a q x y : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hx : is_U_free x = true) (hy : is_U_free y = true)
    (hx' : is_S_free x = true) (hy' : is_S_free y = true) :
    is_separable_with_U_type (.snce (Formula.and a (.untl x y)) (Formula.or q (.untl x y))) x y := by
  apply is_separable_with_U_type_of_equiv (case3_equiv_Z_general (Formula.and a (.untl x y)) q x y)
  simp only [case3_rhs]
  apply or_separable_with_U_type
  · apply or_separable_with_U_type
    · exact case1_sep_with_U_type_gen a q x y ha hq hx hy hx' hy'
    · apply and_separable_with_U_type
      · apply is_separable_with_U_type_of_equiv
          (snce_event_congr_hier (case3_alpha_aU_factor a q x y))
        apply is_separable_with_U_type_of_equiv (int_equiv_trans
          (snce_event_congr_hier (and_or_distrib a
            (Formula.and (Formula.neg q) (.snce (Formula.and a (.untl x y)) q))
            (.untl x y)))
          (since_distrib_or_left _ _ (Q_Z x y (Formula.neg q))))
        apply or_separable_with_U_type
        · exact snce_combined_U_sep_with_U_type a (Q_Z x y (Formula.neg q)) x y
            hx hy hx' hy' (Q_Z_neg_q_U_free x y q hx hy hq)
            (u_free_untl_under_bool a x y ha)
        · let σ := case1_psi a q x y
          have hσ_equiv : int_equiv (.snce (Formula.and a (.untl x y)) q) σ :=
            (case1_psi_properties a q x y ha hq hx hy hx' hy').1
          have hY_congr : int_equiv
            (Formula.and (Formula.neg q) (.snce (Formula.and a (.untl x y)) q))
            (Formula.and (Formula.neg q) σ) := by
            intro m t; constructor
            · intro h; have ⟨hnq, hS⟩ := int_truth_and_iff.mp h
              exact int_truth_and_iff.mpr ⟨hnq, (hσ_equiv m t).mp hS⟩
            · intro h; have ⟨hnq, hσ'⟩ := int_truth_and_iff.mp h
              exact int_truth_and_iff.mpr ⟨hnq, (hσ_equiv m t).mpr hσ'⟩
          apply is_separable_with_U_type_of_equiv (snce_event_congr_hier (and_left_congr_hier hY_congr))
          have h_nqσ_bool : untl_under_bool_only (Formula.and (Formula.neg q) σ) x y := by
            show untl_under_bool_only (.imp (.imp (Formula.neg q) (.imp σ .bot)) .bot) x y
            refine ⟨⟨?_, case1_psi_bool_only a q x y ha hq hx hy, trivial⟩, trivial⟩
            exact ⟨u_free_untl_under_bool q x y hq, trivial⟩
          exact snce_combined_U_sep_with_U_type (Formula.and (Formula.neg q) σ)
            (Q_Z x y (Formula.neg q)) x y hx hy hx' hy'
            (Q_Z_neg_q_U_free x y q hx hy hq) h_nqσ_bool
      · apply or_separable_with_U_type
        · exact u_free_separable_with_type hx
        · exact and_separable_with_U_type
            (u_free_separable_with_type hy)
            (untl_s_free_separable_with_type hx' hy')
  · have h_d21 := d21_sep_equiv a q x y ha hq hx hy hx' hy'
    have h_event_congr : int_equiv
      (Formula.and (Formula.and x (Formula.or q (.untl x y)))
        (.snce (case3_alpha (Formula.and a (.untl x y)) q x y) (Q_Z x y (Formula.neg q))))
      (Formula.and (Formula.and x (Formula.or q (.untl x y))) (d21_sep a q x y)) := by
      intro m t; constructor
      · intro h; have ⟨hAqU, hS⟩ := int_truth_and_iff.mp h
        exact int_truth_and_iff.mpr ⟨hAqU, (h_d21 m t).mp hS⟩
      · intro h; have ⟨hAqU, hd⟩ := int_truth_and_iff.mp h
        exact int_truth_and_iff.mpr ⟨hAqU, (h_d21 m t).mpr hd⟩
    apply is_separable_with_U_type_of_equiv (snce_event_congr_hier h_event_congr)
    apply is_separable_with_U_type_of_equiv (since_event_split _ (.untl x y) q)
    apply or_separable_with_U_type
    · have h_event_bool : untl_under_bool_only
          (Formula.and (Formula.and x (Formula.or q (.untl x y))) (d21_sep a q x y)) x y := by
        show untl_under_bool_only (.imp (.imp (Formula.and x (Formula.or q (.untl x y)))
          (.imp (d21_sep a q x y) .bot)) .bot) x y
        refine ⟨⟨?_, d21_sep_bool_only a q x y ha hq hx hy, trivial⟩, trivial⟩
        show untl_under_bool_only (.imp (.imp x (.imp (Formula.or q (.untl x y)) .bot)) .bot) x y
        refine ⟨⟨u_free_untl_under_bool x x y hx, ?_, trivial⟩, trivial⟩
        show untl_under_bool_only (.imp (.imp q .bot) (.untl x y)) x y
        exact ⟨⟨u_free_untl_under_bool q x y hq, trivial⟩, Or.inl ⟨rfl, rfl⟩⟩
      exact snce_combined_U_sep_with_U_type
        (Formula.and (Formula.and x (Formula.or q (.untl x y))) (d21_sep a q x y))
        q x y hx hy hx' hy' hq h_event_bool
    · have h_event_bool : untl_under_bool_only
          (Formula.and (Formula.and x (Formula.or q (.untl x y))) (d21_sep a q x y)) x y := by
        show untl_under_bool_only (.imp (.imp (Formula.and x (Formula.or q (.untl x y)))
          (.imp (d21_sep a q x y) .bot)) .bot) x y
        refine ⟨⟨?_, d21_sep_bool_only a q x y ha hq hx hy, trivial⟩, trivial⟩
        show untl_under_bool_only (.imp (.imp x (.imp (Formula.or q (.untl x y)) .bot)) .bot) x y
        refine ⟨⟨u_free_untl_under_bool x x y hx, ?_, trivial⟩, trivial⟩
        show untl_under_bool_only (.imp (.imp q .bot) (.untl x y)) x y
        exact ⟨⟨u_free_untl_under_bool q x y hq, trivial⟩, Or.inl ⟨rfl, rfl⟩⟩
      exact snce_combined_notU_sep_with_U_type
        (Formula.and (Formula.and x (Formula.or q (.untl x y))) (d21_sep a q x y))
        q x y hx hy hx' hy' hq h_event_bool

/-- Case 8 with U-type: S(a∧¬U, q∨¬U) is separable_with_U_type A B. -/
theorem case8_sep_with_U_type_Z_gen (a q x y : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hx : is_U_free x = true) (hy : is_U_free y = true)
    (hx' : is_S_free x = true) (hy' : is_S_free y = true) :
    is_separable_with_U_type (.snce (Formula.and a (Formula.neg (.untl x y)))
      (Formula.or q (Formula.neg (.untl x y)))) x y := by
  apply is_separable_with_U_type_of_equiv (case8_equiv_Z a q x y)
  apply and_separable_with_U_type
  · have hg : is_U_free (Formula.neg (.bot : Formula Atom)) = true := by simp [Formula.neg, is_U_free]
    exact case2_sep_with_U_type_gen a (Formula.neg .bot) x y ha hg hx hy hx' hy'
  · apply neg_separable_with_U_type
    have hnq_uf : is_U_free (Formula.neg q) = true := by simp [Formula.neg, is_U_free, hq]
    have hna_uf : is_U_free (Formula.neg a) = true := by simp [Formula.neg, is_U_free, ha]
    exact case5_sep_with_U_type_Z_gen (Formula.neg q) (Formula.neg a) x y hnq_uf hna_uf hx hy hx' hy'

set_option maxHeartbeats 3200000 in
/-- S(ev, q∨U(A,B)) is separable_with_U_type A B when ev is U-free. -/
private theorem snce_Ufree_event_qU_guard_sep_with_U_type (ev q x y : Formula Atom)
    (hev_uf : is_U_free ev = true) (hq : is_U_free q = true)
    (hx : is_U_free x = true) (hy : is_U_free y = true)
    (hx' : is_S_free x = true) (hy' : is_S_free y = true) :
    is_separable_with_U_type (.snce ev (Formula.or q (.untl x y))) x y := by
  apply is_separable_with_U_type_of_equiv (case3_equiv_Z_general ev q x y)
  simp only [case3_rhs]
  apply or_separable_with_U_type
  · apply or_separable_with_U_type
    · have hev_snce_sep : is_syntactically_separated (.snce ev q) = true := by
        simp [is_syntactically_separated, hev_uf, hq]
      exact ⟨.snce ev q, hev_snce_sep, int_equiv_refl _,
        ⟨u_free_has_single_U_type hev_uf, u_free_has_single_U_type hq⟩⟩
    · apply and_separable_with_U_type
      · have h_nqSev_uf : is_U_free (Formula.and (Formula.neg q) (.snce ev q)) = true := by
          simp [Formula.and, Formula.neg, is_U_free, hq, hev_uf]
        apply is_separable_with_U_type_of_equiv (since_distrib_or_left _ _ (Q_Z x y (Formula.neg q)))
        apply or_separable_with_U_type
        · have hQ_uf : is_U_free (Q_Z x y (Formula.neg q)) = true :=
            Q_Z_neg_q_U_free x y q hx hy hq
          exact ⟨.snce ev (Q_Z x y (Formula.neg q)),
            by simp [is_syntactically_separated, hev_uf, hQ_uf], int_equiv_refl _,
            ⟨u_free_has_single_U_type hev_uf, u_free_has_single_U_type hQ_uf⟩⟩
        · apply is_separable_with_U_type_of_equiv
            (since_event_split _ (.untl x y) (Q_Z x y (Formula.neg q)))
          apply or_separable_with_U_type
          · apply is_separable_with_U_type_of_equiv (snce_event_congr_with_U _ _ _ x y
              (fun m t hU => ⟨fun h => (int_truth_and_iff.mp h).1,
                fun h => int_truth_and_iff.mpr ⟨h, int_truth_or_iff.mpr (Or.inr hU)⟩⟩))
            exact snce_combined_U_sep_with_U_type (Formula.and (Formula.neg q) (.snce ev q))
              (Q_Z x y (Formula.neg q)) x y hx hy hx' hy' (Q_Z_neg_q_U_free x y q hx hy hq)
              (u_free_untl_under_bool _ x y h_nqSev_uf)
          · apply is_separable_with_U_type_of_equiv (by
              intro m t; constructor
              · rintro ⟨s, _, h_event, _⟩
                have ⟨h_left, h_notU⟩ := int_truth_and_iff.mp h_event
                have ⟨h_nqS, h_qU⟩ := int_truth_and_iff.mp h_left
                have h_nq := (int_truth_and_iff.mp h_nqS).1
                rcases int_truth_or_iff.mp h_qU with hq' | hU
                · exact h_nq hq'
                · exact h_notU hU
              · intro h; exact h.elim : int_equiv _ .bot)
            exact ⟨.bot, by simp [is_syntactically_separated], int_equiv_refl _, trivial⟩
      · apply or_separable_with_U_type
        · exact u_free_separable_with_type hx
        · exact and_separable_with_U_type
            (u_free_separable_with_type hy)
            (untl_s_free_separable_with_type hx' hy')
  · have h_nqSev_uf_D3 : is_U_free (Formula.and (Formula.neg q) (.snce ev q)) = true := by
      simp [Formula.and, Formula.neg, is_U_free, hq, hev_uf]
    have hQ_uf_D3 : is_U_free (Q_Z x y (Formula.neg q)) = true :=
      Q_Z_neg_q_U_free x y q hx hy hq
    let d21_local := Formula.or (.snce ev (Q_Z x y (Formula.neg q)))
      (case1_psi (Formula.and (Formula.neg q) (.snce ev q)) (Q_Z x y (Formula.neg q)) x y)
    have h_d21_bool : untl_under_bool_only d21_local x y := by
      have h_or_bool : ∀ p q, untl_under_bool_only p x y → untl_under_bool_only q x y →
          untl_under_bool_only (Formula.or p q) x y := by
        intro p q hp hq; exact ⟨⟨hp, trivial⟩, hq⟩
      apply h_or_bool
      · exact ⟨hev_uf, hQ_uf_D3⟩
      · exact case1_psi_bool_only _ _ x y h_nqSev_uf_D3 hQ_uf_D3 hx hy
    have h_d21_equiv : int_equiv (.snce (case3_alpha ev q x y) (Q_Z x y (Formula.neg q))) d21_local := by
      have h_step1 := since_distrib_or_left ev
        (Formula.and (Formula.and (Formula.neg q) (.snce ev q)) (Formula.or q (.untl x y)))
        (Q_Z x y (Formula.neg q))
      have h_step2 := since_event_split
        (Formula.and (Formula.and (Formula.neg q) (.snce ev q)) (Formula.or q (.untl x y)))
        (.untl x y) (Q_Z x y (Formula.neg q))
      have h_congr_U := snce_event_congr_with_U
        (Formula.and (Formula.and (Formula.neg q) (.snce ev q)) (Formula.or q (.untl x y)))
        (Formula.and (Formula.neg q) (.snce ev q))
        (Q_Z x y (Formula.neg q)) x y
        (fun m t hU => ⟨fun h => (int_truth_and_iff.mp h).1,
          fun h => int_truth_and_iff.mpr ⟨h, int_truth_or_iff.mpr (Or.inr hU)⟩⟩)
      have h_psi := (case1_psi_properties (Formula.and (Formula.neg q) (.snce ev q))
        (Q_Z x y (Formula.neg q)) x y h_nqSev_uf_D3 hQ_uf_D3 hx hy hx' hy').1
      intro m t; constructor
      · intro h
        have h12 := (h_step1 m t).mp h
        rcases int_truth_or_iff.mp h12 with h1 | h2
        · exact int_truth_or_iff.mpr (Or.inl h1)
        · have h_split := (h_step2 m t).mp h2
          rcases int_truth_or_iff.mp h_split with hU_br | hnotU_br
          · exact int_truth_or_iff.mpr (Or.inr ((h_psi m t).mp ((h_congr_U m t).mp hU_br)))
          · exfalso
            obtain ⟨s, _, h_event, _⟩ := hnotU_br
            have ⟨h_left, h_notU⟩ := int_truth_and_iff.mp h_event
            have ⟨h_nqS, h_qU⟩ := int_truth_and_iff.mp h_left
            rcases int_truth_or_iff.mp h_qU with hq' | hU
            · exact (int_truth_and_iff.mp h_nqS).1 hq'
            · exact h_notU hU
      · intro h
        rcases int_truth_or_iff.mp h with h1 | h2
        · exact (h_step1 m t).mpr (int_truth_or_iff.mpr (Or.inl h1))
        · have h_combined := (h_congr_U m t).mpr ((h_psi m t).mpr h2)
          have h_unsplit := (h_step2 m t).mpr (int_truth_or_iff.mpr (Or.inl h_combined))
          exact (h_step1 m t).mpr (int_truth_or_iff.mpr (Or.inr h_unsplit))
    have h_event_congr : int_equiv
      (Formula.and (Formula.and x (Formula.or q (.untl x y)))
        (.snce (case3_alpha ev q x y) (Q_Z x y (Formula.neg q))))
      (Formula.and (Formula.and x (Formula.or q (.untl x y))) d21_local) := by
      intro m t; constructor
      · intro h; have ⟨hAqU, hS⟩ := int_truth_and_iff.mp h
        exact int_truth_and_iff.mpr ⟨hAqU, (h_d21_equiv m t).mp hS⟩
      · intro h; have ⟨hAqU, hd⟩ := int_truth_and_iff.mp h
        exact int_truth_and_iff.mpr ⟨hAqU, (h_d21_equiv m t).mpr hd⟩
    apply is_separable_with_U_type_of_equiv (snce_event_congr_hier h_event_congr)
    apply is_separable_with_U_type_of_equiv (since_event_split _ (.untl x y) q)
    apply or_separable_with_U_type
    · have h_event_bool : untl_under_bool_only
          (Formula.and (Formula.and x (Formula.or q (.untl x y))) d21_local) x y := by
        show untl_under_bool_only (.imp (.imp (Formula.and x (Formula.or q (.untl x y)))
          (.imp d21_local .bot)) .bot) x y
        refine ⟨⟨?_, h_d21_bool, trivial⟩, trivial⟩
        show untl_under_bool_only (.imp (.imp x (.imp (Formula.or q (.untl x y)) .bot)) .bot) x y
        refine ⟨⟨u_free_untl_under_bool x x y hx, ?_, trivial⟩, trivial⟩
        show untl_under_bool_only (.imp (.imp q .bot) (.untl x y)) x y
        exact ⟨⟨u_free_untl_under_bool q x y hq, trivial⟩, Or.inl ⟨rfl, rfl⟩⟩
      exact snce_combined_U_sep_with_U_type
        (Formula.and (Formula.and x (Formula.or q (.untl x y))) d21_local)
        q x y hx hy hx' hy' hq h_event_bool
    · have h_event_bool : untl_under_bool_only
          (Formula.and (Formula.and x (Formula.or q (.untl x y))) d21_local) x y := by
        show untl_under_bool_only (.imp (.imp (Formula.and x (Formula.or q (.untl x y)))
          (.imp d21_local .bot)) .bot) x y
        refine ⟨⟨?_, h_d21_bool, trivial⟩, trivial⟩
        show untl_under_bool_only (.imp (.imp x (.imp (Formula.or q (.untl x y)) .bot)) .bot) x y
        refine ⟨⟨u_free_untl_under_bool x x y hx, ?_, trivial⟩, trivial⟩
        show untl_under_bool_only (.imp (.imp q .bot) (.untl x y)) x y
        exact ⟨⟨u_free_untl_under_bool q x y hq, trivial⟩, Or.inl ⟨rfl, rfl⟩⟩
      exact snce_combined_notU_sep_with_U_type
        (Formula.and (Formula.and x (Formula.or q (.untl x y))) d21_local)
        q x y hx hy hx' hy' hq h_event_bool

/-- Case 6 with U-type: S(a∧¬U, q∨U) is separable_with_U_type A B. -/
theorem case6_sep_with_U_type_Z_gen (a q x y : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hx : is_U_free x = true) (hy : is_U_free y = true)
    (hx' : is_S_free x = true) (hy' : is_S_free y = true) :
    is_separable_with_U_type (.snce (Formula.and a (Formula.neg (.untl x y)))
      (Formula.or q (.untl x y))) x y := by
  apply is_separable_with_U_type_of_equiv (case6_equiv_Z a q x y)
  apply or_separable_with_U_type
  · apply and_separable_with_U_type
    · apply and_separable_with_U_type
      · have hg_uf : is_U_free (Formula.and q (Formula.neg x)) = true := by
          simp [Formula.and, Formula.neg, is_U_free, hq, hx]
        exact ⟨.snce a (Formula.and q (Formula.neg x)),
          by simp [is_syntactically_separated, ha, hg_uf], int_equiv_refl _,
          ⟨u_free_has_single_U_type ha, u_free_has_single_U_type hg_uf⟩⟩
      · exact u_free_separable_with_type (by simp [Formula.neg, is_U_free, hx])
    · apply neg_separable_with_U_type
      exact and_separable_with_U_type
        (u_free_separable_with_type hy)
        (untl_s_free_separable_with_type hx' hy')
  · have h_rearrange : int_equiv
      (Formula.and (Formula.and (Formula.and (Formula.neg y) (Formula.neg x))
        (Formula.or q (.untl x y)))
        (.snce a (Formula.and q (Formula.neg x))))
      (Formula.and (Formula.and (Formula.and (Formula.neg y) (Formula.neg x))
        (.snce a (Formula.and q (Formula.neg x))))
        (Formula.or q (.untl x y))) := by
      intro m t; constructor
      · intro h
        have ⟨h1, h2⟩ := int_truth_and_iff.mp h
        have ⟨h3, h4⟩ := int_truth_and_iff.mp h1
        exact int_truth_and_iff.mpr ⟨int_truth_and_iff.mpr ⟨h3, h2⟩, h4⟩
      · intro h
        have ⟨h1, h2⟩ := int_truth_and_iff.mp h
        have ⟨h3, h4⟩ := int_truth_and_iff.mp h1
        exact int_truth_and_iff.mpr ⟨int_truth_and_iff.mpr ⟨h3, h2⟩, h4⟩
    apply is_separable_with_U_type_of_equiv (snce_event_congr_hier h_rearrange)
    have h_distrib : int_equiv
      (Formula.and (Formula.and (Formula.and (Formula.neg y) (Formula.neg x))
        (.snce a (Formula.and q (Formula.neg x))))
        (Formula.or q (.untl x y)))
      (Formula.or
        (Formula.and (Formula.and (Formula.and (Formula.neg y) (Formula.neg x))
          (.snce a (Formula.and q (Formula.neg x)))) q)
        (Formula.and (Formula.and (Formula.and (Formula.neg y) (Formula.neg x))
          (.snce a (Formula.and q (Formula.neg x)))) (.untl x y))) := by
      intro m t; constructor
      · intro h
        have ⟨hc, hab⟩ := int_truth_and_iff.mp h
        rcases int_truth_or_iff.mp hab with ha' | hb'
        · exact int_truth_or_iff.mpr (Or.inl (int_truth_and_iff.mpr ⟨hc, ha'⟩))
        · exact int_truth_or_iff.mpr (Or.inr (int_truth_and_iff.mpr ⟨hc, hb'⟩))
      · intro h
        rcases int_truth_or_iff.mp h with h1 | h2
        · have ⟨hc, ha'⟩ := int_truth_and_iff.mp h1
          exact int_truth_and_iff.mpr ⟨hc, int_truth_or_iff.mpr (Or.inl ha')⟩
        · have ⟨hc, hb'⟩ := int_truth_and_iff.mp h2
          exact int_truth_and_iff.mpr ⟨hc, int_truth_or_iff.mpr (Or.inr hb')⟩
    apply is_separable_with_U_type_of_equiv (snce_event_congr_hier h_distrib)
    apply is_separable_with_U_type_of_equiv (since_distrib_or_left _ _ (Formula.or q (.untl x y)))
    have hSTUFF_uf : is_U_free (Formula.and (Formula.and (Formula.neg y) (Formula.neg x))
        (.snce a (Formula.and q (Formula.neg x)))) = true := by
      simp [Formula.and, Formula.neg, is_U_free, ha, hq, hx, hy]
    apply or_separable_with_U_type
    · have hev_uf : is_U_free (((y.neg.and x.neg).and (a.snce (q.and x.neg))).and q) = true := by
        simp [Formula.and, Formula.neg, is_U_free, ha, hq, hx, hy]
      exact snce_Ufree_event_qU_guard_sep_with_U_type _ q x y hev_uf hq hx hy hx' hy'
    · exact case5_sep_with_U_type_Z_gen _ q x y hSTUFF_uf hq hx hy hx' hy'

/-- S(ev, q∨¬U) is separable_with_U_type when ev is U-free. -/
private theorem snce_Ufree_event_qNotU_guard_sep_with_U_type (ev q x y : Formula Atom)
    (hev_uf : is_U_free ev = true) (hq : is_U_free q = true)
    (hx : is_U_free x = true) (hy : is_U_free y = true)
    (hx' : is_S_free x = true) (hy' : is_S_free y = true) :
    is_separable_with_U_type (.snce ev (Formula.or q (Formula.neg (.untl x y)))) x y := by
  have hna_uf : is_U_free (Formula.neg ev) = true := by simp [Formula.neg, is_U_free, hev_uf]
  have hnq_uf : is_U_free (Formula.neg q) = true := by simp [Formula.neg, is_U_free, hq]
  have hanq_uf : is_U_free (Formula.and (Formula.neg ev) (Formula.neg q)) = true := by
    simp [Formula.and, Formula.neg, is_U_free, hev_uf, hq]
  have ⟨hequiv1, hsep1⟩ := case1_psi_properties
    (Formula.and (Formula.neg ev) (Formula.neg q)) (Formula.neg ev) x y
    hanq_uf hna_uf hx hy hx' hy'
  have hsingle1 := case1_psi_has_single_U_type
    (Formula.and (Formula.neg ev) (Formula.neg q)) (Formula.neg ev) x y
    hanq_uf hna_uf hx hy
  let psi1 := case1_psi (Formula.and (Formula.neg ev) (Formula.neg q)) (Formula.neg ev) x y
  have hsep_H : is_syntactically_separated (.allPast (Formula.neg ev)) = true := by
    simp [is_syntactically_separated, Formula.neg, is_U_free, hev_uf]
  have h_allpast_uf : is_U_free (.allPast (Formula.neg ev)) = true := by
    simp only [Formula.allPast, Formula.somePast]
    simp only [Formula.neg, is_U_free]
    simp only [hev_uf]
    decide
  refine is_separable_with_U_type_of_equiv ?equiv_
    (and_separable_with_U_type
      (neg_separable_with_U_type ⟨.allPast (Formula.neg ev), hsep_H, int_equiv_refl _,
        u_free_has_single_U_type h_allpast_uf⟩)
      (neg_separable_with_U_type ⟨psi1, hsep1, hequiv1, hsingle1⟩))
  intro m t; constructor
  · intro hS
    apply int_truth_and_iff.mpr; constructor
    · rw [int_truth_neg_iff]; intro hall
      rw [int_truth_allPast] at hall
      obtain ⟨s, hst, hev_s, _⟩ := hS; exact hall s hst hev_s
    · intro hpsi1
      obtain ⟨s1, hs1t, hevent1, hguard1⟩ := hpsi1
      have ⟨hanq1, hU1⟩ := int_truth_and_iff.mp hevent1
      have hna1 := (int_truth_and_iff.mp hanq1).1
      have hnq1 := (int_truth_and_iff.mp hanq1).2
      obtain ⟨s, hst, hev_s, hguard_S⟩ := hS
      rcases lt_trichotomy s s1 with hss1 | hss1 | hss1
      · rcases int_truth_or_iff.mp (hguard_S s1 hss1 hs1t) with hq1 | hnotU1
        · exact hnq1 hq1
        · exact hnotU1 hU1
      · exact hna1 (hss1 ▸ hev_s)
      · exact (hguard1 s hss1 hst) hev_s
  · intro hand
    have ⟨hnotH, hnotPsi1⟩ := int_truth_and_iff.mp hand
    have hnotS1 : ¬ int_truth m t (.snce (Formula.and (Formula.and (Formula.neg ev) (Formula.neg q))
        (.untl x y)) (Formula.neg ev)) :=
      fun hS1 => hnotPsi1 hS1
    by_contra hnotS
    rcases int_truth_or_iff.mp ((neg_since_equiv ev (Formula.or q (Formula.neg (.untl x y))) m t).mp hnotS) with hH | hS_neg
    · exact hnotH hH
    · obtain ⟨s, hst, hevent, hguard⟩ := hS_neg
      have ⟨hna_s, hnotQnU_s⟩ := int_truth_and_iff.mp hevent
      have hnotQ_s : ¬ int_truth m s q :=
        fun h => (int_truth_neg_iff.mp hnotQnU_s) (int_truth_or_iff.mpr (Or.inl h))
      have hnotNotU_s : ¬ (¬ int_truth m s (.untl x y)) :=
        fun h => (int_truth_neg_iff.mp hnotQnU_s) (int_truth_or_iff.mpr (Or.inr h))
      push_neg at hnotNotU_s
      exact hnotS1 ⟨s, hst, int_truth_and_iff.mpr
        ⟨int_truth_and_iff.mpr ⟨hna_s, hnotQ_s⟩, hnotNotU_s⟩, hguard⟩

set_option maxHeartbeats 1600000 in
/-- Case 7 with U-type: S(a∧U, q∨¬U) is separable_with_U_type A B. -/
theorem case7_sep_with_U_type_Z_gen (a q x y : Formula Atom)
    (ha : is_U_free a = true) (hq : is_U_free q = true)
    (hx : is_U_free x = true) (hy : is_U_free y = true)
    (hx' : is_S_free x = true) (hy' : is_S_free y = true) :
    is_separable_with_U_type (.snce (Formula.and a (.untl x y))
      (Formula.or q (Formula.neg (.untl x y)))) x y := by
  apply is_separable_with_U_type_of_equiv (case7_equiv_Z a q x y)
  have hBq_uf : is_U_free (Formula.and y q) = true := by
    simp only [Formula.and, Formula.neg, is_U_free, hy, hq, Bool.true_and, Bool.and_self]
  apply or_separable_with_U_type
  · apply or_separable_with_U_type
    · have h_rearrange : int_equiv
        (Formula.and (Formula.and x (Formula.or q (Formula.neg (.untl x y))))
          (.snce a (Formula.and y q)))
        (Formula.and (Formula.and x (.snce a (Formula.and y q)))
          (Formula.or q (Formula.neg (.untl x y)))) := by
        intro m t; constructor
        · intro h
          have ⟨h1, h2⟩ := int_truth_and_iff.mp h
          have ⟨h3, h4⟩ := int_truth_and_iff.mp h1
          exact int_truth_and_iff.mpr ⟨int_truth_and_iff.mpr ⟨h3, h2⟩, h4⟩
        · intro h
          have ⟨h1, h2⟩ := int_truth_and_iff.mp h
          have ⟨h3, h4⟩ := int_truth_and_iff.mp h1
          exact int_truth_and_iff.mpr ⟨int_truth_and_iff.mpr ⟨h3, h2⟩, h4⟩
      apply is_separable_with_U_type_of_equiv (snce_event_congr_hier h_rearrange)
      have h_distrib : int_equiv
        (Formula.and (Formula.and x (.snce a (Formula.and y q)))
          (Formula.or q (Formula.neg (.untl x y))))
        (Formula.or
          (Formula.and (Formula.and x (.snce a (Formula.and y q))) q)
          (Formula.and (Formula.and x (.snce a (Formula.and y q)))
            (Formula.neg (.untl x y)))) := by
        intro m t; constructor
        · intro h
          have ⟨hc, hab⟩ := int_truth_and_iff.mp h
          rcases int_truth_or_iff.mp hab with ha' | hb'
          · exact int_truth_or_iff.mpr (Or.inl (int_truth_and_iff.mpr ⟨hc, ha'⟩))
          · exact int_truth_or_iff.mpr (Or.inr (int_truth_and_iff.mpr ⟨hc, hb'⟩))
        · intro h
          rcases int_truth_or_iff.mp h with h1 | h2
          · have ⟨hc, ha'⟩ := int_truth_and_iff.mp h1
            exact int_truth_and_iff.mpr ⟨hc, int_truth_or_iff.mpr (Or.inl ha')⟩
          · have ⟨hc, hb'⟩ := int_truth_and_iff.mp h2
            exact int_truth_and_iff.mpr ⟨hc, int_truth_or_iff.mpr (Or.inr hb')⟩
      apply is_separable_with_U_type_of_equiv (snce_event_congr_hier h_distrib)
      apply is_separable_with_U_type_of_equiv (since_distrib_or_left _ _
        (Formula.or q (Formula.neg (.untl x y))))
      have hSTUFF_uf : is_U_free (Formula.and x (.snce a (Formula.and y q))) = true := by
        simp only [Formula.and, Formula.neg, is_U_free, hx, ha, hy, hq, Bool.and_self]
      apply or_separable_with_U_type
      · have hev_uf : is_U_free (Formula.and (Formula.and x
            (.snce a (Formula.and y q))) q) = true := by
          simp only [Formula.and, Formula.neg, is_U_free, hx, ha, hy, hq, Bool.and_self]
        exact snce_Ufree_event_qNotU_guard_sep_with_U_type _ q x y hev_uf hq hx hy hx' hy'
      · exact case8_sep_with_U_type_Z_gen
          (Formula.and x (.snce a (Formula.and y q)))
          q x y hSTUFF_uf hq hx hy hx' hy'
    · apply and_separable_with_U_type
      · have hg_uf : is_U_free (Formula.and y q) = true := hBq_uf
        exact ⟨.snce a (Formula.and y q),
          by simp [is_syntactically_separated, ha, hg_uf], int_equiv_refl _,
          ⟨u_free_has_single_U_type ha, u_free_has_single_U_type hBq_uf⟩⟩
      · exact u_free_separable_with_type hx
  · apply and_separable_with_U_type
    · exact and_separable_with_U_type
        ⟨.snce a (Formula.and y q),
          by simp [is_syntactically_separated, ha, hBq_uf], int_equiv_refl _,
          ⟨u_free_has_single_U_type ha, u_free_has_single_U_type hBq_uf⟩⟩
        (u_free_separable_with_type hy)
    · exact untl_s_free_separable_with_type hx' hy'

end Cslib.Logic.Bimodal.Metalogic.Separation
