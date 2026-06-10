/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Separation.Hierarchy.HierarchyInduction

/-!
# Hierarchy Completion: U-Type-Preserving Separation and Final all_formulas_separable

Steps 5c-5d and JD infrastructure: U-type-preserving separation,
separable_with_U_type strengthening, combinators, Cases 5-8 with U-type
preservation, single-U-type separability (axiom-free), GHR94 Lemma 10.2.6/10.2.7,
oracle threading, and all_formulas_separable.
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedDecidableInType false
set_option linter.style.maxHeartbeats false
@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Separation

variable {Atom : Type*} [DecidableEq Atom] [Infinite Atom]

open Cslib.Logic.Bimodal

/-- GHR94 Lemma 10.2.6 (parameterized): A formula with `no_S_nested_in_U` and
    `has_no_allpast_allfuture` is separable, given a callback for handling
    the `.snce`/`.allPast` constituents produced by substitution.

    The callback receives formulas with `no_S_nested_in_U` that arise from
    substituting `.untl A B` (S-free args) into U-free positions of a
    separated formula. These callback formulas have single U-type U(A,B). -/
theorem no_S_nested_in_U_separable_param (phi : Formula Atom)
    (hns : no_S_nested_in_U phi)
    (hexp : has_no_allpast_allfuture phi = true)
    (callback : ∀ (χ : Formula Atom), no_S_nested_in_U χ → is_separable χ) :
    is_separable phi := by
  -- Strong induction on count_U_subformulas
  induction h : count_U_subformulas phi using Nat.strongRecOn generalizing phi with
  | ind n ih =>
  -- Case n = 0: U-free, syntactically separated
  by_cases huf : is_U_free phi = true
  · exact separated_imp_separable phi (restricted_u_free_separated phi hexp huf)
  · -- Case n > 0: extract U-type and abstract
    push_neg at huf; simp [Bool.not_eq_true] at huf
    have huf' : is_U_free phi = false := huf
    let AB := extract_U_type phi huf' hns
    have hAB_sf := extract_U_type_S_free phi huf' hns
    let p := fresh_atom phi
    have hfresh := fresh_atom_not_in phi
    let phi' := abstract_untl phi AB.1 AB.2 p
    have hcontains := extract_U_type_contains_surface phi huf' hns
    have hcount_lt : count_U_subformulas phi' < count_U_subformulas phi :=
      abstract_untl_count_lt_of_contains_surface phi AB.1 AB.2 p hcontains
    have hns' : no_S_nested_in_U phi' :=
      abstract_untl_preserves_no_S_nested phi AB.1 AB.2 p hns
    have hexp' : has_no_allpast_allfuture phi' = true :=
      abstract_untl_preserves_no_allpast_allfuture phi AB.1 AB.2 p hexp
    -- phi' is separable by IH (strictly fewer U-subformulas)
    have h_phi'_sep : is_separable phi' := by
      exact ih (count_U_subformulas phi') (h ▸ hcount_lt) phi' hns' hexp' rfl
    -- Get separated psi equivalent to phi'
    obtain ⟨psi, hpsi_sep, hpsi_equiv⟩ := h_phi'_sep
    -- phi = subst(phi', p, U(A,B)) by syntactic roundtrip
    have hroundtrip : subst_formula phi' p (.untl AB.1 AB.2) = phi :=
      abstract_subst_roundtrip phi AB.1 AB.2 p hfresh
    -- phi is equiv to subst(psi, p, U(A,B)) by congruence
    have hphi_equiv : int_equiv phi (subst_formula psi p (.untl AB.1 AB.2)) := by
      rw [← hroundtrip]
      exact subst_formula_congr hpsi_equiv p (.untl AB.1 AB.2)
    -- subst(psi, p, U(A,B)) is separable via constituent substitution
    have h_subst_sep : is_separable (subst_formula psi p (.untl AB.1 AB.2)) :=
      subst_in_separated_separable psi p AB.1 AB.2
        hAB_sf.1 hAB_sf.2 hpsi_sep callback
    exact is_separable_of_equiv hphi_equiv h_subst_sep

/-! ### Step 5c': Single-U-Type Separability (GHR94 Lemma 10.2.5, axiom-free)

The main inductive theorem: any formula with single-U-type is separable.
Uses strong induction on snce_depth_of_U. The key `.snce` case at depth >= 2
recurses on children (strict depth decrease), producing separated witnesses
WITH single-U-type preservation. Box-normalization + leaf case finishes it. -/

/-- has_single_U_type with S-free A, B implies no_S_nested_in_U.
    This follows because no_S_nested_in_U checks that .untl args are S-free,
    and has_single_U_type forces every .untl to be .untl A B where A, B are S-free. -/
theorem has_single_U_type_gives_no_S_nested (phi A B : Formula Atom)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true)
    (h_single : has_single_U_type phi A B) :
    no_S_nested_in_U phi := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 => exact ⟨ih1 h_single.1, ih2 h_single.2⟩
  | box a ih => exact ih h_single
  | untl a b _ _ =>
    have ⟨ha, hb⟩ := h_single; subst ha; subst hb
    exact ⟨hA_sf, hB_sf⟩
  | snce a b ih1 ih2 => exact ⟨ih1 h_single.1, ih2 h_single.2⟩

/-- Box-normalization preserves has_single_U_type with box-normalized args:
    if has_single_U_type phi A B, then
    has_single_U_type (replace_box_with_top phi) (replace_box_with_top A) (replace_box_with_top B). -/
theorem replace_box_preserves_single_U_type (phi A B : Formula Atom)
    (h : has_single_U_type phi A B) :
    has_single_U_type (replace_box_with_top phi) (replace_box_with_top A) (replace_box_with_top B) := by
  induction phi with
  | atom _ => trivial
  | bot => trivial
  | imp a b ih1 ih2 =>
    exact ⟨ih1 h.1, ih2 h.2⟩
  | box _ => -- replace_box_with_top (.box _) = .imp .bot .bot
    simp only [replace_box_with_top, has_single_U_type]; trivial
  | untl a b _ _ =>
    have ⟨ha, hb⟩ := h; subst ha; subst hb
    simp only [replace_box_with_top, has_single_U_type]; trivial
  | snce a b ih1 ih2 =>
    exact ⟨ih1 h.1, ih2 h.2⟩

/-- GHR94 Lemma 10.2.5 (oracle-parameterized):
    A formula with single U-type U(A,B) (where A, B are S-free and U-free)
    is separable, given an oracle for `no_S_nested_in_U` formulas with JD ≤ 1.

    The `.snce` case splits by snce_depth_of_U:
    - **depth 0**: Both C, w are U-free. Already syntactically separated.
    - **depth 1** (leaf case): C, w at depth 0 have `has_single_U_type` and are
      already syntactically separated. Box-normalize preserves single-U-type.
      Apply `snce_single_U_depth_one_separable` (Lemma 10.2.4) directly.
      **The oracle is NOT invoked at depth 1.**
    - **depth >= 2**: IH on C, w (strict depth decrease). Box-normalize.
      Apply oracle on the normalized `.snce C'' w''` (which has JD ≤ 1).

    GHR94 reference: Lemma 10.2.5, pp. 569. "By induction on the maximum
    number k of nested Ss above any U(A,B)."

    The oracle is provided by `all_formulas_separable_aux` via JD induction.
    At n = 1, the oracle is never invoked (all paths terminate at depth ≤ 1
    via the leaf case), breaking the circularity. -/
theorem single_U_formula_separable_noax_param (phi A B : Formula Atom)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (h_single : has_single_U_type phi A B)
    (oracle : ∀ (chi : Formula Atom), no_S_nested_in_U chi →
        junction_depth chi ≤ 1 → is_separable chi) :
    is_separable phi := by
  -- Strong induction on snce_depth_of_U
  have : ∀ (n : Nat) (ψ : Formula Atom), snce_depth_of_U ψ ≤ n →
      has_single_U_type ψ A B → is_separable ψ := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih_depth =>
    intro ψ hdepth h_single_ψ
    induction ψ with
    | atom a => exact ⟨.atom a, rfl, int_equiv_refl _⟩
    | bot => exact ⟨.bot, rfl, int_equiv_refl _⟩
    | imp a b ih_a ih_b =>
      have hle_a : snce_depth_of_U a ≤ n := Nat.le_trans (snce_depth_of_U_le_imp_left a b) hdepth
      have hle_b : snce_depth_of_U b ≤ n := Nat.le_trans (snce_depth_of_U_le_imp_right a b) hdepth
      exact imp_separable (ih_a hle_a h_single_ψ.1) (ih_b hle_b h_single_ψ.2)
    | box _ => exact ⟨.box _, rfl, int_equiv_refl _⟩
    | untl a b _ _ =>
      have ⟨ha, hb⟩ := h_single_ψ; subst ha; subst hb
      exact untl_s_free_separable hA_sf hB_sf
    | snce C w ih_C ih_F =>
      by_cases huf : is_U_free C = true ∧ is_U_free w = true
      · exact ⟨.snce C w, by simp [is_syntactically_separated, huf.1, huf.2], int_equiv_refl _⟩
      · -- snce_depth_of_U >= 1
        have hlt_C := (snce_depth_of_U_lt_snce C w huf).1
        have hlt_F := (snce_depth_of_U_lt_snce C w huf).2
        have hle_C : snce_depth_of_U C ≤ n := Nat.le_of_lt (Nat.lt_of_lt_of_le hlt_C hdepth)
        have hle_F : snce_depth_of_U w ≤ n := Nat.le_of_lt (Nat.lt_of_lt_of_le hlt_F hdepth)
        -- Split: depth 1 (leaf, no oracle) vs depth >= 2 (uses oracle)
        by_cases hn_le1 : n ≤ 1
        · -- Depth 1 leaf case (n ≤ 1 means snce_depth_of_U C = 0, w = 0).
          -- C, F at depth 0 with has_single_U_type are already syntactically separated.
          -- Box-normalize preserves single-U-type. Apply Lemma 10.2.4 directly.
          have hdC : snce_depth_of_U C = 0 := by omega
          have hdF : snce_depth_of_U w = 0 := by omega
          have hC_sep_raw : is_syntactically_separated C = true :=
            snce_depth_zero_single_U_separated C A B hA_sf hB_sf h_single_ψ.1
              (has_no_allpast_allfuture_true C) hdC
          have hF_sep_raw : is_syntactically_separated w = true :=
            snce_depth_zero_single_U_separated w A B hA_sf hB_sf h_single_ψ.2
              (has_no_allpast_allfuture_true w) hdF
          -- Box-normalize
          let C'' := replace_box_with_top C
          let w'' := replace_box_with_top w
          let A'' := replace_box_with_top A
          let B'' := replace_box_with_top B
          have hequiv : int_equiv (.snce C w) (.snce C'' w'') :=
            snce_congr (replace_box_equiv C) (replace_box_equiv w)
          have hsingle_C'' : has_single_U_type C'' A'' B'' :=
            replace_box_preserves_single_U_type C A B h_single_ψ.1
          have hsingle_F'' : has_single_U_type w'' A'' B'' :=
            replace_box_preserves_single_U_type w A B h_single_ψ.2
          have hdC'' : snce_depth_of_U C'' = 0 := separated_boxnorm_snce_depth_zero C hC_sep_raw
          have hdF'' : snce_depth_of_U w'' = 0 := separated_boxnorm_snce_depth_zero w hF_sep_raw
          have hA''_sf : is_S_free A'' = true := replace_box_preserves_S_free A hA_sf
          have hB''_sf : is_S_free B'' = true := replace_box_preserves_S_free B hB_sf
          have hA''_uf : is_U_free A'' = true := replace_box_preserves_U_free A hA_uf
          have hB''_uf : is_U_free B'' = true := replace_box_preserves_U_free B hB_uf
          -- Apply snce_single_U_depth_one_separable (Lemma 10.2.4) -- no oracle needed
          exact is_separable_of_equiv hequiv
            (snce_single_U_depth_one_separable C'' w'' A'' B''
              hA''_sf hB''_sf hA''_uf hB''_uf
              hsingle_C'' hsingle_F'' hdC'' hdF''
              (has_no_allpast_allfuture_true C'') (has_no_allpast_allfuture_true w''))
        · -- Depth >= 2: IH on C, w, then apply oracle on .snce C'' w''
          push_neg at hn_le1
          have hC_sep : is_separable C := ih_C hle_C h_single_ψ.1
          have hF_sep : is_separable w := ih_F hle_F h_single_ψ.2
          obtain ⟨C', hC'_sep, hC'_equiv⟩ := hC_sep
          obtain ⟨w', hF'_sep, hF'_equiv⟩ := hF_sep
          let C'' := replace_box_with_top C'
          let w'' := replace_box_with_top w'
          have hequiv : int_equiv (.snce C w) (.snce C'' w'') :=
            int_equiv_trans (snce_congr hC'_equiv hF'_equiv)
              (snce_congr (replace_box_equiv C') (replace_box_equiv w'))
          have hns : no_S_nested_in_U (.snce C'' w'') :=
            snce_of_boxfree_sep_no_S_nested C' w' hC'_sep hF'_sep
          have hjd : junction_depth (.snce C'' w'') ≤ 1 :=
            snce_of_boxfree_sep_jd_le_one C' w' hC'_sep hF'_sep
          -- Apply oracle (depth >= 2, so oracle invocation is safe)
          exact is_separable_of_equiv hequiv (oracle (.snce C'' w'') hns hjd)
  exact this (snce_depth_of_U phi) phi (Nat.le_refl _) h_single

/-- GHR94 Lemma 10.2.5 (oracle-free, returning is_separable_with_U_type):
    A formula with single U-type U(A,B) (where A, B are S-free and U-free)
    is `is_separable_with_U_type _ A B`.

    By strong induction on `snce_depth_of_U`:
    - `.atom`, `.bot`, `.box`: trivial
    - `.imp`: combine via `imp_separable_with_type`
    - `.untl`: `has_single_U_type` forces args = (A, B)
    - `.snce` at depth 0: U-free → `u_free_separable_with_type`
    - `.snce` at depth 1: `snce_single_U_depth_one_sep_with_U_type` (Phase 2)
    - `.snce` at depth >= 2: IH on children (strict depth decrease), box-normalize,
      apply `snce_single_U_depth_one_sep_with_U_type`. **NO ORACLE.** -/
theorem single_U_formula_sep_with_U_type_no_oracle (phi A B : Formula Atom)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (h_single : has_single_U_type phi A B) :
    is_separable_with_U_type phi A B := by
  -- Strong induction on snce_depth_of_U
  have : ∀ (n : Nat) (ψ : Formula Atom), snce_depth_of_U ψ ≤ n →
      has_single_U_type ψ A B → is_separable_with_U_type ψ A B := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih_depth =>
    intro ψ hdepth h_single_ψ
    induction ψ with
    | atom a => exact ⟨.atom a, rfl, int_equiv_refl _, trivial⟩
    | bot => exact ⟨.bot, rfl, int_equiv_refl _, trivial⟩
    | imp a b ih_a ih_b =>
      have hle_a : snce_depth_of_U a ≤ n := Nat.le_trans (snce_depth_of_U_le_imp_left a b) hdepth
      have hle_b : snce_depth_of_U b ≤ n := Nat.le_trans (snce_depth_of_U_le_imp_right a b) hdepth
      exact imp_separable_with_type (ih_a hle_a h_single_ψ.1) (ih_b hle_b h_single_ψ.2)
    | box _ =>
      -- .box on Z is equivalent to .imp .bot .bot (True), which is U-free
      exact ⟨.box _, rfl, int_equiv_refl _, h_single_ψ⟩
    | untl a b _ _ =>
      have ⟨ha, hb⟩ := h_single_ψ; subst ha; subst hb
      exact untl_s_free_separable_with_type hA_sf hB_sf
    | snce C w ih_C ih_F =>
      by_cases huf : is_U_free C = true ∧ is_U_free w = true
      · -- depth 0: U-free → separated directly
        exact ⟨.snce C w, by simp [is_syntactically_separated, huf.1, huf.2], int_equiv_refl _,
          ⟨u_free_has_single_U_type huf.1, u_free_has_single_U_type huf.2⟩⟩
      · -- snce_depth_of_U >= 1
        have hlt_C := (snce_depth_of_U_lt_snce C w huf).1
        have hlt_F := (snce_depth_of_U_lt_snce C w huf).2
        have hle_C : snce_depth_of_U C ≤ n := Nat.le_of_lt (Nat.lt_of_lt_of_le hlt_C hdepth)
        have hle_F : snce_depth_of_U w ≤ n := Nat.le_of_lt (Nat.lt_of_lt_of_le hlt_F hdepth)
        -- Split: depth <= 1 (leaf) vs depth >= 2
        by_cases hn_le1 : n ≤ 1
        · -- Depth 1 leaf case: C, w at depth 0
          have hdC : snce_depth_of_U C = 0 := by omega
          have hdF : snce_depth_of_U w = 0 := by omega
          have hC_sep_raw : is_syntactically_separated C = true :=
            snce_depth_zero_single_U_separated C A B hA_sf hB_sf h_single_ψ.1
              (has_no_allpast_allfuture_true C) hdC
          have hF_sep_raw : is_syntactically_separated w = true :=
            snce_depth_zero_single_U_separated w A B hA_sf hB_sf h_single_ψ.2
              (has_no_allpast_allfuture_true w) hdF
          -- Box-normalize
          let C'' := replace_box_with_top C
          let w'' := replace_box_with_top w
          let A'' := replace_box_with_top A
          let B'' := replace_box_with_top B
          have hequiv : int_equiv (.snce C w) (.snce C'' w'') :=
            snce_congr (replace_box_equiv C) (replace_box_equiv w)
          have hsingle_C'' : has_single_U_type C'' A'' B'' :=
            replace_box_preserves_single_U_type C A B h_single_ψ.1
          have hsingle_F'' : has_single_U_type w'' A'' B'' :=
            replace_box_preserves_single_U_type w A B h_single_ψ.2
          have hdC'' : snce_depth_of_U C'' = 0 := separated_boxnorm_snce_depth_zero C hC_sep_raw
          have hdF'' : snce_depth_of_U w'' = 0 := separated_boxnorm_snce_depth_zero w hF_sep_raw
          have hA''_sf : is_S_free A'' = true := replace_box_preserves_S_free A hA_sf
          have hB''_sf : is_S_free B'' = true := replace_box_preserves_S_free B hB_sf
          have hA''_uf : is_U_free A'' = true := replace_box_preserves_U_free A hA_uf
          have hB''_uf : is_U_free B'' = true := replace_box_preserves_U_free B hB_uf
          -- Apply snce_single_U_depth_one_sep_with_U_type on box-normalized args
          have h_sep_AB'' : is_separable_with_U_type (C''.snce w'') A'' B'' :=
            snce_single_U_depth_one_sep_with_U_type C'' w'' A'' B''
              hA''_sf hB''_sf hA''_uf hB''_uf hsingle_C'' hsingle_F'' hdC'' hdF''
              (has_no_allpast_allfuture_true C'') (has_no_allpast_allfuture_true w'')
          -- Transfer from C''.snce F'' to C.snce F via hequiv
          have h_sep_CF_AB'' : is_separable_with_U_type (C.snce w) A'' B'' :=
            is_separable_with_U_type_of_equiv hequiv h_sep_AB''
          -- Bridge from A'' B'' to A B
          exact is_separable_with_U_type_replace_args h_sep_CF_AB''
            (replace_box_equiv A) (replace_box_equiv B) hA_sf hB_sf
        · -- Depth >= 2: IH on C, w → is_separable_with_U_type
          push_neg at hn_le1
          have hC_sep_ut : is_separable_with_U_type C A B := ih_C hle_C h_single_ψ.1
          have hF_sep_ut : is_separable_with_U_type w A B := ih_F hle_F h_single_ψ.2
          obtain ⟨C', hC'_sep, hC'_equiv, hC'_single⟩ := hC_sep_ut
          obtain ⟨w', hF'_sep, hF'_equiv, hF'_single⟩ := hF_sep_ut
          let C'' := replace_box_with_top C'
          let w'' := replace_box_with_top w'
          let A'' := replace_box_with_top A
          let B'' := replace_box_with_top B
          have hequiv : int_equiv (.snce C w) (.snce C'' w'') :=
            int_equiv_trans (snce_congr hC'_equiv hF'_equiv)
              (snce_congr (replace_box_equiv C') (replace_box_equiv w'))
          have hsingle_C'' : has_single_U_type C'' A'' B'' :=
            replace_box_preserves_single_U_type C' A B hC'_single
          have hsingle_F'' : has_single_U_type w'' A'' B'' :=
            replace_box_preserves_single_U_type w' A B hF'_single
          have hdC'' : snce_depth_of_U C'' = 0 := separated_boxnorm_snce_depth_zero C' hC'_sep
          have hdF'' : snce_depth_of_U w'' = 0 := separated_boxnorm_snce_depth_zero w' hF'_sep
          have hA''_sf : is_S_free A'' = true := replace_box_preserves_S_free A hA_sf
          have hB''_sf : is_S_free B'' = true := replace_box_preserves_S_free B hB_sf
          have hA''_uf : is_U_free A'' = true := replace_box_preserves_U_free A hA_uf
          have hB''_uf : is_U_free B'' = true := replace_box_preserves_U_free B hB_uf
          -- Apply snce_single_U_depth_one_sep_with_U_type on box-normalized args
          have h_sep_AB'' : is_separable_with_U_type (C''.snce w'') A'' B'' :=
            snce_single_U_depth_one_sep_with_U_type C'' w'' A'' B''
              hA''_sf hB''_sf hA''_uf hB''_uf hsingle_C'' hsingle_F'' hdC'' hdF''
              (has_no_allpast_allfuture_true C'') (has_no_allpast_allfuture_true w'')
          -- Transfer from C''.snce F'' to C.snce F via hequiv
          have h_sep_CF_AB'' : is_separable_with_U_type (C.snce w) A'' B'' :=
            is_separable_with_U_type_of_equiv hequiv h_sep_AB''
          -- Bridge from A'' B'' to A B
          exact is_separable_with_U_type_replace_args h_sep_CF_AB''
            (replace_box_equiv A) (replace_box_equiv B) hA_sf hB_sf
  exact this (snce_depth_of_U phi) phi (Nat.le_refl _) h_single

/-- Oracle-free corollary: is_separable for single-U-type formulas. -/
theorem single_U_formula_separable_no_oracle (phi A B : Formula Atom)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (h_single : has_single_U_type phi A B) :
    is_separable phi :=
  separable_with_type_imp_separable
    (single_U_formula_sep_with_U_type_no_oracle phi A B hA_sf hB_sf hA_uf hB_uf h_single)

/-- GHR94 Lemma 10.2.5 (backward-compatible wrapper):
    Now delegates to the oracle-free version. -/
theorem single_U_formula_separable_noax (phi A B : Formula Atom)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (h_single : has_single_U_type phi A B) :
    is_separable phi :=
  single_U_formula_separable_no_oracle phi A B hA_sf hB_sf hA_uf hB_uf h_single

/-! ### Step 5d': GHR94 Lemma 10.2.6 (self-contained) and Lemma 10.2.7 (direct)

Lemma 10.2.6: `no_S_nested_in_U phi` and `U_nesting_depth phi <= 1` implies separable.
Lemma 10.2.7: `no_S_nested_in_U phi` implies separable (by U_nesting_depth induction). -/

/-- Helper: `extract_U_type` returns U-free arguments when `U_nesting_depth phi <= 1`.
    At depth <= 1, every `.untl a b` has `U_nesting_depth (.untl a b) <= 1`,
    so `U_nesting_depth a = 0` and `U_nesting_depth b = 0`, meaning a and b are U-free. -/
private theorem extract_U_type_U_free (φ : Formula Atom) (h : is_U_free φ = false)
    (hns : no_S_nested_in_U φ) (hdepth : U_nesting_depth φ ≤ 1) :
    is_U_free (extract_U_type φ h hns).1 = true ∧
    is_U_free (extract_U_type φ h hns).2 = true := by
  induction φ with
  | atom _ => simp [is_U_free] at h
  | bot => simp [is_U_free] at h
  | imp c d ih1 ih2 =>
    unfold extract_U_type
    by_cases hc : is_U_free c = false
    · simp only [hc, ↓reduceDIte]
      have hle : U_nesting_depth c ≤ 1 := Nat.le_trans (U_nesting_depth_le_imp_left c d) hdepth
      exact ih1 hc hns.1 hle
    · simp only [hc, ↓reduceDIte]
      have hd : is_U_free d = false := by
        simp only [is_U_free] at h; cases huf : is_U_free c <;> simp_all
      have hle : U_nesting_depth d ≤ 1 := Nat.le_trans (U_nesting_depth_le_imp_right c d) hdepth
      exact ih2 hd hns.2 hle
  | box c ih =>
    simp only [is_U_free] at h
    unfold extract_U_type
    have hle : U_nesting_depth c ≤ 1 := by
      simp only [U_nesting_depth] at hdepth; exact hdepth
    exact ih h hns hle
  | untl a b =>
    unfold extract_U_type
    exact U_nesting_depth_le_one_untl_args_U_free a b hdepth
  | snce c d ih1 ih2 =>
    unfold extract_U_type
    by_cases hc : is_U_free c = false
    · simp only [hc, ↓reduceDIte]
      have hle : U_nesting_depth c ≤ 1 := Nat.le_trans (U_nesting_depth_le_snce_left c d) hdepth
      exact ih1 hc hns.1 hle
    · simp only [hc, ↓reduceDIte]
      have hd : is_U_free d = false := by
        simp only [is_U_free] at h; cases huf : is_U_free c <;> simp_all
      have hle : U_nesting_depth d ≤ 1 := Nat.le_trans (U_nesting_depth_le_snce_right c d) hdepth
      exact ih2 hd hns.2 hle

/-- GHR94 Lemma 10.2.6 (oracle-parameterized):
    A formula with `no_S_nested_in_U` and `U_nesting_depth <= 1` is separable,
    given an oracle for `no_S_nested_in_U` formulas with JD ≤ 1.

    Proved by inlining the `no_S_nested_in_U_separable_param` logic with
    `single_U_formula_separable_noax_param` as the callback for `.snce` nodes.
    The oracle is threaded through to `single_U_formula_separable_noax_param`. -/
theorem lemma_10_2_6_self_contained_param (phi : Formula Atom)
    (hns : no_S_nested_in_U phi)
    (hd : U_nesting_depth phi ≤ 1)
    (oracle : ∀ (chi : Formula Atom), no_S_nested_in_U chi →
        junction_depth chi ≤ 1 → is_separable chi) :
    is_separable phi := by
  induction h : count_U_subformulas phi using Nat.strongRecOn generalizing phi with
  | ind n ih =>
  have hexp : has_no_allpast_allfuture phi = true := has_no_allpast_allfuture_true phi
  by_cases huf : is_U_free phi = true
  · exact separated_imp_separable phi (restricted_u_free_separated phi hexp huf)
  · push_neg at huf; simp [Bool.not_eq_true] at huf
    have huf' : is_U_free phi = false := huf
    let AB := extract_U_type phi huf' hns
    have hAB_sf := extract_U_type_S_free phi huf' hns
    have hAB_uf := extract_U_type_U_free phi huf' hns hd
    let p := fresh_atom phi
    have hfresh := fresh_atom_not_in phi
    let phi' := abstract_untl phi AB.1 AB.2 p
    have hcontains := extract_U_type_contains_surface phi huf' hns
    have hcount_lt : count_U_subformulas phi' < count_U_subformulas phi :=
      abstract_untl_count_lt_of_contains_surface phi AB.1 AB.2 p hcontains
    have hns' : no_S_nested_in_U phi' :=
      abstract_untl_preserves_no_S_nested phi AB.1 AB.2 p hns
    have h_phi'_sep : is_separable phi' := by
      exact ih (count_U_subformulas phi') (h ▸ hcount_lt) phi' hns'
        (abstract_untl_U_nesting_depth_le_of_le phi AB.1 AB.2 p 1 hd) rfl
    obtain ⟨psi, hpsi_sep, hpsi_equiv⟩ := h_phi'_sep
    have hroundtrip : subst_formula phi' p (.untl AB.1 AB.2) = phi :=
      abstract_subst_roundtrip phi AB.1 AB.2 p hfresh
    have hphi_equiv : int_equiv phi (subst_formula psi p (.untl AB.1 AB.2)) := by
      rw [← hroundtrip]
      exact subst_formula_congr hpsi_equiv p (.untl AB.1 AB.2)
    -- Use single_U_formula_separable_noax_param with oracle (NOT all_separable)
    have h_subst_sep : is_separable (subst_formula psi p (.untl AB.1 AB.2)) :=
      subst_in_separated_separable_typed psi p AB.1 AB.2
        hAB_sf.1 hAB_sf.2 hAB_uf.1 hAB_uf.2 hpsi_sep
        (fun χ _hns_χ hsingle_χ =>
          single_U_formula_separable_noax_param χ AB.1 AB.2
            hAB_sf.1 hAB_sf.2 hAB_uf.1 hAB_uf.2 hsingle_χ oracle)
    exact is_separable_of_equiv hphi_equiv h_subst_sep

/-- GHR94 Lemma 10.2.6 (oracle-free):
    Uses `single_U_formula_separable_no_oracle` directly instead of an oracle. -/
theorem lemma_10_2_6_no_oracle (phi : Formula Atom)
    (hns : no_S_nested_in_U phi)
    (hd : U_nesting_depth phi ≤ 1) :
    is_separable phi := by
  induction h : count_U_subformulas phi using Nat.strongRecOn generalizing phi with
  | ind n ih =>
  have hexp : has_no_allpast_allfuture phi = true := has_no_allpast_allfuture_true phi
  by_cases huf : is_U_free phi = true
  · exact separated_imp_separable phi (restricted_u_free_separated phi hexp huf)
  · push_neg at huf; simp [Bool.not_eq_true] at huf
    have huf' : is_U_free phi = false := huf
    let AB := extract_U_type phi huf' hns
    have hAB_sf := extract_U_type_S_free phi huf' hns
    have hAB_uf := extract_U_type_U_free phi huf' hns hd
    let p := fresh_atom phi
    have hfresh := fresh_atom_not_in phi
    let phi' := abstract_untl phi AB.1 AB.2 p
    have hcontains := extract_U_type_contains_surface phi huf' hns
    have hcount_lt : count_U_subformulas phi' < count_U_subformulas phi :=
      abstract_untl_count_lt_of_contains_surface phi AB.1 AB.2 p hcontains
    have hns' : no_S_nested_in_U phi' :=
      abstract_untl_preserves_no_S_nested phi AB.1 AB.2 p hns
    have h_phi'_sep : is_separable phi' := by
      exact ih (count_U_subformulas phi') (h ▸ hcount_lt) phi' hns'
        (abstract_untl_U_nesting_depth_le_of_le phi AB.1 AB.2 p 1 hd) rfl
    obtain ⟨psi, hpsi_sep, hpsi_equiv⟩ := h_phi'_sep
    have hroundtrip : subst_formula phi' p (.untl AB.1 AB.2) = phi :=
      abstract_subst_roundtrip phi AB.1 AB.2 p hfresh
    have hphi_equiv : int_equiv phi (subst_formula psi p (.untl AB.1 AB.2)) := by
      rw [← hroundtrip]
      exact subst_formula_congr hpsi_equiv p (.untl AB.1 AB.2)
    -- Use single_U_formula_separable_no_oracle (NO ORACLE)
    have h_subst_sep : is_separable (subst_formula psi p (.untl AB.1 AB.2)) :=
      subst_in_separated_separable_typed psi p AB.1 AB.2
        hAB_sf.1 hAB_sf.2 hAB_uf.1 hAB_uf.2 hpsi_sep
        (fun χ _hns_χ hsingle_χ =>
          single_U_formula_separable_no_oracle χ AB.1 AB.2
            hAB_sf.1 hAB_sf.2 hAB_uf.1 hAB_uf.2 hsingle_χ)
    exact is_separable_of_equiv hphi_equiv h_subst_sep

/-- GHR94 Lemma 10.2.6 (backward-compatible wrapper):
    Now delegates to the oracle-free version. -/
theorem lemma_10_2_6_self_contained (phi : Formula Atom)
    (hns : no_S_nested_in_U phi)
    (hd : U_nesting_depth phi ≤ 1) :
    is_separable phi :=
  lemma_10_2_6_no_oracle phi hns hd

/-- Substituting `.untl A B` (with U-free A, B) into a U-free formula gives
    `U_nesting_depth <= 1`. Since the base formula has no `.untl` nodes, the only
    `.untl` in the result comes from substituting `.untl A B` for atoms. Each such
    occurrence has depth 1 (U-free args), and they don't nest inside each other. -/
private theorem subst_U_free_U_nesting_depth_le_one (ψ : Formula Atom) (p : Atom) (A B : Formula Atom)
    (hψ_uf : is_U_free ψ = true) (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true) :
    U_nesting_depth (subst_formula ψ p (.untl A B)) ≤ 1 := by
  induction ψ with
  | atom a =>
    simp only [subst_formula]
    split
    · -- a = p: result is .untl A B
      simp only [U_nesting_depth]
      have ha := U_nesting_depth_zero_of_U_free A hA_uf
      have hb := U_nesting_depth_zero_of_U_free B hB_uf
      omega
    · simp only [U_nesting_depth]; omega
  | bot => simp only [subst_formula, U_nesting_depth]; omega
  | imp a b ih1 ih2 =>
    simp only [is_U_free, Bool.and_eq_true] at hψ_uf
    simp only [subst_formula, U_nesting_depth]
    have := ih1 hψ_uf.1; have := ih2 hψ_uf.2; omega
  | box a ih =>
    simp only [is_U_free] at hψ_uf
    simp only [subst_formula, U_nesting_depth]; exact ih hψ_uf
  | untl _ _ => simp only [is_U_free] at hψ_uf; exact absurd hψ_uf (by decide)
  | snce a b ih1 ih2 =>
    simp only [is_U_free, Bool.and_eq_true] at hψ_uf
    simp only [subst_formula, U_nesting_depth]
    have := ih1 hψ_uf.1; have := ih2 hψ_uf.2; omega

/-- Callback formulas from `subst_in_separated_separable_typed` have `U_nesting_depth ≤ 1`
    when A, B are U-free. The callback formula is `.snce (subst c p (.untl A B)) (subst d p (.untl A B))`
    where c, d are U-free. -/
private theorem callback_U_nesting_depth_le_one (c d : Formula Atom) (p : Atom) (A B : Formula Atom)
    (hc_uf : is_U_free c = true) (hd_uf : is_U_free d = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true) :
    U_nesting_depth (.snce (subst_formula c p (.untl A B))
                           (subst_formula d p (.untl A B))) ≤ 1 := by
  simp only [U_nesting_depth]
  have h1 := subst_U_free_U_nesting_depth_le_one c p A B hc_uf hA_uf hB_uf
  have h2 := subst_U_free_U_nesting_depth_le_one d p A B hd_uf hA_uf hB_uf
  omega

/-- Version of `subst_in_separated_separable` where the callback also receives
    `U_nesting_depth χ ≤ 1`. Used by `no_S_nested_sep` to thread the
    `U_nesting_depth` IH through back-substitution at depth >= 2.
    Requires U-free A, B (so callback formulas have depth <= 1). -/
theorem subst_in_separated_separable_depth (ψ : Formula Atom) (p : Atom) (A B : Formula Atom)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true)
    (hA_uf : is_U_free A = true) (hB_uf : is_U_free B = true)
    (hsep : is_syntactically_separated ψ = true)
    (ih_snce : ∀ (χ : Formula Atom), no_S_nested_in_U χ →
        U_nesting_depth χ ≤ 1 → is_separable χ) :
    is_separable (subst_formula ψ p (.untl A B)) := by
  induction ψ with
  | atom a =>
    simp only [subst_formula]; split
    · exact ⟨.untl A B, by simp [is_syntactically_separated, hA_sf, hB_sf], int_equiv_refl _⟩
    · exact ⟨.atom a, rfl, int_equiv_refl _⟩
  | bot => exact ⟨.bot, rfl, int_equiv_refl _⟩
  | box ψ => exact ⟨.box (subst_formula ψ p (.untl A B)), rfl, int_equiv_refl _⟩
  | imp c d ih_c ih_d =>
    simp [is_syntactically_separated] at hsep
    exact imp_separable (ih_c hsep.1) (ih_d hsep.2)
  | untl c d _ _ =>
    simp [is_syntactically_separated] at hsep
    have hU_sf : is_S_free (.untl A B) = true := by
      simp only [is_S_free, hA_sf, hB_sf, Bool.and_self]
    exact ⟨.untl (subst_formula c p (.untl A B)) (subst_formula d p (.untl A B)),
           by simp [is_syntactically_separated,
                     subst_S_free_preserves_S_free c p _ hsep.1 hU_sf,
                     subst_S_free_preserves_S_free d p _ hsep.2 hU_sf],
           int_equiv_refl _⟩
  | snce c d _ _ =>
    simp [is_syntactically_separated] at hsep
    have hns : no_S_nested_in_U (.snce (subst_formula c p (.untl A B))
        (subst_formula d p (.untl A B))) :=
      ⟨subst_U_free_gives_no_S_nested c p A B hsep.1 hA_sf hB_sf,
       subst_U_free_gives_no_S_nested d p A B hsep.2 hA_sf hB_sf⟩
    have hdepth : U_nesting_depth (.snce (subst_formula c p (.untl A B))
        (subst_formula d p (.untl A B))) ≤ 1 :=
      callback_U_nesting_depth_le_one c d p A B hsep.1 hsep.2 hA_uf hB_uf
    exact ih_snce _ hns hdepth

/-! ### JD Infrastructure for Oracle Threading

These helpers establish that callback formulas produced during separation have
junction_depth ≤ 1, enabling the JD-bounded oracle pattern. -/

/-- Junction depth 0 with expanded gives separated (re-export for convenience). -/
private theorem jd_zero_sep (φ : Formula Atom)
    (hexp : has_no_allpast_allfuture φ = true) (hjd : junction_depth φ = 0) :
    is_separable φ :=
  separated_imp_separable φ (expanded_jd_zero_imp_separated φ hexp hjd)

/-- Callback formulas from `subst_in_separated_separable` have junction_depth ≤ 1.
    This follows because: (1) the `.snce c d` branches c, d of a separated formula
    are U-free, hence have junction_depth_S = 0; (2) substituting `.untl A B` (with
    S-free A, B) into U-free formulas gives junction_depth_S ≤ 1; (3) the callback
    `.snce (subst c p (.untl A B)) (subst d p (.untl A B))` has JD = max of these ≤ 1. -/
private theorem callback_jd_le_one (c d : Formula Atom) (p : Atom) (A B : Formula Atom)
    (hc_uf : is_U_free c = true) (hd_uf : is_U_free d = true)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true) :
    junction_depth (.snce (subst_formula c p (.untl A B)) (subst_formula d p (.untl A B))) ≤ 1 := by
  simp only [junction_depth]
  have h1 := subst_u_free_jdS_le_one c p A B hc_uf hA_sf hB_sf
  have h2 := subst_u_free_jdS_le_one d p A B hd_uf hA_sf hB_sf
  omega
where
  /-- Substituting `.untl A B` (S-free args) into a U-free formula gives jdS ≤ 1. -/
  subst_u_free_jdS_le_one (φ : Formula Atom) (p : Atom) (A B : Formula Atom)
      (huf : is_U_free φ = true) (hA : is_S_free A = true) (hB : is_S_free B = true) :
      junction_depth_S (subst_formula φ p (.untl A B)) ≤ 1 := by
    induction φ with
    | atom a =>
      simp only [subst_formula]
      split
      · -- a = p: result is .untl A B
        simp only [junction_depth_S]
        have hA0 := s_free_junction_depth_zero A hA
        have hB0 := s_free_junction_depth_zero B hB
        omega
      · simp [junction_depth_S]
    | bot => simp [subst_formula, junction_depth_S]
    | imp a b ih1 ih2 =>
      simp [is_U_free] at huf
      simp [subst_formula, junction_depth_S, ih1 huf.1, ih2 huf.2]
    | box a ih =>
      simp [is_U_free] at huf
      simp [subst_formula, junction_depth_S, ih huf]
    | untl _ _ => simp [is_U_free] at huf
    | snce a b ih1 ih2 =>
      simp [is_U_free] at huf
      simp [subst_formula, junction_depth_S, ih1 huf.1, ih2 huf.2]

/-- Callback formulas from substitution into separated formulas have has_no_allpast_allfuture. -/
private theorem callback_has_no_allpast_allfuture (c d : Formula Atom) (p : Atom) (A B : Formula Atom) :
    has_no_allpast_allfuture
      (.snce (subst_formula c p (.untl A B)) (subst_formula d p (.untl A B))) = true := by
  exact has_no_allpast_allfuture_true _

/-- Version of `subst_in_separated_separable` where the callback also receives a
    junction_depth bound. The callback formulas have JD ≤ 1. -/
theorem subst_in_separated_separable_jd (ψ : Formula Atom) (p : Atom) (A B : Formula Atom)
    (hA_sf : is_S_free A = true) (hB_sf : is_S_free B = true)
    (hsep : is_syntactically_separated ψ = true)
    (ih_snce : ∀ (χ : Formula Atom), no_S_nested_in_U χ → junction_depth χ ≤ 1 → is_separable χ) :
    is_separable (subst_formula ψ p (.untl A B)) := by
  induction ψ with
  | atom a =>
    simp only [subst_formula]; split
    · exact ⟨.untl A B, by simp [is_syntactically_separated, hA_sf, hB_sf], int_equiv_refl _⟩
    · exact ⟨.atom a, rfl, int_equiv_refl _⟩
  | bot => exact ⟨.bot, rfl, int_equiv_refl _⟩
  | box ψ => exact ⟨.box (subst_formula ψ p (.untl A B)), rfl, int_equiv_refl _⟩
  | imp c d ih_c ih_d =>
    simp [is_syntactically_separated] at hsep
    exact imp_separable (ih_c hsep.1) (ih_d hsep.2)
  | untl c d _ _ =>
    simp [is_syntactically_separated] at hsep
    have hU_sf : is_S_free (.untl A B) = true := by
      simp only [is_S_free, hA_sf, hB_sf, Bool.and_self]
    exact ⟨.untl (subst_formula c p (.untl A B)) (subst_formula d p (.untl A B)),
           by simp [is_syntactically_separated,
                     subst_S_free_preserves_S_free c p _ hsep.1 hU_sf,
                     subst_S_free_preserves_S_free d p _ hsep.2 hU_sf],
           int_equiv_refl _⟩
  | snce c d _ _ =>
    simp [is_syntactically_separated] at hsep
    have hns : no_S_nested_in_U (.snce (subst_formula c p (.untl A B))
        (subst_formula d p (.untl A B))) :=
      ⟨subst_U_free_gives_no_S_nested c p A B hsep.1 hA_sf hB_sf,
       subst_U_free_gives_no_S_nested d p A B hsep.2 hA_sf hB_sf⟩
    have hjd_bound : junction_depth (.snce (subst_formula c p (.untl A B))
        (subst_formula d p (.untl A B))) ≤ 1 :=
      callback_jd_le_one c d p A B hsep.1 hsep.2 hA_sf hB_sf
    exact ih_snce _ hns hjd_bound

/-- GHR94 Lemma 10.2.7 (oracle-parameterized):
    A formula with `no_S_nested_in_U` is separable, given an oracle for
    `no_S_nested_in_U` formulas with JD ≤ 1.

    Proved by strong induction on `U_nesting_depth`.
    - Depth ≤ 1: `lemma_10_2_6_self_contained_param` with oracle.
    - Depth ≥ 2: Abstract a surface `.untl A B`, prove abstracted formula
      separable by inner `count_U_subformulas` induction, then back-substitute
      using `subst_in_separated_separable_jd` with the oracle (callback
      formulas always have JD ≤ 1, regardless of whether A, B are U-free). -/
theorem no_S_nested_in_U_separable_direct_param (phi : Formula Atom)
    (hns : no_S_nested_in_U phi)
    (oracle : ∀ (chi : Formula Atom), no_S_nested_in_U chi →
        junction_depth chi ≤ 1 → is_separable chi) :
    is_separable phi := by
  -- Outer induction on U_nesting_depth
  have outer : ∀ (d : Nat) (ψ : Formula Atom), U_nesting_depth ψ ≤ d →
      no_S_nested_in_U ψ → is_separable ψ := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih_depth =>
    intro ψ hd_le hns_ψ
    -- Base: depth ≤ 1 -- use lemma_10_2_6_self_contained_param with oracle
    by_cases hd_le1 : d ≤ 1
    · exact lemma_10_2_6_self_contained_param ψ hns_ψ (Nat.le_trans hd_le hd_le1) oracle
    · -- Depth ≥ 2: inner induction on count_U_subformulas
      push_neg at hd_le1
      induction hc : count_U_subformulas ψ using Nat.strongRecOn generalizing ψ with
      | ind m ih_count =>
      have hexp : has_no_allpast_allfuture ψ = true := has_no_allpast_allfuture_true ψ
      -- Base case: U-free
      by_cases huf : is_U_free ψ = true
      · exact separated_imp_separable ψ (restricted_u_free_separated ψ hexp huf)
      · -- Not U-free: extract surface U-type and abstract
        push_neg at huf; simp only [Bool.not_eq_true] at huf
        have huf' : is_U_free ψ = false := huf
        let AB := extract_U_type ψ huf' hns_ψ
        have hAB_sf := extract_U_type_S_free ψ huf' hns_ψ
        let p := fresh_atom ψ
        have hfresh := fresh_atom_not_in ψ
        let ψ' := abstract_untl ψ AB.1 AB.2 p
        have hcontains := extract_U_type_contains_surface ψ huf' hns_ψ
        have hcount_lt : count_U_subformulas ψ' < count_U_subformulas ψ :=
          abstract_untl_count_lt_of_contains_surface ψ AB.1 AB.2 p hcontains
        have hns' := abstract_untl_preserves_no_S_nested ψ AB.1 AB.2 p hns_ψ
        have hdepth_le' := abstract_untl_U_nesting_depth_le_of_le ψ AB.1 AB.2 p d hd_le
        -- ψ' is separable by inner IH (fewer U-subformulas, same depth bound)
        have h_psi'_sep : is_separable ψ' :=
          ih_count (count_U_subformulas ψ') (hc ▸ hcount_lt) ψ' hdepth_le' hns' rfl
        -- Get separated form
        obtain ⟨psi, hpsi_sep, hpsi_equiv⟩ := h_psi'_sep
        -- Roundtrip: subst(ψ', p, .untl AB.1 AB.2) = ψ
        have hroundtrip := abstract_subst_roundtrip ψ AB.1 AB.2 p hfresh
        -- ψ ≡ subst(psi, p, .untl AB.1 AB.2)
        have hphi_equiv : int_equiv ψ (subst_formula psi p (.untl AB.1 AB.2)) := by
          rw [← hroundtrip]; exact subst_formula_congr hpsi_equiv p (.untl AB.1 AB.2)
        -- Back-substitution via subst_in_separated_separable_jd with oracle
        -- Callback formulas always have JD ≤ 1 (via callback_jd_le_one)
        have h_subst_sep : is_separable (subst_formula psi p (.untl AB.1 AB.2)) :=
          subst_in_separated_separable_jd psi p AB.1 AB.2
            hAB_sf.1 hAB_sf.2 hpsi_sep oracle
        exact is_separable_of_equiv hphi_equiv h_subst_sep
  exact outer (U_nesting_depth phi) phi (Nat.le_refl _) hns

/-- GHR94 Lemmas 10.2.6 + 10.2.7 (oracle-free):
    A formula with no_S_nested_in_U is separable.
    No oracle parameter, no axiom-backed functions.
    Proved by double strong induction on (U_nesting_depth, count_U_total). -/
theorem no_S_nested_sep (phi : Formula Atom) (hns : no_S_nested_in_U phi) :
    is_separable phi := by
  -- Double strong induction: outer on U_nesting_depth, inner on count_U_total
  have proof : ∀ (d c : Nat) (ψ : Formula Atom), U_nesting_depth ψ ≤ d →
      count_U_total ψ ≤ c → no_S_nested_in_U ψ → is_separable ψ := by
    intro d
    induction d using Nat.strongRecOn with | ind d ih_d =>
    intro c
    induction c using Nat.strongRecOn with | ind c ih_c =>
    intro ψ hd hc hns_ψ
    -- Base: U-free
    by_cases huf : is_U_free ψ = true
    · exact separated_imp_separable ψ
        (restricted_u_free_separated ψ (has_no_allpast_allfuture_true ψ) huf)
    · push_neg at huf; simp only [Bool.not_eq_true] at huf
      have huf' : is_U_free ψ = false := huf
      -- Case split on U_nesting_depth
      by_cases hd_ge2 : d ≥ 2
      · -- UND >= 2: extract innermost U-type (U-free args)
        let AB := extract_innermost_U_type ψ huf' hns_ψ
        have hAB_sf := extract_innermost_U_type_S_free ψ huf' hns_ψ
        have hAB_uf := extract_innermost_U_type_U_free ψ huf' hns_ψ
        let p := fresh_atom ψ
        have hfresh := fresh_atom_not_in ψ
        let ψ' := abstract_untl ψ AB.1 AB.2 p
        have hcontains := extract_innermost_U_type_contains_deep ψ huf' hns_ψ
        have hcount_lt : count_U_total ψ' < count_U_total ψ :=
          abstract_untl_count_total_lt_of_contains_deep ψ AB.1 AB.2 p hcontains
        have hns' := abstract_untl_preserves_no_S_nested ψ AB.1 AB.2 p hns_ψ
        -- ψ' separable by inner IH (same d, smaller count_U_total)
        have h_und_le : U_nesting_depth ψ' ≤ d :=
          Nat.le_trans (abstract_untl_U_nesting_depth_le ψ AB.1 AB.2 p) hd
        have h_psi'_sep : is_separable ψ' :=
          ih_c (count_U_total ψ') (by omega) ψ' h_und_le (le_refl _) hns'
        obtain ⟨psi, hpsi_sep, hpsi_equiv⟩ := h_psi'_sep
        have hroundtrip := abstract_subst_roundtrip ψ AB.1 AB.2 p hfresh
        have hphi_equiv : int_equiv ψ (subst_formula psi p (.untl AB.1 AB.2)) := by
          rw [← hroundtrip]; exact subst_formula_congr hpsi_equiv p (.untl AB.1 AB.2)
        -- Substitute back: callbacks have UND <= 1, so outer IH handles them
        have h_subst_sep : is_separable (subst_formula psi p (.untl AB.1 AB.2)) :=
          subst_in_separated_separable_depth psi p AB.1 AB.2
            hAB_sf.1 hAB_sf.2 hAB_uf.1 hAB_uf.2 hpsi_sep
            (fun chi hns_chi hund_chi =>
              -- chi has no_S_nested_in_U, UND <= 1
              -- Since d >= 2 and UND chi <= 1, outer IH at d' = 1 < d
              ih_d 1 (by omega) (count_U_total chi) chi hund_chi (le_refl _) hns_chi)
        exact is_separable_of_equiv hphi_equiv h_subst_sep
      · -- UND <= 1: use oracle-free lemma_10_2_6_no_oracle
        push_neg at hd_ge2
        exact lemma_10_2_6_no_oracle ψ hns_ψ (by omega)
  exact proof (U_nesting_depth phi) (count_U_total phi) phi (le_refl _) (le_refl _) hns

/-- Version of `no_S_nested_in_U_separable_param` with JD-bounded callback. -/
theorem no_S_nested_in_U_separable_param_jd (phi : Formula Atom)
    (hns : no_S_nested_in_U phi)
    (hexp : has_no_allpast_allfuture phi = true)
    (callback : ∀ (χ : Formula Atom), no_S_nested_in_U χ → junction_depth χ ≤ 1 → is_separable χ) :
    is_separable phi := by
  -- Strong induction on count_U_subformulas
  induction h : count_U_subformulas phi using Nat.strongRecOn generalizing phi with
  | ind n ih =>
  -- Case n = 0: U-free, syntactically separated
  by_cases huf : is_U_free phi = true
  · exact separated_imp_separable phi (restricted_u_free_separated phi hexp huf)
  · -- Case n > 0: extract U-type and abstract
    push_neg at huf; simp [Bool.not_eq_true] at huf
    have huf' : is_U_free phi = false := huf
    let AB := extract_U_type phi huf' hns
    have hAB_sf := extract_U_type_S_free phi huf' hns
    let p := fresh_atom phi
    have hfresh := fresh_atom_not_in phi
    let phi' := abstract_untl phi AB.1 AB.2 p
    have hcontains := extract_U_type_contains_surface phi huf' hns
    have hcount_lt : count_U_subformulas phi' < count_U_subformulas phi :=
      abstract_untl_count_lt_of_contains_surface phi AB.1 AB.2 p hcontains
    have hns' : no_S_nested_in_U phi' :=
      abstract_untl_preserves_no_S_nested phi AB.1 AB.2 p hns
    have hexp' : has_no_allpast_allfuture phi' = true :=
      abstract_untl_preserves_no_allpast_allfuture phi AB.1 AB.2 p hexp
    -- phi' is separable by IH (strictly fewer U-subformulas)
    have h_phi'_sep : is_separable phi' := by
      exact ih (count_U_subformulas phi') (h ▸ hcount_lt) phi' hns' hexp' rfl
    -- Get separated psi equivalent to phi'
    obtain ⟨psi, hpsi_sep, hpsi_equiv⟩ := h_phi'_sep
    -- phi = subst(phi', p, U(A,B)) by syntactic roundtrip
    have hroundtrip : subst_formula phi' p (.untl AB.1 AB.2) = phi :=
      abstract_subst_roundtrip phi AB.1 AB.2 p hfresh
    -- phi is equiv to subst(psi, p, U(A,B)) by congruence
    have hphi_equiv : int_equiv phi (subst_formula psi p (.untl AB.1 AB.2)) := by
      rw [← hroundtrip]
      exact subst_formula_congr hpsi_equiv p (.untl AB.1 AB.2)
    -- subst(psi, p, U(A,B)) is separable via constituent substitution with JD-bounded callback
    have h_subst_sep : is_separable (subst_formula psi p (.untl AB.1 AB.2)) :=
      subst_in_separated_separable_jd psi p AB.1 AB.2
        hAB_sf.1 hAB_sf.2 hpsi_sep callback
    exact is_separable_of_equiv hphi_equiv h_subst_sep

/-- Main hierarchy theorem: every expanded formula is separable.
    Proved by strong induction on junction_depth. The `.snce` case reduces to separated
    forms of sub-formulas, which satisfy `no_S_nested_in_U` and have JD ≤ 1.
    For JD ≥ 2, the JD induction hypothesis serves as the callback for
    `no_S_nested_in_U_separable_param` (callback formulas have JD ≤ 1 < JD).
    For JD ≤ 1, `no_S_nested_in_U_separable_param` is applied with the JD = 0
    base case as callback (JD = 0 formulas are separated, so no further callbacks).
    The `.untl` case follows by temporal duality.

    GHR94 Lemma 10.2.8 + Theorem 10.2.9 (specialized to integer time). -/
theorem all_formulas_separable_aux (φ : Formula Atom)
    (hexp : has_no_allpast_allfuture φ = true) : is_separable φ := by
  -- Strong induction on junction_depth, with structural sub-induction for same-JD cases.
  -- We use (junction_depth, sizeOf) lexicographic well-founded induction.
  have : ∀ (n : Nat) (ψ : Formula Atom), junction_depth ψ ≤ n →
      has_no_allpast_allfuture ψ = true → is_separable ψ := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih_jd =>
    intro ψ hjd hψ_exp
    -- Within each JD level, use structural induction on ψ
    induction ψ with
    | atom a => exact ⟨.atom a, rfl, int_equiv_refl _⟩
    | bot => exact ⟨.bot, rfl, int_equiv_refl _⟩
    | box ψ => exact ⟨.box ψ, rfl, int_equiv_refl _⟩
    | imp a b ih_a ih_b =>
      have hle_a : junction_depth a ≤ n := Nat.le_trans (jd_imp_le_left a b) hjd
      have hle_b : junction_depth b ≤ n := Nat.le_trans (jd_imp_le_right a b) hjd
      exact imp_separable (ih_a hle_a (has_no_allpast_allfuture_true a))
                          (ih_b hle_b (has_no_allpast_allfuture_true b))
    | snce a b ih_a ih_b =>
      -- Sub-formulas a, b have JD ≤ n (same level), but are structurally smaller
      have hle_a : junction_depth a ≤ n := Nat.le_trans (jd_snce_le_left a b) hjd
      have hle_b : junction_depth b ≤ n := Nat.le_trans (jd_snce_le_right a b) hjd
      -- Quick exit: JD = 0 means formula is directly separated
      by_cases hjd0 : junction_depth (.snce a b) = 0
      · exact jd_zero_sep (.snce a b) hψ_exp hjd0
      · -- JD ≥ 1: need the full separation/box-normalization path
        -- Step 1: By structural IH at same JD level, a and b are separable.
        have ha := ih_a hle_a (has_no_allpast_allfuture_true a)
        have hb := ih_b hle_b (has_no_allpast_allfuture_true b)
        -- Step 2: Get separated forms ψa ≡ a, ψb ≡ b.
        obtain ⟨ψa, hψa_sep, hψa_equiv⟩ := ha
        obtain ⟨ψb, hψb_sep, hψb_equiv⟩ := hb
        -- Step 3: Box-normalize.
        let χa := replace_box_with_top ψa
        let χb := replace_box_with_top ψb
        -- Step 4: Build equivalence chain: .snce a b ≡ .snce χa χb
        have hequiv : int_equiv (.snce a b) (.snce χa χb) :=
          int_equiv_trans (snce_congr hψa_equiv hψb_equiv)
            (snce_congr (replace_box_equiv ψa) (replace_box_equiv ψb))
        -- Step 5: .snce χa χb has no_S_nested_in_U
        have hns : no_S_nested_in_U (.snce χa χb) :=
          snce_of_boxfree_sep_no_S_nested ψa ψb hψa_sep hψb_sep
        -- Step 6: .snce χa χb has JD ≤ 1
        have hjd_le_one : junction_depth (.snce χa χb) ≤ 1 :=
          snce_of_boxfree_sep_jd_le_one ψa ψb hψa_sep hψb_sep
        -- Step 7: Apply no_S_nested_in_U_separable_direct_param with oracle from JD IH.
        -- Oracle formulas have JD ≤ 1, so we need 1 < n.
        -- Since JD(.snce a b) ≥ 1 (quick exit handled JD = 0) and JD(.snce a b) ≤ n,
        -- we have n ≥ 1. For n = 1, the oracle may receive JD = 1 formulas.
        -- We handle this by using no_S_nested_in_U_separable_param_jd which
        -- threads the callback through its own count_U_subformulas induction.
        -- The callback feeds back to the JD IH: oracle formulas at JD ≤ 1 need
        -- the result at level ≤ 1 < n when n ≥ 2.
        -- For n ≥ 2: direct oracle from ih_jd.
        -- For n = 1: oracle feeds to ih_jd at level 0, handling JD = 0.
        --   JD = 1 callback formulas are handled by the n = 1 proof itself via
        --   the structural induction: the callback formula is generated internally
        --   by no_S_nested_in_U_separable_param_jd's own count induction.
        have h_sep : is_separable (.snce χa χb) := by
          by_cases hn2 : n ≥ 2
          · -- n ≥ 2: oracle from JD IH (oracle formulas have JD ≤ 1 < 2 ≤ n)
            exact no_S_nested_in_U_separable_direct_param (.snce χa χb) hns
              (fun chi hns_chi hjd_chi =>
                ih_jd (junction_depth chi) (by omega) chi
                  (le_refl _) (has_no_allpast_allfuture_true chi))
          · -- n = 1: use oracle-free no_S_nested_sep
            exact no_S_nested_sep (.snce χa χb) hns
        exact is_separable_of_equiv hequiv h_sep
    | untl a b ih_a ih_b =>
      -- Sub-formulas have JD ≤ n
      have hle_a : junction_depth a ≤ n := Nat.le_trans (jd_untl_le_left a b) hjd
      have hle_b : junction_depth b ≤ n := Nat.le_trans (jd_untl_le_right a b) hjd
      -- Quick exit: JD = 0 means formula is directly separated
      by_cases hjd0 : junction_depth (.untl a b) = 0
      · exact jd_zero_sep (.untl a b) hψ_exp hjd0
      · -- JD ≥ 1: need full path
        -- Step 1: By structural IH, a and b are separable.
        have ha := ih_a hle_a (has_no_allpast_allfuture_true a)
        have hb := ih_b hle_b (has_no_allpast_allfuture_true b)
        obtain ⟨ψa, hψa_sep, hψa_equiv⟩ := ha
        obtain ⟨ψb, hψb_sep, hψb_equiv⟩ := hb
        -- Step 2: Box-normalize.
        let χa := replace_box_with_top ψa
        let χb := replace_box_with_top ψb
        -- Step 3: .untl χa χb has no_U_nested_in_S
        have hns_U : no_U_nested_in_S (.untl χa χb) :=
          untl_of_boxfree_sep_no_U_nested ψa ψb hψa_sep hψb_sep
        -- Step 4: swap(.untl χa χb) has no_S_nested_in_U
        have hns_S : no_S_nested_in_U (Formula.swapTemporal (.untl χa χb)) :=
          swap_no_U_nested_gives_no_S_nested (.untl χa χb) hns_U
        -- Step 5: swap is separable.
        -- For n ≥ 2: use _param variant with oracle from JD IH.
        -- For n = 1: fall back to existing path.
        have h_swap_sep : is_separable (Formula.swapTemporal (.untl χa χb)) := by
          have hn_pos : n ≥ 1 := by
            have : junction_depth (.untl a b) ≥ 1 := by omega
            omega
          by_cases hn2 : n ≥ 2
          · exact no_S_nested_in_U_separable_direct_param _ hns_S
              (fun chi hns_chi hjd_chi =>
                ih_jd (junction_depth chi) (by omega) chi
                  (le_refl _) (has_no_allpast_allfuture_true chi))
          · exact no_S_nested_sep _ hns_S
        -- Step 7: dual_separable
        have h_untl_sep : is_separable (.untl χa χb) := by
          have h := dual_separable _ h_swap_sep
          rw [Formula.swapTemporal_involution] at h
          exact h
        -- Step 8: Build equivalence chain
        have hequiv : int_equiv (.untl a b) (.untl χa χb) :=
          int_equiv_trans (untl_congr hψa_equiv hψb_equiv)
            (untl_congr (replace_box_equiv ψa) (replace_box_equiv ψb))
        exact is_separable_of_equiv hequiv h_untl_sep
  exact this (junction_depth φ) φ (Nat.le_refl _) hexp

/-- Every formula is separable (GHR94 Theorem 10.2.9 for integer time).
    Proved by expanding temporal operators and applying the hierarchy theorem. -/
theorem all_formulas_separable (φ : Formula Atom) : is_separable φ :=
  is_separable_of_equiv (expand_temporal_equiv φ)
    (all_formulas_separable_aux (expand_temporal φ) (by simp [expand_temporal_id, has_no_allpast_allfuture_true]))


end Cslib.Logic.Bimodal.Metalogic.Separation
