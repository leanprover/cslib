/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

import Cslib.Languages.LambdaCalculus.Named.Untyped.Properties
import Cslib.Languages.LambdaCalculus.Named.Untyped.SwapProperties

/-! # Equivalence of α-equivalence definitions

Theorems showing equivalence of multiple α-equivalence.

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012]
-/

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.Named.Untyped.Term

/-
  Non-occurrence implies freshness.
-/
omit [HasFresh Var] in
lemma alphaEquiv_of_alphaEquivPFresh {m n : Term Var} : AlphaEquiv m n → AlphaEquivPFresh m n := by
  intro h
  induction h with
  | var => constructor
  | abs z_h1 ih1 ih2 =>
    rename_i x z x1 x2 m1 m2
    have h1 : z ∉ ({x1, x2} : Finset Var) ∪ m1.fv ∪ m2.fv := by
      rw [vars_either_fv_or_bv] at z_h1
      rw [vars_either_fv_or_bv] at z_h1
      simp_all
    have h2 : AlphaEquivPFresh (m1.swap x1 z) (m2.swap x2 z) := by
      grind [swap_eq_rename_of_not_mem_vars]
    apply AlphaEquivPFresh.abs h1 h2
  | app h1 h2 ih1 ih2 => exact AlphaEquivPFresh.app ih1 ih2

lemma alphaEquivPFresh_of_alphaEquiv {m n : Term Var} : AlphaEquivPFresh m n → AlphaEquiv m n := by
  intro h
  induction h with
  | var => constructor
  | abs hy h ih =>
    rename_i u a b E E'
    have h1 : u ∉ E.fv := by aesop
    have h2 : u ∉ E'.fv := by aesop
    -- TODO do this whole proof via Lemma 6.2 using the agreement set (AS) argumentation

    -- TODO how to formalize the "pick any z ≠ u"

    obtain ⟨m1', hm1', hm1''⟩ := exists_alphaEquiv_not_mem_vars h1
    obtain ⟨m2', hm2', hm2''⟩ := exists_alphaEquiv_not_mem_vars h2

    have h_swap_preserve :
      (E.swap a u).AlphaEquiv (m1'.swap a u) ∧ (E'.swap b u).AlphaEquiv (m2'.swap b u) := by
      exact ⟨AlphaEquiv.swap_preserve hm1', AlphaEquiv.swap_preserve hm2'⟩;

    have h_trans : (m1'.rename a u).AlphaEquiv (m2'.rename b u) := by
      rw [← swap_eq_rename_of_not_mem_vars hm1'']
      rw [← swap_eq_rename_of_not_mem_vars hm2'']
      exact AlphaEquiv.trans
        ( AlphaEquiv.symm h_swap_preserve.1 ) ( AlphaEquiv.trans ih h_swap_preserve.2 );

    have h_abs1 : (abs a m1').AlphaEquiv (abs b m2') := by
      apply_rules [ AlphaEquiv.abs ];
      grind [AlphaEquiv.trans];
    have h_abs2 : (abs a E).AlphaEquiv (abs a m1') ∧ (abs b m2').AlphaEquiv (abs b E') := by
      exact ⟨
        AlphaEquiv.context ( c := Context.abs a Context.hole ) hm1',
        AlphaEquiv.context ( c := Context.abs b Context.hole ) hm2'.symm
      ⟩;
    exact AlphaEquiv.trans h_abs2.1 ( AlphaEquiv.trans h_abs1 h_abs2.2 );
  | app _ _ ih1 ih2 => exact AlphaEquiv.app ih1 ih2

/-! See [Crole2012] Theorem 4.1 -/
theorem alphaEquiv_iff_alphaEquivPFresh (m n : Term Var) : AlphaEquiv m n ↔ AlphaEquivPFresh m n :=
  ⟨alphaEquiv_of_alphaEquivPFresh, alphaEquivPFresh_of_alphaEquiv⟩

/-! See [Crole2012] Theorem 4.2 -/
theorem alphaEquiv_iff_alphaEquivP1 (m n : Term Var) :
    AlphaEquiv m n ↔ AlphaEquivP1 m n := by
  sorry

/-! See [Crole2012] Theorem 4.4 -/
theorem alphaEquiv_iff_alphaEquivR (m n : Term Var) :
    AlphaEquiv m n ↔ AlphaEquivR m n := by
  sorry

/-! See [Crole2012] Theorem 4.5 -/
theorem alphaEquiv_iff_alphaEquivRFresh (m n : Term Var) :
    AlphaEquiv m n ↔ AlphaEquivRFresh m n := by
  sorry

/-! See [Crole2012] Theorem 4.6 -/
theorem alphaEquivR_iff_alphaEquivRFresh (m n : Term Var) :
    AlphaEquivR m n ↔ AlphaEquivRFresh m n := by
  sorry

end LambdaCalculus.Named.Untyped.Term

end Cslib
