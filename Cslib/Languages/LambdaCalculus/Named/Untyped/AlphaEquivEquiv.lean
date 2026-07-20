/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Properties
public import Cslib.Languages.LambdaCalculus.Named.Untyped.SwapProperties

/-! # Equivalence of α-equivalence definitions

Theorems showing equivalence of the five definitions of α-equivalence from [Crole2012]:

* `∼p`  (Definition 3.1): permutation with non-occurrence side condition (`AlphaEquiv`)
* `∼p#` (Definition 3.2): permutation with freshness side condition (`AlphaEquivPFresh`)
* `∼¹p` (Definition 3.3): permutation with non-occurrence on bodies only (`AlphaEquivP1`)
* `∼r`  (Definition 3.4): traditional renaming axiom with non-occurrence (`AlphaEquivR`)
* `∼r#` (Definition 3.5): renaming axiom with freshness (`AlphaEquivRFresh`)

The main results are:

* **Theorem 4.1** [Crole2012]: `∼p = ∼p#` (`alphaEquiv_iff_alphaEquivPFresh`)
* **Theorem 4.2** [Crole2012]: `∼p = ∼¹p` (`alphaEquiv_iff_alphaEquivP1`)
* **Theorem 4.4** [Crole2012]: `∼p = ∼r`  (`alphaEquiv_iff_alphaEquivR`)
* **Theorem 4.5** [Crole2012]: `∼p = ∼r#` (`alphaEquiv_iff_alphaEquivRFresh`)
* **Theorem 4.6** [Crole2012]: `∼r = ∼r#` (`alphaEquivR_iff_alphaEquivRFresh`)

## References

* [Roy L. Crole, *Alpha equivalence equalities*][Crole2012]
-/

@[expose] public section

namespace Cslib

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.Named.Untyped.Term

/-! ## Direction ∼p → ∼p#

Non-occurrence (`y ∉ vars(m)`) obviously implies freshness (`y ∉ fv(m)`), and the `swap`
operation coincides with `rename` when the target variable does not occur in the term.

See [Crole2012] proof of Theorem 4.1, first sentence: "It is trivial that ∼p is contained in ∼p#."
-/
omit [HasFresh Var] in
lemma alphaEquiv_of_alphaEquivPFresh {m n : Term Var} :
   AlphaEquiv m n → AlphaEquivPFresh m n := by
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

/-! ## Direction ∼p# → ∼p (the interesting direction of Theorem 4.1) -/
lemma alphaEquivPFresh_of_alphaEquiv {m n : Term Var} :
    AlphaEquivPFresh m n → AlphaEquiv m n := by
  intro h
  induction h with
  | var => constructor
  | abs hy _h ih =>
    rename_i u a b E E'
    -- We have: (u a) · E ∼p (u b) · E' (by induction: ih) and u # a, b, E, E' (by hy).
    -- Extract freshness conditions from hy.
    have hu_a : u ≠ a := by aesop
    have hu_b : u ≠ b := by aesop
    have hu_E : u ∉ E.fv := by aesop
    have hu_E' : u ∉ E'.fv := by aesop
    -- Pick z ≠ u with z ∉ vars(E) ∪ vars(E') ∪ {a, b} (stronger than freshness).
    obtain ⟨z, hz⟩ : ∃ z : Var, z ∉ E.vars ∪ E'.vars ∪ {a, b, u} := by
      exact Infinite.exists_notMem_finset (E.vars ∪ E'.vars ∪ {a, b, u})
    have hz_a : z ≠ a := by aesop
    have hz_b : z ≠ b := by aesop
    have hz_u : z ≠ u := by aesop
    have hz_E : z ∉ E.vars := by aesop
    have hz_E' : z ∉ E'.vars := by aesop
    have hz_fv_E : z ∉ E.fv := by
      have : E.vars = E.fv ∪ E.bv := vars_either_fv_or_bv
      aesop
    have hz_fv_E' : z ∉ E'.fv := by
      have : E'.vars = E'.fv ∪ E'.bv := vars_either_fv_or_bv
      aesop
    -- Using Lemma 6.1 we get
    have h_swap : ((E.swap u a).swap z u) =α ((E'.swap u b).swap z u) := by
      rw [@swap_comm (x := u) (y := a), swap_comm (x := u) (y := b)]
      exact AlphaEquiv.swap_preserve ih
    -- From Lemma 6.2 part 2 via agreement sets
    have h_agree_E : ((E.swap u a).swap z u) =α (E.swap z a) :=
      swap_comp_alphaEquiv_of_not_mem_fv hu_E hz_fv_E
    have h_agree_E' : ((E'.swap u b).swap z u) =α (E'.swap z b) :=
      swap_comp_alphaEquiv_of_not_mem_fv hu_E' hz_fv_E'
    -- Chain by symmetry and transitivity of ∼p
    -- (z a) · E ∼p (z u)·(u a)·E ∼p (z u)·(u b)·E' ∼p (z b) · E'
    have h_chain : (E.swap z a) =α (E'.swap z b) :=
      AlphaEquiv.trans (AlphaEquiv.symm h_agree_E) (AlphaEquiv.trans h_swap h_agree_E')
    -- Convert swap to rename (since z ∉ vars) and apply the pi rule.
    -- Since z ∉ vars(E), swap z a = rename a z (by swap_comm + swap_eq_rename).
    rw [swap_comm, swap_eq_rename_of_not_mem_vars hz_E] at h_chain
    rw [swap_comm, swap_eq_rename_of_not_mem_vars hz_E'] at h_chain
    exact AlphaEquiv.abs (by aesop) h_chain
  | app _ _ ih1 ih2 => exact AlphaEquiv.app ih1 ih2

/-! ## Theorem 4.1 [Crole2012] -/
theorem alphaEquiv_iff_alphaEquivPFresh (m n : Term Var) :
    AlphaEquiv m n ↔ AlphaEquivPFresh m n :=
  ⟨alphaEquiv_of_alphaEquivPFresh, alphaEquivPFresh_of_alphaEquiv⟩

/-
/-! ## Theorem 4.2 [Crole2012] -/
theorem alphaEquiv_iff_alphaEquivP1 (m n : Term Var) :
    AlphaEquiv m n ↔ AlphaEquivP1 m n := by
  sorry

/-! ## Theorem 4.4 [Crole2012] -/
theorem alphaEquiv_iff_alphaEquivR (m n : Term Var) :
    AlphaEquiv m n ↔ AlphaEquivR m n := by
  sorry

/-! ## Theorem 4.5 [Crole2012] -/
theorem alphaEquiv_iff_alphaEquivRFresh (m n : Term Var) :
    AlphaEquiv m n ↔ AlphaEquivRFresh m n := by
  sorry

/-! ## Theorem 4.6 [Crole2012] -/
theorem alphaEquivR_iff_alphaEquivRFresh (m n : Term Var) :
    AlphaEquivR m n ↔ AlphaEquivRFresh m n := by
  sorry
-/

end LambdaCalculus.Named.Untyped.Term

end Cslib
