/-
Copyright (c) 2026 Chris Anto Fröschl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Anto Fröschl
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Basic
public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivVariants.Defs
public import Cslib.Languages.LambdaCalculus.Named.Untyped.RenameProperties
public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivProperties
public import Cslib.Languages.LambdaCalculus.Named.Untyped.AlphaEquivVariants.Swap

/-! # Equivalence of α-equivalence definitions

Theorems showing equivalence of the five definitions of α-equivalence from [Crole2012]:

* `∼p`  (Definition 3.1): permutation with non-occurrence side condition (`AlphaEquiv`)
* `∼p#` (Definition 3.2): permutation with freshness side condition (`AlphaEquivPFresh`)
* `∼¹p` (Definition 3.3): permutation with non-occurrence on bodies only (`AlphaEquivP1`)
* `∼r`  (Definition 3.4): traditional renaming axiom with non-occurrence (`AlphaEquivR`)
* `∼r#` (Definition 3.5): renaming axiom with freshness (`AlphaEquivRFresh`)

Theorem 4.1 is proved in this file. The remaining results are stated as `theorem_wanted`:

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

omit [HasFresh Var] in
/-- Non-occurrence obviously implies freshness, and the `swap` operation coincides with
`rename` when the target variable does not occur in the term. -/
lemma alphaEquivPFresh_of_alphaEquiv {m n : Term Var} (h : m =α n) : AlphaEquivPFresh m n := by
  induction h with
  | var => constructor
  | @abs z x1 x2 m1 m2 hz _ ih =>
    have h1 : z ∉ ({x1, x2} : Finset Var) ∪ m1.fv ∪ m2.fv := by
      simp_all [vars_eq_fv_union_bv]
    have h2 : AlphaEquivPFresh (m1.swap x1 z) (m2.swap x2 z) := by
      grind [swap_eq_rename_of_notMem_vars]
    apply AlphaEquivPFresh.abs h1 h2
  | app h1 h2 ih1 ih2 => exact AlphaEquivPFresh.app ih1 ih2

/-- The converse direction: the freshness witness `u` of the rule `pi#` is exchanged for an atom
`z` that does not occur at all, using Lemma 6.1 and Lemma 6.2 part 2 [Crole2012]. -/
lemma alphaEquiv_of_alphaEquivPFresh {m n : Term Var} (h : AlphaEquivPFresh m n) : m =α n := by
  induction h with
  | var => constructor
  | @abs u a b m m' hy _ ih =>
    -- We have: (u a) · m ∼p (u b) · m' (by induction: ih) and u # a, b, m, m' (by hy).
    -- Pick z ≠ u with z ∉ vars(m) ∪ vars(m') ∪ {a, b} (stronger than freshness).
    obtain ⟨z, hz⟩ := fresh_exists (m.vars ∪ m'.vars ∪ {a, b, u})
    have hzm : z ∉ m.vars := by grind
    have hzm' : z ∉ m'.vars := by grind
    -- Using Lemma 6.1 we get
    have h_swap : ((m.swap u a).swap z u) =α ((m'.swap u b).swap z u) := by
      nth_rw 2 [swap_comm]
      nth_rw 4 [swap_comm]
      exact AlphaEquiv.swap_preserve ih
    -- From Lemma 6.2 part 2 via agreement sets
    have h_agree : ((m.swap u a).swap z u) =α (m.swap z a) := by
      apply swap_comp_alphaEquiv_of_notMem_fv <;> grind [vars_eq_fv_union_bv]
    have h_agree' : ((m'.swap u b).swap z u) =α (m'.swap z b) := by
      apply swap_comp_alphaEquiv_of_notMem_fv <;> grind [vars_eq_fv_union_bv]
    -- Chain by symmetry and transitivity of ∼p
    -- (z a) · m ∼p (z u)·(u a)·m ∼p (z u)·(u b)·m' ∼p (z b) · m'
    have h_chain : (m.swap z a) =α (m'.swap z b) := h_agree.symm.trans (h_swap.trans h_agree')
    -- Convert swap to rename (since z ∉ vars) and apply the pi rule.
    -- Since z ∉ vars(m), swap z a = rename a z (by swap_comm + swap_eq_rename).
    rw [swap_comm, swap_eq_rename_of_notMem_vars hzm] at h_chain
    rw [swap_comm, swap_eq_rename_of_notMem_vars hzm'] at h_chain
    exact AlphaEquiv.abs (by grind) h_chain
  | app _ _ ih1 ih2 => exact AlphaEquiv.app ih1 ih2

/-- **Theorem 4.1** [Crole2012]: `∼p` and `∼p#` are the same relation. -/
theorem alphaEquiv_iff_alphaEquivPFresh (m n : Term Var) : m =α n ↔ AlphaEquivPFresh m n :=
  ⟨alphaEquivPFresh_of_alphaEquiv, alphaEquiv_of_alphaEquivPFresh⟩

/-- **Theorem 4.2** [Crole2012]: `∼p` and `∼¹p` are the same relation. -/
theorem_wanted alphaEquiv_iff_alphaEquivP1 (m n : Term Var) : m =α n ↔ AlphaEquivP1 m n

/-- **Theorem 4.4** [Crole2012]: `∼p` and `∼r` are the same relation. -/
theorem_wanted alphaEquiv_iff_alphaEquivR (m n : Term Var) : m =α n ↔ AlphaEquivR m n

/-- **Theorem 4.5** [Crole2012]: `∼p` and `∼r#` are the same relation. -/
theorem_wanted alphaEquiv_iff_alphaEquivRFresh (m n : Term Var) : m =α n ↔ AlphaEquivRFresh m n

/-- **Theorem 4.6** [Crole2012]: `∼r` and `∼r#` are the same relation. -/
theorem_wanted alphaEquivR_iff_alphaEquivRFresh (m n : Term Var) :
    AlphaEquivR m n ↔ AlphaEquivRFresh m n :=
  (❰alphaEquiv_iff_alphaEquivR❱ m n).symm.trans (❰alphaEquiv_iff_alphaEquivRFresh❱ m n)

end LambdaCalculus.Named.Untyped.Term

end Cslib
