module

public import Cslib.Foundations.Data.Relation
public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasSubstitution
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.Basic
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.StrongNorm


@[expose] public section

namespace Cslib

universe u v


namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u} {Base : Type v} [DecidableEq Var] [HasFresh Var]


abbrev Environment (Var : Type u) := Context Var (Term Var)

def multiSubst (σ : Environment Var) (M : Term Var) : Term Var :=
  match σ with
  | [] => M
  | ⟨ i, sub ⟩ :: σ' => (multiSubst σ' M) [ i := sub ]

def Environment.fv (Ns : Environment Var) : Finset Var :=
  match Ns with
  | [] => {}
  | ⟨ _, sub ⟩ :: Ns' => sub.fv ∪ fv Ns'


@[simp]
def env_LC (Γ : Environment Var) : Prop :=
  ∀ {x M}, ⟨ x, M ⟩ ∈ Γ → LC M

lemma env_LC_cons {Γ : Environment Var} {x : Var} {sub : Term Var}
  (lc_sub : LC sub)
  (lc_Γ : env_LC Γ)
  : env_LC (⟨ x, sub ⟩ :: Γ) := by
  intro y M h_mem
  cases h_mem <;> aesop



def multiSubst_fvar_fresh (Ns : Environment Var) :
  ∀ x ∉ Ns.dom, multiSubst Ns (Term.fvar x) = Term.fvar x := by
  induction Ns <;> intro x h_fresh
  · case nil =>
      simp [multiSubst]
  · case cons N Ns ih =>
      simp only [multiSubst]
      simp only [Context.dom] at h_fresh
      rw[ih]
      · rw[subst_fvar]
        by_cases h : N.1 = x <;> simp_all
      · simp_all

lemma multiSubst_preserves_not_fvar {x : Var}
  (M : Term Var)
  (Ns : Environment Var)
  (nmem : x ∉ M.fv ∪ Ns.fv) :
  x ∉ (multiSubst Ns M).fv := by
  induction Ns
  · case nil =>
      rw[multiSubst]
      simp_all
  · case cons N Ns ih =>
      rw[multiSubst]
      apply subst_preserve_not_fvar
      rw[Environment.fv] at nmem
      simp_all

def multiSubst_app (M N : Term Var) (Ps : Environment Var) :
        multiSubst Ps (Term.app M N) = Term.app (multiSubst Ps M) (multiSubst Ps N) := by
  induction Ps
  · rfl
  · case cons N Ns ih => rw[multiSubst, multiSubst, ih]; rfl

def multiSubst_abs (M : Term Var) (Ns : Environment Var) :
    multiSubst Ns (Term.abs M) =
    Term.abs (multiSubst Ns M) := by
  induction Ns
  · rfl
  · case cons N Ns ih => rw[multiSubst, ih]; rfl

lemma open'_fvar_subst (M N : Term Var) (x : Var) (H : x ∉ Term.fv M) :
  (i : Nat) → (M ⟦ i ↝ Term.fvar x ⟧) [x := N] = M ⟦ i ↝ N ⟧ := by
  induction M <;> intro i
  · case bvar j =>
      rw[Term.openRec_bvar, Term.openRec_bvar]
      by_cases h : i = j <;> simp[h, Term.subst_fvar, Term.subst_bvar]
  · case fvar y =>
      rw[Term.openRec_fvar, Term.openRec_fvar]
      simp only [Term.fv, Finset.mem_singleton] at H
      simp only [subst_fvar, ite_eq_right_iff]
      intro H
      contradiction
  · case abs M ih =>
      rw[Term.openRec_abs, Term.openRec_abs]
      rw[Term.subst_abs]
      rw[ih H]
  · case app l r ih_l ih_r =>
      rw[Term.openRec_app, Term.openRec_app]
      rw[Term.subst_app]
      simp only [Term.fv, Finset.mem_union, not_or] at H
      rw[ih_l H.1]
      rw[ih_r H.2]

lemma multiSubst_open_var (M : Term Var) (Ns : Environment Var) (x : Var) :
  x ∉ Ns.dom →
  env_LC Ns →
  (multiSubst Ns (M ^ (Term.fvar x))) =
  (multiSubst Ns M) ^ (Term.fvar x) := by
  intro h_ndom h_lc
  induction Ns with
  | nil => rfl
  | cons N Ns ih =>
    rw[multiSubst, multiSubst]
    rw[ih]
    · rw[subst_open_var] <;> aesop
    · simp_all
    aesop

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
