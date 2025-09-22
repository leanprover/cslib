/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Opening

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines the well-formedness condition for types and contexts.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Fsub

open scoped Ty in
/-- A type is well-formed when it is locally closed and all free variables appear in a context. -/
inductive Ty.Wf : Env Var → Ty Var → Prop
  | top : Ty.Wf Γ top
  | var : Binding.sub σ ∈ Γ.dlookup X → Ty.Wf Γ (fvar X)
  | arrow : Ty.Wf Γ σ → Ty.Wf Γ τ → Ty.Wf Γ (arrow σ τ)
  | all (L : Finset Var) : 
      Ty.Wf Γ σ →
      (∀ X ∉ L, Ty.Wf (⟨X,Binding.sub σ⟩ :: Γ) (τ ^ᵞ fvar X)) →
      Ty.Wf Γ (all σ τ)
  | sum : Ty.Wf Γ σ → Ty.Wf Γ τ → Ty.Wf Γ (sum σ τ)

attribute [scoped grind] Ty.Wf.top Ty.Wf.var Ty.Wf.arrow Ty.Wf.sum

/-- An environment is well-formed if it binds each variable exactly once to a well-formed type. -/
inductive Env.Wf : Env Var → Prop
  | empty : Wf []
  | sub : Wf Γ → τ.Wf Γ → X ∉ Γ.dom → Wf (⟨X, Binding.sub τ⟩ :: Γ)
  | ty : Wf Γ → τ.Wf Γ → x ∉ Γ.dom → Wf (⟨x, Binding.ty τ⟩ :: Γ)

attribute [scoped grind] Env.Wf.sub Env.Wf.ty

variable {Γ Δ Θ : Env Var} {σ τ τ' γ δ : Ty Var}

open scoped Context in
/-- A well-formed context contains no duplicate keys. -/
lemma Env.Wf.to_ok {Γ : Env Var} (wf : Γ.Wf) : Γ✓ := by
  induction wf <;> constructor <;> first | assumption | grind [List.mem_keys_of_mem]

namespace Ty.Wf

open Context List

/-- A well-formed type is locally closed. -/
@[grind →]
theorem lc (wf : σ.Wf Γ) : σ.LC := by
  induction wf with
  | all => apply LC.all (free_union Var) <;> grind
  | _ => grind

/-- A type remains well-formed under context permutation. -/
theorem perm_env (wf : σ.Wf Γ) (perm : Γ ~ Δ) (ok_Γ : Γ✓) (ok_Δ : Δ✓) : σ.Wf Δ := by
  induction wf generalizing Δ with
  | all => apply all (free_union [dom] Var) <;> grind [Perm.cons, nodupKeys_cons]
  | _ => grind [perm_dlookup]

-- TODO: move the simp_all into grind?
/-- A type remains well-formed under context weakening (in the middle). -/
theorem weaken (wf_ΓΘ : σ.Wf (Γ ++ Θ)) (ok_ΓΔΘ : (Γ ++ Δ ++ Θ)✓) : σ.Wf (Γ ++ Δ ++ Θ) := by
  generalize eq : Γ ++ Θ = ΓΔ at wf_ΓΘ
  induction wf_ΓΘ generalizing Γ
  case all σ _ _ _ _ _ ih => 
    apply all (free_union [Context.dom] Var) (by grind)
    intro X _
    apply ih (Γ := ⟨X, Binding.sub σ⟩ :: Γ)
    · grind
    · simp_all [haswellformed_def, keys]
    · grind
  all_goals grind [NodupKeys.sublist, sublist_dlookup]

-- TODO: remove this?
/-- A type remains well-formed under context weakening (at the front). -/
theorem weaken_head (wf : σ.Wf Δ) (ok : (Γ ++ Δ)✓) : σ.Wf (Γ ++ Δ) := by
  have : Γ ++ Δ = [] ++ Γ ++ Δ := by rfl
  grind [weaken]

/-- A type remains well-formed under context narrowing. -/
lemma narrow (wf : σ.Wf (Γ ++ ⟨X, Binding.sub τ⟩ :: Δ)) (ok : (Γ ++ ⟨X, Binding.sub τ'⟩ :: Δ)✓) :
    σ.Wf (Γ ++ ⟨X, Binding.sub τ'⟩ :: Δ) := by
  generalize eq : (Γ ++ ⟨X, Binding.sub τ⟩ :: Δ) = Θ at wf
  induction wf generalizing Γ with
  | all => apply all (free_union [dom] Var) <;> grind [nodupKeys_cons, nmem_append_keys]
  | _ => grind [sublist_dlookup, dlookup_append]

/-- A type remains well-formed under context strengthening. -/
lemma strengthen (wf : σ.Wf (Γ ++ ⟨X, Binding.ty τ⟩ :: Δ)) : σ.Wf (Γ ++ Δ) := by
  generalize eq : Γ ++ ⟨X, Binding.ty τ⟩ :: Δ = Θ at wf
  induction wf generalizing Γ with
  | all => apply all (free_union [Context.dom] Var) <;> grind
  | _ => grind [dlookup_append]

/-- A type remains well-formed under context substitution (of a well-formed type). -/
lemma map_subst (wf_σ : σ.Wf (Γ ++ ⟨X, Binding.sub τ⟩ :: Δ)) (wf_τ' : τ'.Wf Δ)
    (ok : (Γ.map_val (·[X:=τ']) ++ Δ)✓) : σ[X:=τ'].Wf <| Γ.map_val (·[X:=τ']) ++ Δ := sorry

variable [HasFresh Var] in
/-- A type remains well-formed under opening (to a well-formed type). -/
lemma open_lc (ok_Γ : Γ✓) (wf_all : (Ty.all σ τ).Wf Γ) (wf_δ : δ.Wf Γ) : (τ ^ᵞ δ).Wf Γ := by
  cases wf_all with | all => 
    let ⟨X, _⟩ := fresh_exists <| free_union [fv, Context.dom] Var
    have : Γ = Context.map_val (·[X:=δ]) [] ++ Γ := by grind
    grind [open_subst_intro, map_subst]

/-- A type bound in a context is well formed. -/
lemma from_bind_ty (wf : Γ.Wf) (bind : Binding.ty σ ∈ Γ.dlookup X) : σ.Wf Γ := by
  induction wf <;> grind [Env.Wf.to_ok, weaken_head]

/-- A type at the head of a well-formed context is well-formed. -/
lemma from_env_bind_ty (wf : Env.Wf (⟨X, Binding.ty σ⟩ :: Γ)) : σ.Wf Γ := by
  cases wf
  assumption

/-- A subtype at the head of a well-formed context is well-formed. -/
lemma from_env_bind_sub (wf : Env.Wf (⟨X, Binding.sub σ⟩ :: Γ)) : σ.Wf Γ := by
  cases wf
  assumption

variable [HasFresh Var] in
/-- A variable not appearing in a context does not appear in its well-formed types. -/
lemma nmem_fv {σ : Ty Var} (wf : σ.Wf Γ) (nmem : X ∉ Γ.dom) : X ∉ σ.fv := by
  induction wf with
  | all => have := fresh_exists <| free_union [dom] Var; grind [keys_cons, nmem_fv_open, openRec_lc]
  | _ => grind

end Ty.Wf

namespace Env.Wf

open Context List Binding

/-- A context remains well-formed under narrowing (of a well-formed subtype). -/
lemma narrow (wf_env : Env.Wf (Γ ++ ⟨X, Binding.sub τ⟩ :: Δ)) (wf_τ' : τ'.Wf Δ) : 
    Env.Wf (Γ ++ ⟨X, Binding.sub τ'⟩ :: Δ) := by
  induction Γ <;> cases wf_env <;> 
  grind [to_ok, Ty.Wf.narrow, nmem_append_keys, eq_nil_of_append_eq_nil, cases Env.Wf]
      
/-- A context remains well-formed under strengthening. -/
lemma strengthen (wf : Env.Wf <| Γ ++ ⟨X, Binding.ty τ⟩ :: Δ) : Env.Wf <| Γ ++ Δ := by
  induction Γ <;> cases wf <;> grind [Ty.Wf.strengthen, List.nmem_append_keys]

/-- A context remains well-formed under substitution (of a well-formed type). -/
lemma map_subst (wf_env : Env.Wf (Γ ++ ⟨X, Binding.sub τ⟩ :: Δ)) (wf_τ' : τ'.Wf Δ) :
    Env.Wf <| Γ.map_val (·[X:=τ']) ++ Δ := by
  induction Γ generalizing wf_τ' Δ τ' <;> cases wf_env
  case nil => grind
  case cons.sub | cons.ty => constructor <;> grind [Ty.Wf.map_subst, Env.Wf.to_ok, keys_append]
    
variable [HasFresh Var]

/-- A well-formed context is unchaged by substituting for a free key. -/
lemma map_subst_nmem (Γ : Env Var) (X : Var) (σ : Ty Var) (wf : Γ.Wf) (nmem : X ∉ Γ.dom) :
    Γ = Γ.map_val (·[X:=σ]) := by
  induction wf <;> grind [Ty.Wf.nmem_fv, Binding.subst_fresh]

end Env.Wf
    
end LambdaCalculus.LocallyNameless.Fsub
