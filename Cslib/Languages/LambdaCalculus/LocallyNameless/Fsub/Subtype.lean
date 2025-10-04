/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.WellFormed

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines the subtyping relation.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

variable {Var : Type*} [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Fsub

open Ty

/-- The subtyping relation. -/
inductive Sub : Env Var → Ty Var → Ty Var → Prop
  | top : Γ.Wf → σ.Wf Γ → Sub Γ σ top
  | refl_tvar : Γ.Wf → (fvar X).Wf Γ → Sub Γ (fvar X) (fvar X)
  | trans_tvar : Binding.sub σ ∈ Γ.dlookup X → Sub Γ σ σ' → Sub Γ (fvar X) σ'
  | arrow : Sub Γ σ σ' → Sub Γ τ' τ → Sub Γ (arrow σ' τ') (arrow σ τ)
  | all (L : Finset Var) :
      Sub Γ σ σ' →
      (∀ X ∉ L, Sub (⟨X, Binding.sub σ⟩ :: Γ) (τ' ^ᵞ fvar X) (τ ^ᵞ fvar X)) →
      Sub Γ (all σ' τ') (all σ τ)
  | sum : Sub Γ σ' σ → Sub Γ τ' τ → Sub Γ (sum σ' τ') (sum σ τ)

namespace Sub

open Context List Ty.Wf Env.Wf Binding

attribute [scoped grind] Sub.top Sub.refl_tvar Sub.trans_tvar Sub.arrow Sub.sum

variable {Γ Δ Θ : Env Var} {σ τ δ : Ty Var}

/-- Subtypes have well-formed contexts and types. -/
@[grind →]
lemma wf (Γ : Env Var) (σ σ' : Ty Var) (sub : Sub Γ σ σ') : Γ.Wf ∧ σ.Wf Γ ∧ σ'.Wf Γ := by
  induction sub with
  | all => 
    refine ⟨by grind, ?_, ?_⟩ <;>
    apply Wf.all (free_union Var) <;> grind [Wf.narrow_cons, cases Env.Wf, cases LC]
  | _ => grind

/-- Subtypes are reflexive when well-formed. -/
lemma refl (wf_Γ : Γ.Wf) (wf_σ : σ.Wf Γ) : Sub Γ σ σ := by
  induction wf_σ with
  | all => apply all (free_union [Context.dom] Var) <;> grind
  | _ => grind

/-- Weakening of subtypes. -/
lemma weaken (sub : Sub (Γ ++ Θ) σ σ') (wf : (Γ ++ Δ ++ Θ).Wf) : Sub (Γ ++ Δ ++ Θ) σ σ' := by
  generalize eq : Γ ++ Θ = ΓΘ at sub
  induction sub generalizing Γ 
  case all => 
    subst eq
    apply all (free_union [Context.dom] Var) <;> grind [keys_append]
  all_goals grind [Ty.Wf.weaken, <= sublist_dlookup]

lemma weaken_head (sub : Sub Δ σ σ') (wf : (Γ ++ Δ).Wf) : Sub (Γ ++ Δ) σ σ' := by
  have eq : Γ ++ Δ = [] ++ Γ ++ Δ := by grind
  grind [weaken]

lemma narrow_aux
    (trans : ∀ Γ σ τ, Sub Γ σ δ → Sub Γ δ τ → Sub Γ σ τ)
    (sub₁ : Sub (Γ ++ ⟨X, Binding.sub δ⟩ :: Δ) σ τ) (sub₂ : Sub Δ δ' δ) : 
      Sub (Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ) σ τ := by
  generalize eq : Γ ++ ⟨X, Binding.sub δ⟩ :: Δ = Θ at sub₁ 
  induction sub₁ generalizing Γ δ
  case trans_tvar σ _ σ' X' mem sub ih => 
    have p : ∀ δ, Γ ++ ⟨X, Binding.sub δ⟩ :: Δ ~ ⟨X, Binding.sub δ⟩ :: (Γ ++ Δ) := 
      by grind [perm_middle]
    have := perm_dlookup (p := p δ')
    have := perm_dlookup (p := p δ)
    grind [Sub.weaken, sublist_append_of_sublist_right]
  case all => apply Sub.all (free_union Var) <;> grind
  all_goals grind [Env.Wf.narrow, Ty.Wf.narrow]

@[grind →]
lemma trans : Sub Γ σ δ → Sub Γ δ τ → Sub Γ σ τ := by
  intro sub₁ sub₂ 
  have δ_lc : δ.LC := by grind
  induction δ_lc generalizing Γ σ τ
  case top => cases sub₁ <;> cases sub₂ <;> grind
  case var X =>
    generalize eq : fvar X = γ at sub₁ 
    induction sub₁ <;> grind [cases Sub]
  case arrow σ' τ' _ _ _ _ => 
    generalize eq : σ'.arrow τ' = γ at sub₁
    induction sub₁ <;> grind [cases Sub]
  case sum σ' τ' _ _ _ _ => 
    generalize eq : σ'.sum τ' = γ at sub₁
    induction sub₁ <;> grind [cases Sub]
  case all σ' τ' _ _ _ _ _ => 
    generalize eq : σ'.all τ' = γ at sub₁
    induction sub₁
    case all =>
      cases eq
      cases sub₂
      case refl.top Γ σ'' τ'' _ _ _ _ _ _ _ => 
        have : Sub Γ (σ''.all τ'') (σ'.all τ') := by apply all (free_union Var) <;> grind
        grind
      case refl.all Γ _ _ _ _ _ σ _ _ _ _ _ _ => 
        apply all (free_union Var)
        · grind
        · intro X nmem
          have eq : ∀ σ, ⟨X, Binding.sub σ⟩ :: Γ = [] ++ ⟨X, Binding.sub σ⟩ :: Γ := by grind
          grind [Sub.narrow_aux]
    all_goals grind

instance (Γ : Env Var) : Trans (Sub Γ) (Sub Γ) (Sub Γ) := 
  ⟨Sub.trans⟩

/-- Narrowing of subtypes. -/
lemma narrow (sub_δ : Sub Δ δ δ') (sub_narrow : Sub (Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ) σ τ) :
    Sub (Γ ++ ⟨X, Binding.sub δ⟩ :: Δ) σ τ := by
  apply narrow_aux (δ := δ') <;> grind

variable [HasFresh Var] in
/-- Subtyping of substitutions. -/
lemma map_subst (sub₁ : Sub (Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ) σ τ) (sub₂ : Sub Δ δ δ') :
    Sub (Γ.map_val (·[X:=δ]) ++ Δ) (σ[X:=δ]) (τ[X:=δ]) := by
  generalize eq : Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ = Θ at sub₁
  induction sub₁ generalizing Γ
  case all => apply Sub.all (free_union Var) <;> grind [open_subst_var]
  case trans_tvar σ _ _ X' _ _ _ => 
    have := map_subst_nmem Δ X δ
    have : Γ ++ ⟨X, .sub δ'⟩ :: Δ ~ ⟨X, .sub δ'⟩ :: (Γ ++ Δ) := perm_middle
    have : .sub σ ∈ dlookup X' (⟨X, .sub δ'⟩ :: (Γ ++ Δ)) := by grind [perm_dlookup]
    have := @map_val_mem Var (f := ((·[X:=δ]) : Binding Var → Binding Var))
    by_cases X = X'
    · trans δ' <;> grind [→ mem_dlookup, Ty.subst_fresh, Ty.Wf.nmem_fv, weaken_head, keys_append]
    · grind [keys_append]
  all_goals
    grind [Env.Wf.to_ok, keys_append, Sub.refl, Env.Wf.map_subst, Ty.Wf.map_subst]

/-- Strengthening of subtypes. -/
lemma strengthen (sub : Sub (Γ ++ ⟨X, Binding.ty δ⟩ :: Δ) σ τ) :  Sub (Γ ++ Δ) σ τ := by
  generalize eq : Γ ++ ⟨X, Binding.ty δ⟩ :: Δ = Θ at sub
  induction sub generalizing Γ 
  case all => apply Sub.all (free_union Var) <;> grind
  all_goals grind [to_ok, Wf.strengthen, Env.Wf.strengthen, dlookup_append]
  
end Sub

end LambdaCalculus.LocallyNameless.Fsub
