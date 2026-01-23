/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Reduction
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Subtype

@[expose] public section

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines the typing relation.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

namespace Cslib

variable {Var : Type*} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.LocallyNameless.Fsub

open Term Ty Ty.Wf Env.Wf Sub Context List Binding

/-- The typing relation. -/
inductive Typing : Env Var → Term Var → Ty Var → Prop
  | var : Γ.Wf → Binding.ty σ ∈ Γ.dlookup x → Typing Γ (fvar x) σ
  | abs (L : Finset Var) :
      (∀ x ∉ L, Typing (⟨x, Binding.ty σ⟩ :: Γ) (t₁ ^ᵗᵗ fvar x) τ) →
      Typing Γ (abs σ t₁) (arrow σ τ)
  | app : Typing Γ t₁ (arrow σ τ) → Typing Γ t₂ σ → Typing Γ (app t₁ t₂) τ
  | tabs (L : Finset Var) :
      (∀ X ∉ L, Typing (⟨X, Binding.sub σ⟩ :: Γ) (t₁ ^ᵗᵞ fvar X) (τ ^ᵞ fvar X)) →
      Typing Γ (tabs σ t₁) (all σ τ)
  | tapp : Typing Γ t₁ (all σ τ) → Sub Γ σ' σ → Typing Γ (tapp t₁ σ') (τ ^ᵞ σ')
  | sub : Typing Γ t τ → Sub Γ τ τ' → Typing Γ t τ'
  | let' (L : Finset Var) :
      Typing Γ t₁ σ →
      (∀ x ∉ L, Typing (⟨x, Binding.ty σ⟩ :: Γ) (t₂ ^ᵗᵗ fvar x) τ) →
      Typing Γ (let' t₁ t₂) τ
  | inl : Typing Γ t₁ σ → τ.Wf Γ → Typing Γ (inl t₁) (sum σ τ)
  | inr : Typing Γ t₁ τ → σ.Wf Γ → Typing Γ (inr t₁) (sum σ τ)
  | case (L : Finset Var) :
      Typing Γ t₁ (sum σ τ) →
      (∀ x ∉ L, Typing (⟨x, Binding.ty σ⟩ :: Γ) (t₂ ^ᵗᵗ fvar x) δ) →
      (∀ x ∉ L, Typing (⟨x, Binding.ty τ⟩ :: Γ) (t₃ ^ᵗᵗ fvar x) δ) →
      Typing Γ (case t₁ t₂ t₃) δ

namespace Typing

variable {Γ Δ Θ : Env Var} {σ τ δ : Ty Var}

attribute [grind .] Typing.var Typing.app Typing.tapp Typing.sub Typing.inl Typing.inr

/-- Typings have well-formed contexts and types. -/
@[grind →]
lemma wf {Γ : Env Var} {t : Term Var} {τ : Ty Var} (der : Typing Γ t τ) : Γ.Wf ∧ t.LC ∧ τ.Wf Γ := by
  induction der <;> let L := free_union Var <;> have ⟨x, nmem⟩ := fresh_exists L
  case tabs ih =>
    cases (ih x (by grind)).left
    grind [LC.tabs L, Ty.Wf.all L]
  case abs ih =>
    cases (ih x (by grind)).left
    grind [LC.abs L, Wf.strengthen]
  case let' => grind [LC.let' L, Ty.Wf.strengthen]
  case case => refine ⟨?_, LC.case L ?_ ?_ ?_, ?_⟩ <;> grind [Ty.Wf.strengthen]
  all_goals grind [of_bind_ty, open_lc, cases Ty.Wf]

/-- Weakening of typings. -/
lemma weaken (der : Typing (Γ ++ Δ) t τ) (wf : (Γ ++ Θ ++ Δ).Wf) :
    Typing (Γ ++ Θ ++ Δ) t τ := by
  generalize eq : Γ ++ Δ = ΓΔ at der
  induction der generalizing Γ
  case' abs => apply abs ((Γ ++ Θ ++ Δ).dom ∪ free_union Var)
  case' tabs => apply tabs ((Γ ++ Θ ++ Δ).dom ∪ free_union Var)
  case' let' der _ => apply let' ((Γ ++ Θ ++ Δ).dom ∪ free_union Var) (der wf eq)
  case' case der _ _ => apply case ((Γ ++ Θ ++ Δ).dom ∪ free_union Var) (der wf eq)
  all_goals
    grind [Wf.weaken, Sub.weaken, Wf.of_env_ty, Wf.of_env_sub, Sub.refl, <= sublist_dlookup]

/-- Weakening of typings (at the front). -/
lemma weaken_head (der : Typing Δ t τ) (wf : (Γ ++ Δ).Wf) :
    Typing (Γ ++ Δ) t τ := by
  have eq : Δ = [] ++ Δ := by rfl
  rw [eq] at der
  grind [Typing.weaken der wf]

/-- Narrowing of typings. -/
lemma narrow (sub : Sub Δ δ δ') (der : Typing (Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ) t τ) :
    Typing (Γ ++ ⟨X, Binding.sub δ⟩ :: Δ) t τ := by
  generalize eq : Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ = Θ at der
  induction der generalizing Γ
  case var X' _ _ =>
    grind [Env.Wf.narrow, List.perm_nodupKeys, => List.perm_dlookup]
  case' abs  => apply abs (free_union Var)
  case' tabs => apply tabs (free_union Var)
  case' let' der _ => apply let' (free_union Var) (der eq)
  case' case der _ _ => apply case (free_union Var) (der eq)
  all_goals grind [Ty.Wf.narrow, Env.Wf.narrow, Sub.narrow]

/-- Term substitution within a typing. -/
lemma subst_tm (der : Typing (Γ ++ ⟨X, .ty σ⟩ :: Δ) t τ) (der_sub : Typing Δ s σ) :
    Typing (Γ ++ Δ) (t[X := s]) τ := by
  generalize eq : Γ ++ ⟨X, .ty σ⟩ :: Δ = Θ at der
  induction der generalizing Γ X
  case var σ' _ X' _ _ =>
    have : Γ ++ ⟨X, .ty σ⟩ :: Δ ~ ⟨X, .ty σ⟩ :: (Γ ++ Δ) := perm_middle
    by_cases eq : X = X'
    · #adaptation_note
      /--
      Moving from `nightly-2025-09-15` to `nightly-2025-10-19`,
      I've had to remove the `append_assoc` lemma from grind;
      without this `grind` is exploding. This requires further investigation.
      -/
      grind [→ List.mem_dlookup, weaken_head, Env.Wf.strengthen, -append_assoc]
    · grind [Env.Wf.strengthen, => List.perm_dlookup]
  case abs => grind [abs (free_union Var), open_tm_subst_tm_var]
  case tabs => grind [tabs (free_union Var), open_ty_subst_tm_var]
  case let' der _ => grind [let' (free_union Var) (der eq), open_tm_subst_tm_var]
  case case der _ _ =>
    apply case (free_union Var) (der eq) <;> grind [open_tm_subst_tm_var]
  all_goals grind [Env.Wf.strengthen, Ty.Wf.strengthen, Sub.strengthen]

/-- Type substitution within a typing. -/
lemma subst_ty (der : Typing (Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ) t τ) (sub : Sub Δ δ δ') :
    Typing (Γ.map_val (·[X := δ]) ++ Δ) (t[X := δ]) (τ[X := δ]) := by
  generalize eq : Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ = Θ at der
  induction der generalizing Γ X
  case var σ _ X' _ mem =>
    have := map_subst_nmem Δ X δ
    have := @map_val_mem Var (f := ((·[X:=δ]) : Binding Var → Binding Var))
    grind [Env.Wf.map_subst, → notMem_keys_of_nodupKeys_cons]
  case abs => grind [abs (free_union [Ty.fv] Var), Ty.subst_fresh, open_tm_subst_ty_var]
  case tabs => grind [tabs (free_union Var), open_ty_subst_ty_var, open_subst_var]
  case let' der _ =>
    apply let' (free_union Var) (der eq)
    grind [open_tm_subst_ty_var]
  case case der _ _ =>
    apply case (free_union Var) (der eq) <;> grind [open_tm_subst_ty_var]
  case tapp => grind [Ty.open_subst, Env.Wf.map_subst, Ty.Wf.map_subst, Sub.map_subst]
  all_goals grind [Env.Wf.map_subst, Ty.Wf.map_subst, Sub.map_subst]

open Term Ty

omit [HasFresh Var]

/-- Invert the typing of an abstraction. -/
lemma abs_inv (der : Typing Γ (.abs γ' t) τ) (sub : Sub Γ τ (arrow γ δ)) :
     Sub Γ γ γ'
  ∧ ∃ δ' L, ∀ x ∉ (L : Finset Var),
    Typing (⟨x, Binding.ty γ'⟩ :: Γ) (t ^ᵗᵗ .fvar x) δ' ∧ Sub Γ δ' δ := by
  generalize eq : Term.abs γ' t = e at der
  induction der generalizing t γ' γ δ
  case abs τ L _ _ =>
    cases eq
    cases sub
    split_ands
    · assumption
    · exists τ, L
      grind
  case sub Γ _ τ τ' _ _ ih =>
    subst eq
    have sub' : Sub Γ τ (γ.arrow δ) := by grind
    obtain ⟨_, δ', L, _⟩ := ih sub' (by rfl)
    split_ands
    · assumption
    · exists δ', L
  all_goals grind

variable [HasFresh Var] in
/-- Invert the typing of a type abstraction. -/
lemma tabs_inv (der : Typing Γ (.tabs γ' t) τ) (sub : Sub Γ τ (all γ δ)) :
     Sub Γ γ γ'
  ∧ ∃ δ' L, ∀ X ∉ (L : Finset Var),
     Typing (⟨X, Binding.sub γ⟩ :: Γ) (t ^ᵗᵞ fvar X) (δ' ^ᵞ fvar X)
     ∧ Sub (⟨X, Binding.sub γ⟩ :: Γ) (δ' ^ᵞ fvar X) (δ ^ᵞ fvar X) := by
  generalize eq : Term.tabs γ' t = e at der
  induction der generalizing γ δ t γ'
  case tabs σ Γ _ τ L der _ =>
    cases sub with | all L' sub =>
    split_ands
    · grind
    · exists τ, L ∪ L'
      intro X _
      have eq : ⟨X, Binding.sub γ⟩ :: Γ = [] ++ ⟨X, Binding.sub γ⟩ :: Γ := by rfl
      grind [narrow]
  case sub Γ _ τ τ' _ _ ih =>
    subst eq
    have sub' : Sub Γ τ (γ.all δ) := by trans τ' <;> grind
    obtain ⟨_, δ', L, _⟩ := ih sub' (by rfl)
    split_ands
    · assumption
    · exists δ', L
  all_goals grind

/-- Invert the typing of a left case. -/
lemma inl_inv (der : Typing Γ (.inl t) τ) (sub : Sub Γ τ (sum γ δ)) :
    ∃ γ', Typing Γ t γ' ∧ Sub Γ γ' γ := by
  generalize eq : t.inl =t at der
  induction der generalizing γ δ <;> grind [cases Sub]

/-- Invert the typing of a right case. -/
lemma inr_inv (der : Typing Γ (.inr t) T) (sub : Sub Γ T (sum γ δ)) :
    ∃ δ', Typing Γ t δ' ∧ Sub Γ δ' δ := by
  generalize eq : t.inr =t at der
  induction der generalizing γ δ <;> grind [cases Sub]

/-- A value that types as a function is an abstraction. -/
lemma canonical_form_abs (val : Value t) (der : Typing [] t (arrow σ τ)) :
    ∃ δ t', t = .abs δ t' := by
  generalize eq  : σ.arrow τ = γ at der
  generalize eq' : [] = Γ at der
  induction der generalizing σ τ <;> grind [cases Sub, cases Value]

/-- A value that types as a quantifier is a type abstraction. -/
lemma canonical_form_tabs (val : Value t) (der : Typing [] t (all σ τ)) :
    ∃ δ t', t = .tabs δ t' := by
  generalize eq  : σ.all τ = γ at der
  generalize eq' : [] = Γ at der
  induction der generalizing σ τ <;> grind [cases Sub, cases Value]

/-- A value that types as a sum is a left or right case. -/
lemma canonical_form_sum (val : Value t) (der : Typing [] t (sum σ τ)) :
    ∃ t', t = .inl t' ∨ t = .inr t' := by
  generalize eq  : σ.sum τ = γ at der
  generalize eq' : [] = Γ at der
  induction der generalizing σ τ <;> grind [cases Sub, cases Value]

end Typing

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
