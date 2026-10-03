/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Reduction
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Subtype

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines the typing relation.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

@[expose] public section

namespace Cslib

variable {Var : Type*} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.LocallyNameless.Fsub

open Term Ty Ty.Wf Env.Wf Fsub.Sub Context List Binding

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

/-- Typings have well-formed contexts and types. -/
lemma wf {Γ : Env Var} {t : Term Var} {τ : Ty Var} (der : Typing Γ t τ) : Γ.Wf ∧ t.LC ∧ τ.Wf Γ := by
  induction der with
  | var wf mem => exact ⟨wf, LC.var, of_bind_ty wf mem⟩
  | abs L _ ih =>
    obtain ⟨x, hx⟩ := fresh_exists L
    have h := ih x hx
    cases h.1 with
    | ty wf σ_wf _ =>
      exact ⟨wf, LC.abs L σ_wf.lc (fun x hx => (ih x hx).2.1),
        Ty.Wf.arrow σ_wf (Ty.Wf.strengthen (Γ := []) h.2.2)⟩
  | app _ _ ih₁ ih₂ =>
    cases ih₁.2.2 with
    | arrow _ τ_wf => exact ⟨ih₁.1, LC.app ih₁.2.1 ih₂.2.1, τ_wf⟩
  | tabs L _ ih =>
    obtain ⟨X, hX⟩ := fresh_exists L
    cases (ih X hX).1 with
    | sub wf σ_wf _ =>
      exact ⟨wf, LC.tabs L σ_wf.lc (fun X hX => (ih X hX).2.1),
        Ty.Wf.all L σ_wf (fun X hX => (ih X hX).2.2)⟩
  | tapp _ sub ih =>
    have h := sub.wf
    exact ⟨ih.1, LC.tapp ih.2.1 h.2.1.lc, open_lc ih.1.to_ok ih.2.2 h.2.1⟩
  | sub _ sub ih => exact ⟨ih.1, ih.2.1, sub.wf.2.2⟩
  | let' L _ _ ih₁ ih₂ =>
    obtain ⟨x, hx⟩ := fresh_exists L
    exact ⟨ih₁.1, LC.let' L ih₁.2.1 (fun x hx => (ih₂ x hx).2.1),
      Ty.Wf.strengthen (Γ := []) (ih₂ x hx).2.2⟩
  | inl _ wf ih => exact ⟨ih.1, LC.inl ih.2.1, Ty.Wf.sum ih.2.2 wf⟩
  | inr _ wf ih => exact ⟨ih.1, LC.inr ih.2.1, Ty.Wf.sum wf ih.2.2⟩
  | case L _ _ _ ih₁ ih₂ ih₃ =>
    obtain ⟨x, hx⟩ := fresh_exists L
    exact ⟨ih₁.1, LC.case L ih₁.2.1 (fun x hx => (ih₂ x hx).2.1)
      (fun x hx => (ih₃ x hx).2.1), Ty.Wf.strengthen (Γ := []) (ih₂ x hx).2.2⟩

/-- Weakening of typings. -/
lemma weaken (der : Typing (Γ ++ Δ) t τ) (wf : (Γ ++ Θ ++ Δ).Wf) :
    Typing (Γ ++ Θ ++ Δ) t τ := by
  generalize eq : Γ ++ Δ = ΓΔ at der
  induction der generalizing Γ with
  | var wf' mem =>
    subst eq
    apply var wf
    apply sublist_dlookup wf.to_ok _ mem
    simpa only [append_assoc] using
      (Sublist.append (Sublist.refl Γ) (sublist_append_right Θ Δ))
  | abs L der ih =>
    subst eq
    apply abs (L ∪ (Γ ++ Θ ++ Δ).dom)
    intro x hx
    simp only [Finset.mem_union, not_or] at hx
    exact ih x hx.1 (Γ := ⟨x, .ty _⟩ :: Γ)
      (Env.Wf.ty wf (Ty.Wf.weaken (of_env_ty (der x hx.1).wf.1) wf.to_ok) hx.2) rfl
  | app _ _ ih₁ ih₂ => exact app (ih₁ wf eq) (ih₂ wf eq)
  | tabs L der ih =>
    subst eq
    apply tabs (L ∪ (Γ ++ Θ ++ Δ).dom)
    intro X hX
    simp only [Finset.mem_union, not_or] at hX
    exact ih X hX.1 (Γ := ⟨X, .sub _⟩ :: Γ)
      (Env.Wf.sub wf (Ty.Wf.weaken (of_env_sub (der X hX.1).wf.1) wf.to_ok) hX.2) rfl
  | tapp _ hsub ih =>
    subst eq
    exact tapp (ih wf rfl) (Sub.weaken hsub wf)
  | sub _ hsub ih =>
    subst eq
    exact Typing.sub (ih wf rfl) (Sub.weaken hsub wf)
  | let' L _ der ih₁ ih₂ =>
    subst eq
    apply let' (L ∪ (Γ ++ Θ ++ Δ).dom) (ih₁ wf rfl)
    intro x hx
    simp only [Finset.mem_union, not_or] at hx
    exact ih₂ x hx.1 (Γ := ⟨x, .ty _⟩ :: Γ)
      (Env.Wf.ty wf (Ty.Wf.weaken (of_env_ty (der x hx.1).wf.1) wf.to_ok) hx.2) rfl
  | inl _ hτ ih =>
    subst eq
    exact inl (ih wf rfl) (Ty.Wf.weaken hτ wf.to_ok)
  | inr _ hσ ih =>
    subst eq
    exact inr (ih wf rfl) (Ty.Wf.weaken hσ wf.to_ok)
  | case L _ der₂ der₃ ih₁ ih₂ ih₃ =>
    subst eq
    apply case (L ∪ (Γ ++ Θ ++ Δ).dom) (ih₁ wf rfl)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      exact ih₂ x hx.1 (Γ := ⟨x, .ty _⟩ :: Γ)
        (Env.Wf.ty wf (Ty.Wf.weaken (of_env_ty (der₂ x hx.1).wf.1) wf.to_ok) hx.2) rfl
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      exact ih₃ x hx.1 (Γ := ⟨x, .ty _⟩ :: Γ)
        (Env.Wf.ty wf (Ty.Wf.weaken (of_env_ty (der₃ x hx.1).wf.1) wf.to_ok) hx.2) rfl

/-- Weakening of typings (at the front). -/
lemma weaken_head (der : Typing Δ t τ) (wf : (Γ ++ Δ).Wf) :
    Typing (Γ ++ Δ) t τ := by
  exact weaken (Γ := []) der wf

/-- Narrowing of typings. -/
lemma narrow (sub : Sub Δ δ δ') (der : Typing (Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ) t τ) :
    Typing (Γ ++ ⟨X, Binding.sub δ⟩ :: Δ) t τ := by
  generalize eq : Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ = Θ at der
  induction der generalizing Γ with
  | var wf mem =>
    subst eq
    have wf' := Env.Wf.narrow wf sub.wf.2.1
    apply var wf'
    apply mem_dlookup wf'.to_ok
    have hmem := of_mem_dlookup mem
    simp only [mem_append, mem_cons] at hmem ⊢
    rcases hmem with hmem | hmem | hmem
    · exact Or.inl hmem
    · cases hmem
    · exact Or.inr (Or.inr hmem)
  | abs L _ ih =>
    subst eq
    exact abs L (fun x hx => ih x hx (Γ := ⟨x, .ty _⟩ :: Γ) rfl)
  | app _ _ ih₁ ih₂ => exact app (ih₁ eq) (ih₂ eq)
  | tabs L _ ih =>
    subst eq
    exact tabs L (fun X hX => ih X hX (Γ := ⟨X, .sub _⟩ :: Γ) rfl)
  | tapp _ hsub ih =>
    subst eq
    exact tapp (ih rfl) (Sub.narrow sub hsub)
  | sub _ hsub ih =>
    subst eq
    exact Typing.sub (ih rfl) (Sub.narrow sub hsub)
  | let' L _ _ ih₁ ih₂ =>
    subst eq
    exact let' L (ih₁ rfl) (fun x hx => ih₂ x hx (Γ := ⟨x, .ty _⟩ :: Γ) rfl)
  | inl der hτ ih =>
    subst eq
    exact inl (ih rfl) (Ty.Wf.narrow hτ (Env.Wf.narrow der.wf.1 sub.wf.2.1).to_ok)
  | inr der hσ ih =>
    subst eq
    exact inr (ih rfl) (Ty.Wf.narrow hσ (Env.Wf.narrow der.wf.1 sub.wf.2.1).to_ok)
  | case L _ _ _ ih₁ ih₂ ih₃ =>
    subst eq
    exact case L (ih₁ rfl) (fun x hx => ih₂ x hx (Γ := ⟨x, .ty _⟩ :: Γ) rfl)
      (fun x hx => ih₃ x hx (Γ := ⟨x, .ty _⟩ :: Γ) rfl)

/-- Term substitution within a typing. -/
lemma subst_tm (der : Typing (Γ ++ ⟨X, .ty σ⟩ :: Δ) t τ) (der_sub : Typing Δ s σ) :
    Typing (Γ ++ Δ) (t[X := s]) τ := by
  generalize eq : Γ ++ ⟨X, .ty σ⟩ :: Δ = Θ at der
  induction der generalizing Γ X with
  | @var τ Θ x wf mem =>
    subst eq
    have wf' := Env.Wf.strengthen wf
    have mem' := mem
    rw [perm_dlookup x wf.to_ok (perm_middle :
      Γ ++ ⟨X, .ty σ⟩ :: Δ ~ ⟨X, .ty σ⟩ :: (Γ ++ Δ))] at mem'
    change Typing (Γ ++ Δ) (if x = X then s else fvar x) τ
    by_cases hx : x = X
    · subst x
      simp only [dlookup_cons_eq, Option.mem_some, Binding.ty.injEq] at mem'
      subst τ
      simpa using weaken_head der_sub wf'
    · rw [ite_eq_right hx]
      apply var wf'
      simpa only [dlookup_cons_ne (Γ ++ Δ) ⟨X, .ty σ⟩ hx] using mem'
  | abs L _ ih =>
    subst eq
    apply abs (L ∪ {X})
    intro x hx
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hx
    simpa only [cons_append, substTm_def, openTm_substTm_var _ hx.2 der_sub.wf.2.1] using
      ih x hx.1 (Γ := ⟨x, .ty _⟩ :: Γ) rfl
  | app _ _ ih₁ ih₂ => exact app (ih₁ eq) (ih₂ eq)
  | tabs L _ ih =>
    subst eq
    apply tabs L
    intro Y hY
    simpa only [cons_append, substTm_def, openTy_substTm_var _ der_sub.wf.2.1] using
      ih Y hY (Γ := ⟨Y, .sub _⟩ :: Γ) rfl
  | tapp _ hsub ih =>
    subst eq
    exact tapp (ih rfl) (Sub.strengthen hsub)
  | sub _ hsub ih =>
    subst eq
    exact Typing.sub (ih rfl) (Sub.strengthen hsub)
  | let' L _ _ ih₁ ih₂ =>
    subst eq
    apply let' (L ∪ {X}) (ih₁ rfl)
    intro x hx
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hx
    simpa only [cons_append, substTm_def, openTm_substTm_var _ hx.2 der_sub.wf.2.1] using
      ih₂ x hx.1 (Γ := ⟨x, .ty _⟩ :: Γ) rfl
  | inl _ hτ ih =>
    subst eq
    exact inl (ih rfl) (Ty.Wf.strengthen hτ)
  | inr _ hσ ih =>
    subst eq
    exact inr (ih rfl) (Ty.Wf.strengthen hσ)
  | case L _ _ _ ih₁ ih₂ ih₃ =>
    subst eq
    apply case (L ∪ {X}) (ih₁ rfl)
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hx
      simpa only [cons_append, substTm_def, openTm_substTm_var _ hx.2 der_sub.wf.2.1] using
        ih₂ x hx.1 (Γ := ⟨x, .ty _⟩ :: Γ) rfl
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hx
      simpa only [cons_append, substTm_def, openTm_substTm_var _ hx.2 der_sub.wf.2.1] using
        ih₃ x hx.1 (Γ := ⟨x, .ty _⟩ :: Γ) rfl

/-- Type substitution within a typing. -/
lemma subst_ty (der : Typing (Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ) t τ) (sub : Sub Δ δ δ') :
    Typing (Γ.mapVal (·[X := δ]) ++ Δ) (t[X := δ]) (τ[X := δ]) := by
  generalize eq : Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ = Θ at der
  induction der generalizing Γ X with
  | @var τ Θ x wf mem =>
    subst eq
    have wf' := Env.Wf.map_subst wf sub.wf.2.1
    apply var wf'
    have ok := nodupKeys_cons.mp (nodupKeys_middle.mp wf.to_ok)
    have hX : X ∉ Δ.dom := by
      have h := ok.1
      simp only [keys_append, mem_append, not_or] at h
      simpa only [dom, mem_toFinset] using h.2
    have mem' : Binding.ty τ ∈ (Γ ++ Δ).dlookup x := by
      apply mem_dlookup ok.2
      have hmem := of_mem_dlookup mem
      simp only [mem_append, mem_cons] at hmem ⊢
      rcases hmem with hmem | hmem | hmem
      · exact Or.inl hmem
      · cases hmem
      · exact Or.inr hmem
    have hmap := mapVal_mem mem' (fun b : Binding Var => b[X := δ])
    have heq : (Γ ++ Δ).mapVal (·[X := δ]) = Γ.mapVal (·[X := δ]) ++ Δ := by
      rw [mapVal, map_append]
      change Γ.mapVal (·[X := δ]) ++ Δ.mapVal (·[X := δ]) = _
      rw [← map_subst_nmem Δ X δ sub.wf.1 hX]
    rw [heq] at hmap
    exact hmap
  | abs L _ ih =>
    subst eq
    apply abs L
    intro x hx
    simpa only [Term.substTy_def, Ty.subst_def, mapVal, map_cons, Binding.substTy,
      cons_append, openTm_substTy_var] using
      ih x hx (Γ := ⟨x, .ty _⟩ :: Γ) rfl
  | app _ _ ih₁ ih₂ => exact app (ih₁ eq) (ih₂ eq)
  | tabs L _ ih =>
    subst eq
    apply tabs (L ∪ {X})
    intro Y hY
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hY
    simpa only [Term.substTy_def, Ty.subst_def, mapVal, map_cons, Binding.substSub, cons_append,
      openTy_substTy_var _ hY.2 sub.wf.2.1.lc, open_subst_var _ hY.2 sub.wf.2.1.lc] using
      ih Y hY.1 (Γ := ⟨Y, .sub _⟩ :: Γ) rfl
  | tapp _ hsub ih =>
    subst eq
    rw [Ty.open_subst _ _ sub.wf.2.1.lc]
    exact tapp (ih rfl) (Sub.map_subst hsub sub)
  | sub _ hsub ih =>
    subst eq
    exact Typing.sub (ih rfl) (Sub.map_subst hsub sub)
  | let' L _ _ ih₁ ih₂ =>
    subst eq
    apply let' L (ih₁ rfl)
    intro x hx
    simpa only [Term.substTy_def, Ty.subst_def, mapVal, map_cons, Binding.substTy,
      cons_append, openTm_substTy_var] using
      ih₂ x hx (Γ := ⟨x, .ty _⟩ :: Γ) rfl
  | inl der hτ ih =>
    subst eq
    exact inl (ih rfl)
      (Ty.Wf.map_subst hτ sub.wf.2.1 (Env.Wf.map_subst der.wf.1 sub.wf.2.1).to_ok)
  | inr der hσ ih =>
    subst eq
    exact inr (ih rfl)
      (Ty.Wf.map_subst hσ sub.wf.2.1 (Env.Wf.map_subst der.wf.1 sub.wf.2.1).to_ok)
  | case L _ _ _ ih₁ ih₂ ih₃ =>
    subst eq
    apply case L (ih₁ rfl)
    · intro x hx
      simpa only [Term.substTy_def, Ty.subst_def, mapVal, map_cons, Binding.substTy,
        cons_append, openTm_substTy_var] using
        ih₂ x hx (Γ := ⟨x, .ty _⟩ :: Γ) rfl
    · intro x hx
      simpa only [Term.substTy_def, Ty.subst_def, mapVal, map_cons, Binding.substTy,
        cons_append, openTm_substTy_var] using
        ih₃ x hx (Γ := ⟨x, .ty _⟩ :: Γ) rfl

open Term Ty

omit [HasFresh Var]

/-- Invert the typing of an abstraction. -/
lemma abs_inv (der : Typing Γ (.abs γ' t) τ) (sub : Sub Γ τ (arrow γ δ)) :
     Sub Γ γ γ'
  ∧ ∃ δ' L, ∀ x ∉ (L : Finset Var),
    Typing (⟨x, Binding.ty γ'⟩ :: Γ) (t ^ᵗᵗ .fvar x) δ' ∧ Sub Γ δ' δ := by
  generalize eq : Term.abs γ' t = e at der
  induction der generalizing t γ' γ δ with
  | abs L der _ =>
    cases eq
    cases sub with
    | arrow hdom hcod => exact ⟨hdom, _, L, fun x hx => ⟨der x hx, hcod⟩⟩
  | sub _ hsub ih => exact ih (Sub.trans hsub sub) eq
  | _ => cases eq

variable [HasFresh Var] in
/-- Invert the typing of a type abstraction. -/
lemma tabs_inv (der : Typing Γ (.tabs γ' t) τ) (sub : Sub Γ τ (all γ δ)) :
     Sub Γ γ γ'
  ∧ ∃ δ' L, ∀ X ∉ (L : Finset Var),
     Typing (⟨X, Binding.sub γ⟩ :: Γ) (t ^ᵗᵞ fvar X) (δ' ^ᵞ fvar X)
     ∧ Sub (⟨X, Binding.sub γ⟩ :: Γ) (δ' ^ᵞ fvar X) (δ ^ᵞ fvar X) := by
  generalize eq : Term.tabs γ' t = e at der
  induction der generalizing γ δ t γ' with
  | @tabs σ Γ t τ L der _ =>
    cases eq
    cases sub with
    | all L' hdom hcod =>
      refine ⟨hdom, τ, L ∪ L', ?_⟩
      intro X hX
      simp only [Finset.mem_union, not_or] at hX
      exact ⟨narrow (Γ := []) hdom (der X hX.1), hcod X hX.2⟩
  | sub _ hsub ih => exact ih (Sub.trans hsub sub) eq
  | _ => cases eq

/-- Invert the typing of a left case. -/
lemma inl_inv (der : Typing Γ (.inl t) τ) (sub : Sub Γ τ (sum γ δ)) :
    ∃ γ', Typing Γ t γ' ∧ Sub Γ γ' γ := by
  generalize eq : t.inl = e at der
  induction der generalizing γ δ with
  | inl der _ _ =>
    cases eq
    cases sub with
    | sum hleft hright => exact ⟨_, der, hleft⟩
  | sub _ hsub ih => exact ih (Sub.trans hsub sub) eq
  | _ => cases eq

/-- Invert the typing of a right case. -/
lemma inr_inv (der : Typing Γ (.inr t) T) (sub : Sub Γ T (sum γ δ)) :
    ∃ δ', Typing Γ t δ' ∧ Sub Γ δ' δ := by
  generalize eq : t.inr = e at der
  induction der generalizing γ δ with
  | inr der _ _ =>
    cases eq
    cases sub with
    | sum hleft hright => exact ⟨_, der, hright⟩
  | sub _ hsub ih => exact ih (Sub.trans hsub sub) eq
  | _ => cases eq

/-- A value that types as a function is an abstraction. -/
lemma canonical_form_abs (val : Value t) (der : Typing [] t (arrow σ τ)) :
    ∃ δ t', t = .abs δ t' := by
  generalize eq : σ.arrow τ = γ at der
  generalize eq' : [] = Γ at der
  induction der generalizing σ τ with
  | sub _ hsub ih =>
    cases eq
    cases eq'
    cases hsub with
    | trans_tvar mem _ => simp at mem
    | arrow _ _ => exact ih val rfl rfl
  | _ => cases val <;> cases eq <;> simp_all

/-- A value that types as a quantifier is a type abstraction. -/
lemma canonical_form_tabs (val : Value t) (der : Typing [] t (all σ τ)) :
    ∃ δ t', t = .tabs δ t' := by
  generalize eq : σ.all τ = γ at der
  generalize eq' : [] = Γ at der
  induction der generalizing σ τ with
  | sub _ hsub ih =>
    cases eq
    cases eq'
    cases hsub with
    | trans_tvar mem _ => simp at mem
    | all L _ _ => exact ih val rfl rfl
  | _ => cases val <;> cases eq <;> simp_all

/-- A value that types as a sum is a left or right case. -/
lemma canonical_form_sum (val : Value t) (der : Typing [] t (sum σ τ)) :
    ∃ t', t = .inl t' ∨ t = .inr t' := by
  generalize eq : σ.sum τ = γ at der
  generalize eq' : [] = Γ at der
  induction der generalizing σ τ with
  | sub _ hsub ih =>
    cases eq
    cases eq'
    cases hsub with
    | trans_tvar mem _ => simp at mem
    | sum _ _ => exact ih val rfl rfl
  | _ => cases val <;> cases eq <;> simp_all

end Typing

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
