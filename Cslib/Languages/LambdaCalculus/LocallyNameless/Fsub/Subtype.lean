/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.WellFormed

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines the subtyping relation.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

@[expose] public section

namespace Cslib

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

variable {Γ Δ Θ : Env Var} {σ τ δ : Ty Var}

/-- Subtypes have well-formed contexts and types. -/
lemma wf (Γ : Env Var) (σ σ' : Ty Var) (sub : Sub Γ σ σ') : Γ.Wf ∧ σ.Wf Γ ∧ σ'.Wf Γ := by
  induction sub with
  | top wfΓ wfσ => exact ⟨wfΓ, wfσ, .top⟩
  | refl_tvar wfΓ wfσ => exact ⟨wfΓ, wfσ, wfσ⟩
  | trans_tvar mem _ ih => exact ⟨ih.1, .var mem, ih.2.2⟩
  | arrow _ _ ihσ ihτ => exact ⟨ihσ.1, .arrow ihσ.2.2 ihτ.2.1, .arrow ihσ.2.1 ihτ.2.2⟩
  | sum _ _ ihσ ihτ => exact ⟨ihσ.1, .sum ihσ.2.1 ihτ.2.1, .sum ihσ.2.2 ihτ.2.2⟩
  | @all Γ σ σ' τ' τ L _ _ ihσ ihτ =>
    refine ⟨ihσ.1, .all (L ∪ Γ.dom) ihσ.2.2 ?_, .all L ihσ.2.1 ?_⟩
    · intro X fresh
      simp only [Finset.mem_union, not_or] at fresh
      exact (ihτ X fresh.1).2.1.narrow_cons
        (Env.Wf.sub ihσ.1 ihσ.2.2 fresh.2).to_ok
    · intro X fresh
      exact (ihτ X fresh).2.2

/-- Subtypes are reflexive when well-formed. -/
lemma refl (wf_Γ : Γ.Wf) (wf_σ : σ.Wf Γ) : Sub Γ σ σ := by
  induction wf_σ with
  | top => exact top wf_Γ .top
  | var mem => exact refl_tvar wf_Γ (.var mem)
  | arrow _ _ ihσ ihτ => exact arrow (ihσ wf_Γ) (ihτ wf_Γ)
  | sum _ _ ihσ ihτ => exact sum (ihσ wf_Γ) (ihτ wf_Γ)
  | @all Γ σ τ L wfσ _ ihσ ihτ =>
    apply all (L ∪ Γ.dom) (ihσ wf_Γ)
    intro X fresh
    simp only [Finset.mem_union, not_or] at fresh
    exact ihτ X fresh.1 (Env.Wf.sub wf_Γ wfσ fresh.2)

/-- Weakening of subtypes. -/
lemma weaken (sub : Sub (Γ ++ Θ) σ σ') (wf : (Γ ++ Δ ++ Θ).Wf) : Sub (Γ ++ Δ ++ Θ) σ σ' := by
  generalize eq : Γ ++ Θ = ΓΘ at sub
  induction sub generalizing Γ with
  | top _ wfσ => subst eq; exact top wf (wfσ.weaken wf.to_ok)
  | refl_tvar _ wfσ => subst eq; exact refl_tvar wf (wfσ.weaken wf.to_ok)
  | trans_tvar mem _ ih =>
    subst eq
    apply trans_tvar ?_ (ih wf rfl)
    apply mem_dlookup wf.to_ok
    rcases mem_append.mp (of_mem_dlookup mem) with mem | mem
    · exact mem_append_left _ (mem_append_left _ mem)
    · exact mem_append_right _ mem
  | arrow _ _ ihσ ihτ => exact arrow (ihσ wf eq) (ihτ wf eq)
  | sum _ _ ihσ ihτ => exact sum (ihσ wf eq) (ihτ wf eq)
  | @all ΓΘ σ σ' τ' τ L subσ _ ihσ ihτ =>
    subst ΓΘ
    apply all (L ∪ (Γ ++ Δ ++ Θ).dom) (ihσ wf rfl)
    intro X fresh
    simp only [Finset.mem_union, not_or] at fresh
    exact ihτ X fresh.1 (Γ := ⟨X, Binding.sub σ⟩ :: Γ)
      (Env.Wf.sub wf ((subσ.wf ..).2.1.weaken wf.to_ok) fresh.2) rfl

lemma weaken_head (sub : Sub Δ σ σ') (wf : (Γ ++ Δ).Wf) : Sub (Γ ++ Δ) σ σ' := by
  exact weaken (Γ := []) sub wf

lemma narrow_aux
    (trans : ∀ Γ σ τ, Sub Γ σ δ → Sub Γ δ τ → Sub Γ σ τ)
    (sub₁ : Sub (Γ ++ ⟨X, Binding.sub δ⟩ :: Δ) σ τ) (sub₂ : Sub Δ δ' δ) :
      Sub (Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ) σ τ := by
  generalize eq : Γ ++ ⟨X, Binding.sub δ⟩ :: Δ = Θ at sub₁
  induction sub₁ generalizing Γ δ with
  | top wfΓ wfσ =>
    subst eq
    have wf := wfΓ.narrow (sub₂.wf ..).2.1
    exact top wf (wfσ.narrow wf.to_ok)
  | refl_tvar wfΓ wfσ =>
    subst eq
    have wf := wfΓ.narrow (sub₂.wf ..).2.1
    exact refl_tvar wf (wfσ.narrow wf.to_ok)
  | @trans_tvar σ Θ σ' Y mem sub ih =>
    subst Θ
    have wf := (sub.wf ..).1.narrow (sub₂.wf ..).2.1
    have narrowed := ih trans sub₂ rfl
    by_cases heq : Y = X
    · subst Y
      have eqσ : σ = δ := Binding.sub.inj ((sub.wf ..).1.to_ok.eq_of_mk_mem
        (of_mem_dlookup mem) (mem_append_right _ (mem_cons_self ..)))
      subst σ
      apply trans_tvar (σ := δ')
      · exact mem_dlookup wf.to_ok (mem_append_right _ (mem_cons_self ..))
      · apply trans _ _ _ ?_ narrowed
        change Sub (Γ ++ ([⟨X, Binding.sub δ'⟩] ++ Δ)) δ' δ
        rw [← append_assoc]
        exact weaken_head sub₂ (by simpa only [append_assoc, singleton_append] using wf)
    · apply trans_tvar (σ := σ) ?_ narrowed
      apply mem_dlookup wf.to_ok
      rcases mem_append.mp (of_mem_dlookup mem) with mem | mem
      · exact mem_append_left _ mem
      · rcases mem_cons.mp mem with heq' | mem
        · cases heq'; exact (heq rfl).elim
        · exact mem_append_right _ (mem_cons_of_mem _ mem)
  | arrow _ _ ihσ ihτ => exact arrow (ihσ trans sub₂ eq) (ihτ trans sub₂ eq)
  | sum _ _ ihσ ihτ => exact sum (ihσ trans sub₂ eq) (ihτ trans sub₂ eq)
  | @all Θ σ σ' τ' τ L _ _ ihσ ihτ =>
    subst Θ
    apply all L (ihσ trans sub₂ rfl)
    intro Y fresh
    exact ihτ Y fresh (Γ := ⟨Y, Binding.sub σ⟩ :: Γ) trans sub₂ rfl

lemma trans : Sub Γ σ δ → Sub Γ δ τ → Sub Γ σ τ := by
  intro sub₁ sub₂
  have δ_lc : δ.LC := (sub₁.wf ..).2.2.lc
  induction δ_lc generalizing Γ σ τ with
  | top =>
    cases sub₂ with
    | top wf _ => exact top wf (sub₁.wf ..).2.1
  | @var X =>
    generalize eq : fvar X = γ at sub₁
    induction sub₁ with
    | refl_tvar => cases eq; exact sub₂
    | trans_tvar mem _ ih => exact trans_tvar mem (ih sub₂ eq)
    | _ => cases eq
  | @arrow σ' τ' _ _ ihσ ihτ =>
    generalize eq : σ'.arrow τ' = γ at sub₁
    induction sub₁ with
    | trans_tvar mem _ ih => exact trans_tvar mem (ih sub₂ eq)
    | arrow subσ subτ _ _ =>
      cases eq
      cases sub₂ with
      | top wf _ => exact top wf (Sub.arrow subσ subτ |>.wf ..).2.1
      | arrow subσ' subτ' => exact arrow (ihσ subσ' subσ) (ihτ subτ subτ')
    | _ => cases eq
  | @sum σ' τ' _ _ ihσ ihτ =>
    generalize eq : σ'.sum τ' = γ at sub₁
    induction sub₁ with
    | trans_tvar mem _ ih => exact trans_tvar mem (ih sub₂ eq)
    | sum subσ subτ _ _ =>
      cases eq
      cases sub₂ with
      | top wf _ => exact top wf (Sub.sum subσ subτ |>.wf ..).2.1
      | sum subσ' subτ' => exact sum (ihσ subσ subσ') (ihτ subτ subτ')
    | _ => cases eq
  | @all σ' τ' L _ _ ihσ ihτ =>
    generalize eq : Ty.all σ' τ' = γ at sub₁
    induction sub₁ with
    | trans_tvar mem _ ih => exact trans_tvar mem (ih sub₂ eq)
    | all L₁ subσ subτ _ _ =>
      cases eq
      cases sub₂ with
      | top wf _ => exact top wf (Sub.all L₁ subσ subτ |>.wf ..).2.1
      | all L₂ subσ' subτ' =>
        apply all (L ∪ L₁ ∪ L₂) (ihσ subσ' subσ)
        intro X fresh
        simp only [Finset.mem_union, not_or] at fresh
        apply ihτ X fresh.1.1 ?_ (subτ' X fresh.2)
        exact narrow_aux (Γ := []) (fun Γ σ τ => @ihσ Γ σ τ)
          (subτ X fresh.1.2) subσ'
    | _ => cases eq

instance (Γ : Env Var) : Trans (Sub Γ) (Sub Γ) (Sub Γ) :=
  ⟨Sub.trans⟩

/-- Narrowing of subtypes. -/
lemma narrow (sub_δ : Sub Δ δ δ') (sub_narrow : Sub (Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ) σ τ) :
    Sub (Γ ++ ⟨X, Binding.sub δ⟩ :: Δ) σ τ := by
  exact narrow_aux (fun _ _ _ => Sub.trans) sub_narrow sub_δ

variable [HasFresh Var] in
/-- Subtyping of substitutions. -/
lemma map_subst (sub₁ : Sub (Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ) σ τ) (sub₂ : Sub Δ δ δ') :
    Sub (Γ.mapVal (·[X := δ]) ++ Δ) (σ[X := δ]) (τ[X := δ]) := by
  have wfδ := (Sub.wf _ _ _ sub₂).2.1
  generalize eq : Γ ++ ⟨X, Binding.sub δ'⟩ :: Δ = Θ at sub₁
  induction sub₁ generalizing Γ with
  | top wf wfσ =>
    subst eq
    have wf' := wf.map_subst wfδ
    exact Sub.top wf' (wfσ.map_subst wfδ wf'.to_ok)
  | refl_tvar wf wfσ =>
    subst eq
    have wf' := wf.map_subst wfδ
    exact Sub.refl wf' (wfσ.map_subst wfδ wf'.to_ok)
  | @trans_tvar σ Θ τ Y mem sub ih =>
    subst eq
    have wf := (Sub.wf _ _ _ sub).1
    have wf' := wf.map_subst wfδ
    have ok := wf.to_ok
    by_cases heq : Y = X
    · subst Y
      have hσ : σ = δ' := Binding.sub.inj
        (ok.eq_of_mk_mem (of_mem_dlookup mem) (mem_append_right _ (mem_cons_self ..)))
      subst σ
      have fresh : X ∉ Δ.dom := by
        have h := (nodupKeys_cons.mp (nodupKeys_middle.mp ok)).1
        simp only [keys_append, mem_append, not_or] at h
        simpa using h.2
      have hδ' := Ty.subst_fresh ((Sub.wf _ _ _ sub₂).2.2.nmem_fv fresh) δ
      simpa [← Ty.subst_def, Ty.subst] using
        Sub.trans (Sub.weaken_head sub₂ wf') (hδ' ▸ ih rfl)
    · change Sub _ (Ty.subst X δ (fvar Y)) _
      rw [Ty.subst, ite_eq_right heq]
      apply Sub.trans_tvar (σ := σ[X := δ]) ?_ (ih rfl)
      apply mem_dlookup wf'.to_ok
      rcases mem_append.mp (of_mem_dlookup mem) with h | h
      · exact mem_append_left _ (mem_map.mpr ⟨⟨Y, Binding.sub σ⟩, h, rfl⟩)
      · rcases mem_cons.mp h with h | h
        · cases h
          exact (heq rfl).elim
        · have fresh : X ∉ Δ.dom := by
            have h := (nodupKeys_cons.mp (nodupKeys_middle.mp ok)).1
            simp only [keys_append, mem_append, not_or] at h
            simpa using h.2
          have mapped := mapVal_mem (mem_dlookup (Sub.wf _ _ _ sub₂).1.to_ok h)
            (fun b : Binding Var => b[X := δ])
          rw [← map_subst_nmem Δ X δ (Sub.wf _ _ _ sub₂).1 fresh] at mapped
          exact mem_append_right _ (of_mem_dlookup mapped)
  | arrow _ _ ihσ ihτ => exact Sub.arrow (ihσ eq) (ihτ eq)
  | sum _ _ ihσ ihτ => exact Sub.sum (ihσ eq) (ihτ eq)
  | @all Θ σ σ' τ' τ L _ _ ihσ ihτ =>
    subst eq
    apply Sub.all (L ∪ {X}) (ihσ rfl)
    intro Y hY
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hY
    change Sub _ ((τ'[X := δ]) ^ᵞ fvar Y) ((τ[X := δ]) ^ᵞ fvar Y)
    rw [← open_subst_var τ' hY.2 wfδ.lc, ← open_subst_var τ hY.2 wfδ.lc]
    exact ihτ Y hY.1 (Γ := ⟨Y, Binding.sub σ⟩ :: Γ) rfl

/-- Strengthening of subtypes. -/
lemma strengthen (sub : Sub (Γ ++ ⟨X, Binding.ty δ⟩ :: Δ) σ τ) :  Sub (Γ ++ Δ) σ τ := by
  generalize eq : Γ ++ ⟨X, Binding.ty δ⟩ :: Δ = Θ at sub
  induction sub generalizing Γ with
  | top wf wfσ => subst eq; exact Sub.top wf.strengthen wfσ.strengthen
  | refl_tvar wf wfσ => subst eq; exact Sub.refl_tvar wf.strengthen wfσ.strengthen
  | @trans_tvar σ Θ τ Y mem sub ih =>
    subst eq
    apply Sub.trans_tvar (σ := σ) ?_ (ih rfl)
    apply mem_dlookup (Env.Wf.strengthen (Sub.wf _ _ _ sub).1).to_ok
    rcases mem_append.mp (of_mem_dlookup mem) with h | h
    · exact mem_append_left _ h
    · rcases mem_cons.mp h with h | h
      · cases h
      · exact mem_append_right _ h
  | arrow _ _ ihσ ihτ => exact Sub.arrow (ihσ eq) (ihτ eq)
  | sum _ _ ihσ ihτ => exact Sub.sum (ihσ eq) (ihτ eq)
  | all L _ _ ihσ ihτ =>
    subst eq
    apply Sub.all L (ihσ rfl)
    intro Y hY
    exact ihτ Y hY (Γ := ⟨Y, _⟩ :: Γ) rfl

end Sub

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
