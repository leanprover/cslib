/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Opening

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines the well-formedness condition for types and contexts.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

@[expose] public section

namespace Cslib

variable {Var : Type*} [DecidableEq Var]

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

/-- An environment is well-formed if it binds each variable exactly once to a well-formed type. -/
inductive Env.Wf : Env Var → Prop
  | empty : Wf []
  | sub : Wf Γ → τ.Wf Γ → X ∉ Γ.dom → Wf (⟨X, Binding.sub τ⟩ :: Γ)
  | ty : Wf Γ → τ.Wf Γ → x ∉ Γ.dom → Wf (⟨x, Binding.ty τ⟩ :: Γ)

variable {Γ Δ Θ : Env Var} {σ τ τ' γ δ : Ty Var}

open scoped Context in
/-- A well-formed context contains no duplicate keys. -/
lemma Env.Wf.to_ok {Γ : Env Var} (wf : Γ.Wf) : Γ✓ := by
  induction wf with
  | empty => exact List.nodupKeys_nil
  | sub _ _ fresh ih | ty _ _ fresh ih =>
    exact List.nodupKeys_cons.mpr ⟨by simpa using fresh, ih⟩

namespace Ty.Wf

open Context List Binding
open scoped Env.Wf

/-- A well-formed type is locally closed. -/
theorem lc (wf : σ.Wf Γ) : σ.LC := by
  induction wf with
  | top => exact LC.top
  | var => exact LC.var
  | arrow _ _ ihσ ihτ => exact LC.arrow ihσ ihτ
  | sum _ _ ihσ ihτ => exact LC.sum ihσ ihτ
  | all L _ _ ihσ ihτ => exact LC.all L ihσ ihτ

private lemma of_lookup (wf : σ.Wf Γ)
    (lookup : ∀ X τ, sub τ ∈ Γ.dlookup X → ∃ δ, sub δ ∈ Δ.dlookup X) : σ.Wf Δ := by
  induction wf generalizing Δ with
  | top => exact top
  | var mem => obtain ⟨δ, mem⟩ := lookup _ _ mem; exact var mem
  | arrow _ _ ihσ ihτ => exact arrow (ihσ lookup) (ihτ lookup)
  | sum _ _ ihσ ihτ => exact sum (ihσ lookup) (ihτ lookup)
  | @all Γ σ τ L _ _ ihσ ihτ =>
    refine all L (ihσ lookup) fun X fresh => ihτ X fresh ?_
    intro Y γ mem
    by_cases eq : Y = X
    · subst Y
      exact ⟨σ, by simp⟩
    · obtain ⟨δ, hδ⟩ := lookup Y γ (by simpa [dlookup, Ne.symm eq] using mem)
      exact ⟨δ, by simpa [dlookup, Ne.symm eq] using hδ⟩

/-- A type remains well-formed under context permutation. -/
theorem perm_env (wf : σ.Wf Γ) (perm : Γ ~ Δ) (ok_Γ : Γ✓) (ok_Δ : Δ✓) : σ.Wf Δ := by
  apply of_lookup wf
  intro X τ mem
  rw [perm_dlookup X ok_Γ perm] at mem
  exact ⟨τ, mem_dlookup ok_Δ (of_mem_dlookup mem)⟩

/-- A type remains well-formed under context weakening (in the middle). -/
theorem weaken (wf_ΓΘ : σ.Wf (Γ ++ Θ)) (ok_ΓΔΘ : (Γ ++ Δ ++ Θ)✓) : σ.Wf (Γ ++ Δ ++ Θ) := by
  apply of_lookup wf_ΓΘ
  intro X τ mem
  exact ⟨τ, mem_dlookup ok_ΓΔΘ (by
    simpa only [mem_append, or_assoc] using
      (mem_append.mp (of_mem_dlookup mem)).elim
        (fun h => Or.inl h) (fun h => Or.inr (Or.inr h)))⟩

/-- A type remains well-formed under context weakening (at the front). -/
theorem weaken_head (wf : σ.Wf Δ) (ok : (Γ ++ Δ)✓) : σ.Wf (Γ ++ Δ) := by
  exact weaken (Γ := []) wf ok

theorem weaken_cons (wf : σ.Wf Δ) (ok : (⟨X, b⟩ :: Δ)✓) : σ.Wf (⟨X, b⟩:: Δ) := by
  exact weaken_head (Γ := [⟨X, b⟩]) wf ok

/-- A type remains well-formed under context narrowing. -/
lemma narrow (wf : σ.Wf (Γ ++ ⟨X, Binding.sub τ⟩ :: Δ)) (ok : (Γ ++ ⟨X, Binding.sub τ'⟩ :: Δ)✓) :
    σ.Wf (Γ ++ ⟨X, Binding.sub τ'⟩ :: Δ) := by
  apply of_lookup wf
  intro Y γ mem
  rcases mem_append.mp (of_mem_dlookup mem) with mem | mem
  · exact ⟨γ, mem_dlookup ok (mem_append_left _ mem)⟩
  · rcases mem_cons.mp mem with eq | mem
    · cases eq
      exact ⟨τ', mem_dlookup ok (mem_append_right _ (mem_cons_self ..))⟩
    · exact ⟨γ, mem_dlookup ok (mem_append_right _ (mem_cons_of_mem _ mem))⟩

lemma narrow_cons (wf : σ.Wf (⟨X, Binding.sub τ⟩ :: Δ)) (ok : (⟨X, Binding.sub τ'⟩ :: Δ)✓) :
    σ.Wf (⟨X, Binding.sub τ'⟩ :: Δ) := by
  exact narrow (Γ := []) wf ok

/-- A type remains well-formed under context strengthening. -/
lemma strengthen (wf : σ.Wf (Γ ++ ⟨X, Binding.ty τ⟩ :: Δ)) : σ.Wf (Γ ++ Δ) := by
  apply of_lookup wf
  intro Y γ mem
  clear wf
  induction Γ with
  | nil =>
    by_cases eq : Y = X
    · subst Y; simp at mem
    · exact ⟨γ, by simpa [dlookup, Ne.symm eq] using mem⟩
  | cons binding Γ ih =>
    by_cases eq : Y = binding.1
    · subst Y
      rcases binding with ⟨Y, b⟩
      exact ⟨γ, by simpa using mem⟩
    · simpa [dlookup_cons_ne _ binding eq] using ih (by
        simpa [dlookup_cons_ne _ binding eq] using mem)

variable [HasFresh Var] in
/-- A type remains well-formed under context substitution (of a well-formed type). -/
lemma map_subst (wf_σ : σ.Wf (Γ ++ ⟨X, Binding.sub τ⟩ :: Δ)) (wf_τ' : τ'.Wf Δ)
    (ok : (Γ.mapVal (·[X := τ']) ++ Δ)✓) : σ[X := τ'].Wf <| Γ.mapVal (·[X := τ']) ++ Δ := by
  generalize eq : Γ ++ ⟨X, Binding.sub τ⟩ :: Δ = Θ at wf_σ
  induction wf_σ generalizing Γ with
  | top => exact top
  | @var γ Θ Y mem =>
    subst Θ
    by_cases heq : Y = X
    · subst Y
      simpa [← subst_def, subst] using wf_τ'.weaken_head ok
    · simp only [← subst_def, subst, ite_eq_right heq]
      rcases mem_append.mp (of_mem_dlookup mem) with mem | mem
      · apply var (σ := γ[X := τ'])
        apply mem_dlookup ok
        apply mem_append_left
        exact mem_map.mpr ⟨⟨Y, sub γ⟩, mem, rfl⟩
      · rcases mem_cons.mp mem with heq' | mem
        · cases heq'; exact (heq rfl).elim
        · exact var (mem_dlookup ok (mem_append_right _ mem))
  | arrow _ _ ihσ ihτ => exact arrow (ihσ ok eq) (ihτ ok eq)
  | sum _ _ ihσ ihτ => exact sum (ihσ ok eq) (ihτ ok eq)
  | @all Θ σ γ L _ _ ihσ ihγ =>
    subst Θ
    apply all (L ∪ (Γ.mapVal (·[X := τ']) ++ Δ).dom ∪ {X}) (ihσ ok rfl)
    intro Y fresh
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at fresh
    change Wf _ ((γ[X := τ']) ^ᵞ fvar Y)
    rw [← open_subst_var γ fresh.2 wf_τ'.lc]
    apply ihγ Y fresh.1.1 (Γ := ⟨Y, sub σ⟩ :: Γ)
    · exact nodupKeys_cons.mpr ⟨by simpa using fresh.1.2, ok⟩
    · rfl

variable [HasFresh Var] in
/-- A type remains well-formed under opening (to a well-formed type). -/
lemma open_lc (ok_Γ : Γ✓) (wf_all : (Ty.all σ τ).Wf Γ) (wf_δ : δ.Wf Γ) : (τ ^ᵞ δ).Wf Γ := by
  cases wf_all with
  | all L _ body =>
    obtain ⟨X, fresh⟩ := fresh_exists (L ∪ τ.fv)
    simp only [Finset.mem_union, not_or] at fresh
    rw [open_subst_intro δ fresh.2]
    exact map_subst (Γ := []) (body X fresh.1) wf_δ ok_Γ

/-- A type bound in a context is well formed. -/
lemma of_bind_ty (wf : Γ.Wf) (bind : Binding.ty σ ∈ Γ.dlookup X) : σ.Wf Γ := by
  induction wf with
  | empty => simp at bind
  | @sub Γ Y τ wfΓ wfτ fresh ih =>
    by_cases eq : X = Y
    · subst X; simp at bind
    · exact (ih (by simpa [dlookup, Ne.symm eq] using bind)).weaken_cons
        (Env.Wf.sub wfΓ wfτ fresh).to_ok
  | @ty Γ Y τ wfΓ wfτ fresh ih =>
    have ok := (Env.Wf.ty wfΓ wfτ fresh).to_ok
    by_cases eq : X = Y
    · subst X
      simp only [dlookup_cons_eq, Option.mem_some_iff, Binding.ty.injEq] at bind
      subst τ
      exact wfτ.weaken_cons ok
    · exact (ih (by simpa [dlookup, Ne.symm eq] using bind)).weaken_cons ok

/-- A type at the head of a well-formed context is well-formed. -/
lemma of_env_ty (wf : Env.Wf (⟨X, Binding.ty σ⟩ :: Γ)) : σ.Wf Γ := by
  cases wf
  assumption

/-- A subtype at the head of a well-formed context is well-formed. -/
lemma of_env_sub (wf : Env.Wf (⟨X, Binding.sub σ⟩ :: Γ)) : σ.Wf Γ := by
  cases wf
  assumption

variable [HasFresh Var] in
/-- A variable not appearing in a context does not appear in its well-formed types. -/
lemma nmem_fv {σ : Ty Var} (wf : σ.Wf Γ) (nmem : X ∉ Γ.dom) : X ∉ σ.fv := by
  induction wf with
  | top => simp [Ty.fv]
  | @var τ Γ Y mem =>
    have keys := mem_keys_of_mem (of_mem_dlookup mem)
    simp only [Ty.fv, Finset.mem_singleton]
    intro eq
    subst Y
    exact nmem (by simpa using keys)
  | arrow _ _ ihσ ihτ | sum _ _ ihσ ihτ =>
    exact Finset.notMem_union.mpr ⟨ihσ nmem, ihτ nmem⟩
  | @all Γ σ τ L _ _ ihσ ihτ =>
    obtain ⟨Y, fresh⟩ := fresh_exists (L ∪ {X})
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at fresh
    apply Finset.notMem_union.mpr ⟨ihσ nmem, ?_⟩
    apply nmem_fv_open (ihτ Y fresh.1 ?_)
    simpa [eq_comm] using And.intro fresh.2 nmem

end Ty.Wf

namespace Env.Wf

open Context List Binding

/-- A context remains well-formed under narrowing (of a well-formed subtype). -/
lemma narrow (wf_env : Env.Wf (Γ ++ ⟨X, Binding.sub τ⟩ :: Δ)) (wf_τ' : τ'.Wf Δ) :
    Env.Wf (Γ ++ ⟨X, Binding.sub τ'⟩ :: Δ) := by
  induction Γ with
  | nil => cases wf_env with | sub wf _ fresh => exact sub wf wf_τ' fresh
  | cons binding Γ ih =>
    cases wf_env with
    | sub wf wfτ fresh =>
      exact sub (ih wf) (wfτ.narrow (ih wf).to_ok) (by simpa using fresh)
    | ty wf wfτ fresh =>
      exact ty (ih wf) (wfτ.narrow (ih wf).to_ok) (by simpa using fresh)

/-- A context remains well-formed under strengthening. -/
lemma strengthen (wf : Env.Wf <| Γ ++ ⟨X, Binding.ty τ⟩ :: Δ) : Env.Wf <| Γ ++ Δ := by
  induction Γ with
  | nil => cases wf with | ty wf _ _ => exact wf
  | cons binding Γ ih =>
    cases wf with
    | sub wf wfτ fresh =>
      exact sub (ih wf) wfτ.strengthen (by simp_all)
    | ty wf wfτ fresh =>
      exact ty (ih wf) wfτ.strengthen (by simp_all)

variable [HasFresh Var] in
/-- A context remains well-formed under substitution (of a well-formed type). -/
lemma map_subst (wf_env : Env.Wf (Γ ++ ⟨X, Binding.sub τ⟩ :: Δ)) (wf_τ' : τ'.Wf Δ) :
    Env.Wf <| Γ.mapVal (·[X := τ']) ++ Δ := by
  induction Γ with
  | nil => cases wf_env with | sub wf _ _ => exact wf
  | cons binding Γ ih =>
    cases wf_env with
    | sub wf wfτ fresh =>
      refine sub (ih wf) (wfτ.map_subst wf_τ' (ih wf).to_ok) ?_
      change _ ∉ dom (mapVal (·[X := τ']) Γ ++ Δ)
      change _ ∉ dom (Γ ++ ⟨X, Binding.sub τ⟩ :: Δ) at fresh
      simp only [dom, keys_append, ← mapVal_keys, mem_toFinset, mem_append, not_or]
      simp only [dom, keys_append, keys_cons, mem_toFinset, mem_append, mem_cons, not_or] at fresh
      exact ⟨fresh.1, fresh.2.2⟩
    | ty wf wfτ fresh =>
      refine ty (ih wf) (wfτ.map_subst wf_τ' (ih wf).to_ok) ?_
      change _ ∉ dom (mapVal (·[X := τ']) Γ ++ Δ)
      change _ ∉ dom (Γ ++ ⟨X, Binding.sub τ⟩ :: Δ) at fresh
      simp only [dom, keys_append, ← mapVal_keys, mem_toFinset, mem_append, not_or]
      simp only [dom, keys_append, keys_cons, mem_toFinset, mem_append, mem_cons, not_or] at fresh
      exact ⟨fresh.1, fresh.2.2⟩

variable [HasFresh Var]

/-- A well-formed context is unchanged by substituting for a free key. -/
lemma map_subst_nmem (Γ : Env Var) (X : Var) (σ : Ty Var) (wf : Γ.Wf) (nmem : X ∉ Γ.dom) :
    Γ = Γ.mapVal (·[X := σ]) := by
  induction wf with
  | empty => rfl
  | sub wf wfτ fresh ih | ty wf wfτ fresh ih =>
    simp only [dom, keys_cons, mem_toFinset, mem_cons, not_or] at nmem
    exact congrArg₂ List.cons
      (congrArg (Sigma.mk _) (Binding.subst_fresh (wfτ.nmem_fv (by simpa using nmem.2)) σ))
      (ih (by simpa using nmem.2))

end Env.Wf

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
