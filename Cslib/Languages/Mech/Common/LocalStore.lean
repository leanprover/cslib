/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Syntax.HasSubstitution
public import Cslib.Languages.Mech.Common.Basic
public import Mathlib.Data.Finset.Defs

/-! # Local stores -/

@[expose] public section

namespace Cslib.Mech

namespace LocalSig

/-- A local store. -/
def Store (L : LocalSig) := (x : L.VarName) → L.VarType x

/-- Read a typed variable in a local store. Results are stated with the notation `σ[x]`. -/
def Store.read {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) : α :=
  x.has_type.mp (σ x.name)

/-- Write a typed variable in a local store. Results are stated with the notation `σ[x := v]`. -/
def Store.write {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) (v : α) : L.Store :=
  Function.update σ x.name (x.has_type.mpr v)

/-! ### Notation for local stores

A store `σ` is read with `σ[x]` and written with `σ[x := v]`. -/

/-- For any local store `σ`, `σ[x]` is the value of the variable `x` in `σ`. -/
instance Store.instGetElem {L : LocalSig} {α} : GetElem L.Store (L.Var α) α (fun _ _ => True) where
  getElem σ x _ := σ.read x

/-- For any local store `σ`, `σ[x := v]` is the store obtained from `σ` by writing `v` in `x`. -/
instance Store.instHasSubstitution {L : LocalSig} {α} : HasSubstitution L.Store (L.Var α) α where
  subst σ x v := σ.write x v

@[simp, grind =]
theorem Store.read_def {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) :
    σ.read x = σ[x] := rfl

@[simp, grind =]
theorem Store.write_def {L : LocalSig} {α} (σ : L.Store) (x : L.Var α)
    (v : α) : σ.write x v = σ[x := v] := rfl

/-- Two stores are equal if they agree on every read. -/
@[ext, grind ext]
theorem Store.ext {L : LocalSig} {σ₁ σ₂ : L.Store} (h : ∀ α (x : L.Var α), σ₁[x] = σ₂[x]) :
    σ₁ = σ₂ :=
  funext fun y => h _ ⟨y, rfl⟩

/-- The value of a written store at a variable name. -/
theorem Store.subst_apply {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) (v : α) (y : L.VarName) :
    σ[x := v] y = if h : y = x.name then h ▸ x.has_type.mpr v else σ y := by
  split <;> rename_i h
  · subst h
    exact Function.update_self ..
  · exact Function.update_of_ne h ..

/-- Writing a variable preserves the values of all other names. -/
theorem Store.subst_apply_of_ne {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) (v : α)
    {y : L.VarName} (h : y ≠ x.name) : σ[x := v] y = σ y := by
  rw [subst_apply, dite_eq_right h]

/-- Reading a variable after a write. If the variable read has the name of the variable written,
their types are equal and the written value is returned. -/
@[grind =]
theorem Store.getElem_subst {L : LocalSig} {α β} (σ : L.Store) (x : L.Var α) (v : α) (y : L.Var β) :
    σ[x := v][y] =
      if h : y.name = x.name then cast (by rw [← x.has_type, ← y.has_type, h]) v else σ[y] := by
  obtain ⟨yn, rfl⟩ := y
  obtain ⟨xn, rfl⟩ := x
  split <;> rename_i h
  · simp only at h
    subst h
    have hgoal := subst_apply σ ⟨ yn , rfl ⟩ v yn
    simp only [↓reduceDIte] at hgoal
    exact hgoal
  · have hgoal := subst_apply_of_ne σ ⟨ xn , rfl ⟩ v h
    simp only at hgoal
    exact hgoal

/-- Reading a variable after writing it returns the written value. -/
@[simp, grind =]
theorem Store.getElem_subst_self {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) (v : α) :
    σ[x := v][x] = v := by
  change x.has_type.mp (σ[x := v] x.name) = v
  simp [subst_apply]

/-- Writing a variable does not affect reading another. -/
@[simp, grind =]
theorem Store.getElem_subst_of_ne {L : LocalSig} {α β} (σ : L.Store) (x : L.Var α) (a : α)
    (y : L.Var β) (h : y.name ≠ x.name) : σ[x := a][y] = σ[y] := by
  change y.has_type.mp (σ[x := a] y.name) = y.has_type.mp (σ y.name)
  rw [subst_apply_of_ne _ _ _ h]

/-- A later write to the same variable overrides an earlier write. -/
@[simp, grind =]
theorem Store.subst_subst_self {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) (a b : α) :
    σ[x := a][x := b] = σ[x := b] := by
  grind

/-- Writes to different variables commute. -/
theorem Store.subst_comm {L : LocalSig} {α β} (σ : L.Store) (x : L.Var α) (y : L.Var β) (a : α)
    (b : β) (h : x.name ≠ y.name) : σ[x := a][y := b] = σ[y := b][x := a] := by
  grind

/-- Two stores agree on a set of variable names if every variable with a name in the set has the
same value in both. -/
def Store.AgreeOn {L : LocalSig} (σ₁ σ₂ : L.Store) (s : Finset L.VarName) : Prop :=
  ∀ {α} (x : L.Var α), x.name ∈ s → σ₁[x] = σ₂[x]

theorem Store.AgreeOn.refl {L : LocalSig} (σ : L.Store) (s : Finset L.VarName) : σ.AgreeOn σ s :=
  fun _ _ => rfl

theorem Store.AgreeOn.symm {L : LocalSig} {σ₁ σ₂ : L.Store} {s : Finset L.VarName}
    (h : σ₁.AgreeOn σ₂ s) : σ₂.AgreeOn σ₁ s :=
  fun x hx => (h x hx).symm

theorem Store.AgreeOn.mono {L : LocalSig} {σ₁ σ₂ : L.Store} {s t : Finset L.VarName}
    (hst : s ⊆ t) (h : σ₁.AgreeOn σ₂ t) : σ₁.AgreeOn σ₂ s :=
  fun x hx => h x (hst hx)

/-- Agreement on a set implies agreement on every subset. -/
theorem Store.AgreeOn.antitone {L : LocalSig} {σ₁ σ₂ : L.Store} : Antitone (AgreeOn σ₁ σ₂ ·) :=
  fun _ _ hst h => h.mono hst

/-- Writing a variable outside a set preserves agreement on the set. -/
theorem Store.agreeOn_subst {L : LocalSig} {α} (σ : L.Store) (x : L.Var α) (v : α)
    {s : Finset L.VarName} (h : x.name ∉ s) : σ[x := v].AgreeOn σ s :=
  fun _ hy => getElem_subst_of_ne _ _ _ _ fun e => h (e ▸ hy)

end LocalSig

end Cslib.Mech
