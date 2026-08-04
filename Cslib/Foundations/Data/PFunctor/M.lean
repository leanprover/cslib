/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Cslib.Init
public import Mathlib.Data.PFunctor.Univariate.M

/-!
# Auxiliary Lemmas for `PFunctor.M`

This file extends the M-type API with rewriting and coinduction helpers for reasoning about
potentially infinite polynomial trees.

## Main Definitions

- `PFunctor.M.eq_of_dest_eq`: Extensionality through the M-type destructor.
- `PFunctor.M.dest_corec_apply`: An explicit destructor equation for `M.corec`.
- `PFunctor.M.corec_eq_corec`: A relational coinduction principle for two corecursive definitions.
- `PFunctor.M.corec_dest`: The corecursive identity.
-/

@[expose] public section

universe uA uB v w

namespace PFunctor.M

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-- `M.dest` is injective because `M.mk` is its left inverse. -/
theorem eq_of_dest_eq {u v : M P} (h : M.dest u = M.dest v) : u = v := by
  rw [← M.mk_dest u, ← M.mk_dest v, h]

@[simp]
theorem dest_inj {u v : M P} : M.dest u = M.dest v ↔ u = v :=
  ⟨eq_of_dest_eq, fun h => h ▸ rfl⟩

/-- `M.dest_corec` with the resulting sigma type unpacked. -/
theorem dest_corec_apply (g : α → P α) (x : α) :
    M.dest (M.corec g x) = ⟨(g x).1, fun b => M.corec g ((g x).2 b)⟩ := rfl

/-- An explicit form of `dest_corec_apply` when the corecursive step is known. -/
theorem dest_corec_eq {a : P.A} {h : P.B a → α} (g : α → P α) (x : α)
    (heq : g x = ⟨a, h⟩) : M.dest (M.corec g x) = ⟨a, fun b => M.corec g (h b)⟩ := by
  rw [dest_corec_apply, heq]

/-- A relational coinduction principle for two `M.corec` constructions. -/
theorem corec_eq_corec {α : Type v} {β : Type w} (g : α → P α) (h : β → P β)
    (R : α → β → Prop) (x₀ : α) (y₀ : β) (hR : R x₀ y₀)
    (step : ∀ x y, R x y → ∃ a f f',
      g x = ⟨a, f⟩ ∧ h y = ⟨a, f'⟩ ∧ ∀ i, R (f i) (f' i)) :
    M.corec g x₀ = M.corec h y₀ := by
  let S : M P → M P → Prop := fun u v => ∃ x y, R x y ∧ u = M.corec g x ∧ v = M.corec h y
  refine M.bisim S ?_ _ _ ⟨x₀, y₀, hR, rfl, rfl⟩
  rintro u v ⟨x, y, hxy, rfl, rfl⟩
  obtain ⟨a, f, f', hf, hf', hR'⟩ := step x y hxy
  refine ⟨a, M.corec g ∘ f, M.corec h ∘ f', ?_, ?_, ?_⟩
  · simp [dest_corec, hf]
  · simp [dest_corec, hf']
  · exact fun i => ⟨f i, f' i, hR' i, rfl, rfl⟩

/-- Corecursing with `M.dest` returns the original M-type value. -/
theorem corec_dest (u : M P) : M.corec M.dest u = u := by
  refine M.bisim (fun a b => a = M.corec M.dest b) ?_ _ _ rfl
  rintro a b rfl
  exact ⟨(M.dest b).1, (fun i => M.corec M.dest ((M.dest b).2 i)),
    (M.dest b).2, by rw [dest_corec_apply], rfl, fun _ => rfl⟩

end PFunctor.M
