/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.TapeExtension

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Finset.Sort

namespace Turing

variable [Inhabited α] [Fintype α]

variable {k : ℕ}

/--
Permute tapes according to a bijection.
-/
public def MultiTapeTM.permute_tapes
  (tm : MultiTapeTM k α) (σ : Equiv.Perm (Fin k)) : MultiTapeTM k α where
  State := tm.State
  stateFintype := tm.stateFintype
  q₀ := tm.q₀
  tr := fun q syms => match tm.tr q (syms ∘ σ) with
    | (stmts, q') => (stmts ∘ σ.symm, q')

--- General theorem: permuting tapes commutes with evaluation
@[simp, grind =]
public theorem MultiTapeTM.permute_tapes_eval
  (tm : MultiTapeTM k α) (σ : Equiv.Perm (Fin k)) (tapes : Fin k → BiTape α) :
  (tm.permute_tapes σ).eval tapes =
    (tm.eval (tapes ∘ σ)).map (fun tapes' => tapes' ∘ σ.symm) := by
  sorry

private def findFin {k : ℕ} (p : Fin k → Prop) [DecidablePred p] (h : ∃ i, p i) : Fin k :=
  (Finset.univ.filter p).min' (by
    simp only [Finset.Nonempty, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h)

def inj_to_perm {k₁ k₂ : ℕ} (f : Fin k₁ → Fin k₂) (h_inj : f.Injective) :
  Equiv.Perm (Fin k₂)
  -- non-computable version
  --  let f' : {i : Fin k₂ // i < k₁} → Fin k₂ := fun ⟨i, _⟩ => f ⟨i, by omega⟩
  --  have h_f'_inj : f'.Injective := by intro a b h; grind
  --  (Equiv.ofInjective f' h_f'_inj).extendSubtype
  where
  toFun := sorry
  invFun := sorry
  left_inv := by sorry
  right_inv := by sorry

/--
Change the order of the tapes of a Turing machine.
Example: For a 2-tape Turing machine tm,
`tm.with_tapes [2, 4].get (by grind)` is a 5-tape Turing machine whose tape 2 is
the original machine's tape 0 and whose tape 4 is the original
machine's tape 1
Note that `f` is a function to `Fin k₂`, which means that integer literals
automatically wrap. You have to be careful to make sure that the target machine
has the right amount of tapes.
-/
public def MultiTapeTM.with_tapes {k₁ k₂ : ℕ}
-- TODO use embedding instead?
  (tm : MultiTapeTM k₁ α) (f : Fin k₁ → Fin k₂) (h_inj : f.Injective) : MultiTapeTM k₂ α :=
  (tm.extend
    (by simpa using Fintype.card_le_of_injective f h_inj)).permute_tapes (inj_to_perm f h_inj)

-- TODO do not use `h.choose` here but rather assume that `f` is injective.

/--
Updates `tapes` by choosing elements from `tapes'` according to (the partial inverse of) `f`.
-/
public noncomputable def apply_updates
  {γ : Type}
  {k₁ k₂ : ℕ}
  (tapes : Fin k₂ → γ)
  (tapes' : Fin k₁ → γ)
  (f : Fin k₁ → Fin k₂)
  (i : Fin k₂) : γ :=
  if h : ∃ j, f j = i then tapes' h.choose else tapes i

@[simp, grind =]
public lemma apply_updates_function_update_apply
  {γ : Type}
  {k₁ k₂ : ℕ}
  {tapes : Fin k₂ → γ}
  {f : Fin k₁ → Fin k₂}
  (h_inj : f.Injective)
  {t : Fin k₁}
  {new_val : γ}
  {i : Fin k₂} :
  apply_updates tapes (Function.update (tapes ∘ f) t new_val) f i =
    Function.update tapes (f t) new_val i := by
  sorry

@[simp, grind =]
public lemma apply_updates_function_update
  {γ : Type}
  {k₁ k₂ : ℕ}
  {tapes : Fin k₂ → γ}
  {f : Fin k₁ → Fin k₂}
  (h_inj : f.Injective)
  {t : Fin k₁}
  {new_val : γ} :
  apply_updates tapes (Function.update (tapes ∘ f) t new_val) f =
    Function.update tapes (f t) new_val := by
  funext i
  apply apply_updates_function_update_apply h_inj

@[simp, grind =]
public theorem MultiTapeTM.with_tapes_eval
  {k₁ k₂ : ℕ}
  {tm : MultiTapeTM k₁ α} {f : Fin k₁ → Fin k₂} {h_inj : f.Injective}
  {tapes : Fin k₂ → BiTape α} :
  (tm.with_tapes f h_inj).eval tapes =
    (tm.eval (tapes ∘ f)).map
      (fun tapes' => fun t => apply_updates tapes tapes' f t) := by
  simp [with_tapes]
  sorry


end Turing
