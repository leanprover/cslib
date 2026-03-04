/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic

namespace Turing

variable [Inhabited Symbol] [Fintype Symbol]

/-- Extend a Turing machine to work with more tapes.
The added tapes are not acted upon. -/
public def MultiTapeTM.extend {k₁ k₂ : ℕ} (h_le : k₁ ≤ k₂)
    (tm : MultiTapeTM k₁ Symbol) : MultiTapeTM k₂ Symbol where
  State := tm.State
  stateFintype := tm.stateFintype
  q₀ := tm.q₀
  tr := fun q syms => match tm.tr q (fun i => syms ⟨i, by omega⟩) with
    | (stmts, q') =>
      (fun i => if h : i < k₁ then stmts ⟨i, h⟩ else default, q')

/--
Restrict a sequence of tapes to the first `k'` tapes.
-/
@[simp]
public abbrev tapes_take
  {γ : Type}
  (tapes : Fin k → γ)
  (k' : ℕ)
  (h_le : k' ≤ k)
  (i : Fin k') : γ :=
  tapes ⟨i, by omega⟩

@[simp]
public lemma Function.update_tapes_take
  {γ : Type}
  (k : ℕ)
  {k' : ℕ}
  {h_le : k' ≤ k}
  {tapes : Fin k → γ}
  {p : Fin k'}
  {v : γ} :
  Function.update (tapes_take tapes k' h_le) p v =
    tapes_take (Function.update tapes ⟨p, by omega⟩ v) k' h_le := by
  sorry

/--
Extend a sequence of tapes by adding more tapes at the end.
Ignores the first `k₁` tapes of `extend_by` and uses the rest.
-/
@[simp]
public abbrev tapes_extend_by
  {γ : Type}
  {k₁ k₂ : ℕ}
  (tapes : Fin k₁ → γ)
  (extend_by : Fin k₂ → γ)
  (i : Fin k₂) : γ :=
  if h : i < k₁ then tapes ⟨i, h⟩ else extend_by i

@[simp, grind =]
public lemma MultiTapeTM.extend_eval {k₁ k₂ : ℕ} (h_le : k₁ ≤ k₂)
  (tm : MultiTapeTM k₁ Symbol)
  {tapes : Fin k₂ → BiTape Symbol} :
  (tm.extend h_le).eval tapes =
    (tm.eval (tapes ⟨·, by omega⟩)).map (fun tapes' => tapes_extend_by tapes' tapes) := by
  sorry

end Turing
