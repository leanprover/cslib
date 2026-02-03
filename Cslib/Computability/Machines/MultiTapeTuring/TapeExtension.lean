/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Cslib.Foundations.Data.BiTape
import Cslib.Foundations.Data.RelatesInSteps

public import Cslib.Computability.Machines.MultiTapeTuring.Basic

-- TODO create a "common file"
import Cslib.Computability.Machines.SingleTapeTuring.Basic

namespace Turing

variable [Inhabited α] [Fintype α]

/-- Extend a Turing machine to work with more tapes.
The added tapes are not acted upon. -/
public def MultiTapeTM.extend {k₁ k₂ : ℕ} (h_le : k₁ ≤ k₂)
    (tm : MultiTapeTM k₁ α) : MultiTapeTM k₂ α where
  Λ := tm.Λ
  q₀ := tm.q₀
  M := fun q syms => match tm.M q (fun i => syms ⟨i, by omega⟩) with
    | (stmts, q') =>
      (fun i => if h : i < k₁ then stmts ⟨i, h⟩ else default, q')

@[simp, grind =]
public lemma MultiTapeTM.extend_eval {k₁ k₂ : ℕ} (h_le : k₁ ≤ k₂)
  (tm : MultiTapeTM k₁ α)
  {tapes : Fin k₂ → BiTape α} :
  (tm.extend h_le).eval tapes =
    (tm.eval (tapes ⟨·, by omega⟩)).map (fun tapes' =>
      fun i : Fin k₂ => if h : i < k₁ then tapes' ⟨i, h⟩ else tapes i) := by
  sorry

end Turing
