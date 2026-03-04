/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Cslib.Foundations.Data.BiTape
import Cslib.Foundations.Data.RelatesInSteps

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding

namespace Turing

namespace MultiTapeTM

variable [Inhabited Symbol] [Fintype Symbol]
variable {k : ℕ}

/--
Sequential combination of Turing machines. Runs `tm₁` and then `tm₂` on the resulting tapes
(if the first one halts).
-/
public def seq (tm₁ tm₂ : MultiTapeTM k Symbol) : MultiTapeTM k Symbol := sorry

public theorem seq_eval
  (tm₁ tm₂ : MultiTapeTM k Symbol)
  (tapes₀ : Fin k → BiTape Symbol) :
  (seq tm₁ tm₂).eval tapes₀ =
    tm₁.eval tapes₀ >>= fun tape₁ => tm₂.eval tape₁ := by
  sorry

@[simp, grind =]
public theorem seq_eval_list
  {tm₁ tm₂ : MultiTapeTM k (WithSep Symbol)}
  {tapes₀ : Fin k → List (List Symbol)} :
  (seq tm₁ tm₂).eval_list tapes₀ =
    tm₁.eval_list tapes₀ >>= fun tape₁ => tm₂.eval_list tape₁ := by
  sorry

public theorem seq_associative
  (tm₁ tm₂ tm₃ : MultiTapeTM k Symbol)
  (tapes₀ : Fin k → List (List Symbol)) :
  (seq (seq tm₁ tm₂) tm₃).eval = (seq tm₁ (seq tm₂ tm₃)).eval := by
  sorry

/--
Sequential combination of Turing machines.
-/
infixl:90 " ;ₜ " => seq


end MultiTapeTM

end Turing
