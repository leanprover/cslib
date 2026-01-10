/-
Copyright (c) 2026 Mohamad Al-Zawahreh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohamad Al-Zawahreh
-/

import Cslib.Foundations.Semantics.LTS.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith


namespace Cslib.Foundations.Semantics.LTS

variable {State Label : Type}
variable (lts : LTS State Label)

/-- The Inductive Definition of Execution Traces (Fabrizio's Tail-Cons Style) -/
inductive IsExecution : State → List Label → List State → State → Prop
| refl (s) : IsExecution s [] [] s
| step {s1 μ s2 μs ss s3} :
    lts.Tr s1 μ s2 →
    IsExecution s2 μs ss s3 →
    IsExecution s1 (μ :: μs) (s2 :: ss) s3

/-- The Indexed View of Execution Traces.
    'ss' contains the *targets* of transitions.
    Thus ss.length = μs.length. The full path is (s_start :: ss). -/
def IsExecution_Indexed (s_start : State) (μs : List Label) (ss : List State) (s_end : State) : Prop :=
  if h : ss.length = μs.length then
    (ss.getLast? = some s_end ∨ (ss = [] ∧ s_start = s_end)) ∧
    ∀ (i : Fin μs.length),
      -- Logic: Step 'i' goes from State[i] to State[i+1]
      -- Since 'ss' starts at index 1 relative to s_start:
      let current := if h0 : i.val = 0 then s_start
                     else ss.get ⟨i.val - 1, by rw [h]; apply Nat.lt_of_le_of_lt (Nat.pred_le _) i.isLt⟩
      let next    := ss.get ⟨i.val, by rw [h]; exact i.isLt⟩
      lts.Tr current (μs.get i) next
  else
    False

end Cslib.Foundations.Semantics.LTS
