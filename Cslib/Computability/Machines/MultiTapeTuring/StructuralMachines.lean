/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.Encoding
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator

namespace Turing

-- ═══════════════════════════════════════════════════════════════════════════
-- eval_struct
-- ═══════════════════════════════════════════════════════════════════════════

/-- Evaluate a Turing machine on structured tape views.
    Converts `TapeView`s to `BiTape`s via `toBiTape`, runs `eval`,
    and converts the result back to `TapeView`s.

    This is defined as a noncomputable opaque function; its behavior
    is specified by the `@[simp]` lemmas for each TM routine. -/
public def MultiTapeTM.eval_struct
    (tm : MultiTapeTM k Char) (views : Fin k → TapeView) :
    Part (Fin k → TapeView) :=
  tm.eval (TapeView.toBiTape ∘ views) >>= (TapeView.ofBiTape? ∘ ·)

namespace Routines

-- ═══════════════════════════════════════════════════════════════════════════
-- Primitives
-- ═══════════════════════════════════════════════════════════════════════════

public def noop : MultiTapeTM k Char := sorry

public def right (i : Fin k) : MultiTapeTM k Char := sorry

public def left (i : Fin k) : MultiTapeTM k Char := sorry

public def write (c : Char) (i : Fin k) : MultiTapeTM k Char := sorry

public def while_eq (c : Char) (i : Fin k) (tm : MultiTapeTM k Char) :
  MultiTapeTM k Char := sorry

public def while_neq (c : Char) (i : Fin k) (tm : MultiTapeTM k Char) :
  MultiTapeTM k Char := sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- eval_struct lemmas: Compositionality
-- ═══════════════════════════════════════════════════════════════════════════

@[simp]
public lemma seq_eval_struct {tm₁ tm₂ : MultiTapeTM k Char}
    {views : Fin k → TapeView} :
    (tm₁ ;ₜ tm₂).eval_struct views =
      (tm₁.eval_struct views).bind tm₂.eval_struct := by sorry

-- ═══════════════════════════════════════════════════════════════════════════
-- Function.update utilities
-- ═══════════════════════════════════════════════════════════════════════════

/-- Sort nested `Function.update` by index: larger indices go outermost. -/
public theorem Function.update_sort {α : Type*} [DecidableEq α] [LinearOrder α]
    {β : Type*} {f : α → β} {a b : α} {v w : β} (h : b < a) :
    Function.update (Function.update f a v) b w =
    Function.update (Function.update f b w) a v :=
  Function.update_comm (ne_of_gt h) v w f

@[simp]
public theorem Function.update_update_update_of_ne {α β : Type*} [DecidableEq α]
    {f : α → β}
    {i j : α} (h : i ≠ j) (x y z : β) :
  Function.update (Function.update (Function.update f i x) j y) i z =
    Function.update (Function.update f j y) i z := by
  simp [Function.update_comm h, Function.update_idem]


end Routines

end Turing
