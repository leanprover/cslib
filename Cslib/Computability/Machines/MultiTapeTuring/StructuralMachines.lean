/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.Encoding
public import Cslib.Computability.Machines.MultiTapeTuring.SequentialCombinator
public import Mathlib.Data.PFun

namespace Turing

-- ═══════════════════════════════════════════════════════════════════════════
-- eval_struct
-- ═══════════════════════════════════════════════════════════════════════════

/-- Evaluate a Turing machine on structured tape views.
    Converts `TapeView`s to `BiTape`s via `toBiTape`, runs `eval`,
    and converts the result back to `TapeView`s.

    This is defined as a noncomputable opaque function; its behavior
    is specified by the `@[simp]` lemmas for each TM routine. -/
@[expose]
public def MultiTapeTM.eval_struct
    (tm : MultiTapeTM k Char) (views : Fin k → TapeView) :
    Part (Fin k → TapeView) :=
  tm.eval (TapeView.toBiTape ∘ views) >>= fun views => (TapeView.ofBiTape? ∘ ·)

namespace Routines

-- ═══════════════════════════════════════════════════════════════════════════
-- Primitives
-- ═══════════════════════════════════════════════════════════════════════════

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {k : ℕ}

public def noop : MultiTapeTM k Symbol := sorry

@[simp]
public theorem noop.eval_struct {views : Fin k → TapeView} :
  noop.eval_struct views = some views := by sorry

public def right (i : Fin k) : MultiTapeTM k Char := sorry

@[simp]
public theorem right.eval {i : Fin k} {tapes : Fin k → BiTape Char} :
  (right i).eval tapes = some
    (Function.update tapes i (tapes i).move_right) := by sorry

public def left (i : Fin k) : MultiTapeTM k Char := sorry

@[simp]
public theorem left.eval {i : Fin k} {tapes : Fin k → BiTape Char} :
  (left i).eval tapes = some
    (Function.update tapes i (tapes i).move_left) := by sorry

public def write (c : Char) (i : Fin k) : MultiTapeTM k Char := sorry

public def if_eq (c : Char) (i : Fin k) (tm₁ tm₂ : MultiTapeTM k Char) :
  MultiTapeTM k Char := sorry

@[simp]
public theorem if_eq.eval {c : Char} {i : Fin k} {tm₁ tm₂ : MultiTapeTM k Char}
    {tapes : Fin k → BiTape Char} :
  (if_eq c i tm₁ tm₂).eval tapes =
    if (tapes i).head = some c then (tm₁.eval tapes) else (tm₂.eval tapes) := by sorry

public def while_eq (c : Char) (i : Fin k) (tm : MultiTapeTM k Char) :
  MultiTapeTM k Char := sorry

-- @[simp]
-- public theorem while_eq.eval
--   (c : Char) (i : Fin k)
--   (tm : MultiTapeTM k Char)
--   (tapes : Fin k → BiTape Char) :
--   (while_eq c i tm).eval tapes =
--     ⟨∃ n, (((tm.eval)^[n] (.some tapes)) >>= fun tapes => (tapes i).head) = Part.some (some c),
--     sorry ⟩ := by sorry

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

@[simp]
public theorem Function.update_redundant {α : Type*} [DecidableEq α]
    {β : Type*} {f : α → β} {i j : α} {v : β} (h : i ≠ j) :
    Function.update (Function.update f i v) j (f j) =
    Function.update f i v := by
  grind


end Routines

end Turing
