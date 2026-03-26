/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.TapeView
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
  tm.eval (TapeView.toBiTape ∘ views) >>= (TapeView.ofBiTapes? ·)

-- TODO clean up (AI)
public theorem MultiTapeTM.eval_of_eval_struct
    {tm : MultiTapeTM k Char} {views views' : Fin k → TapeView}
    (h_eval_struct : tm.eval_struct views = .some views') :
  tm.eval (TapeView.toBiTape ∘ views) = .some (TapeView.toBiTape ∘ views') := by
  unfold eval_struct at h_eval_struct
  simp only [Part.bind_eq_bind] at h_eval_struct
  have h_mem := h_eval_struct ▸ Part.mem_some _
  rw [Part.mem_bind_iff] at h_mem
  obtain ⟨tapes, h_eval, h_of⟩ := h_mem
  rw [Part.eq_some_iff.mpr h_eval]; congr 1
  have h_of' : TapeView.ofBiTapes? tapes = some views' := by
    rwa [Part.mem_coe] at h_of
  simp only [TapeView.ofBiTapes?] at h_of'
  split at h_of'
  · rename_i h_all
    simp only [Option.some.injEq] at h_of'
    ext i; simp only [Function.comp_apply]
    rw [← congr_fun h_of' i, TapeView.ofBiTape_get_toBiTape]
  · simp at h_of'

namespace Routines

-- ═══════════════════════════════════════════════════════════════════════════
-- Primitives
-- ═══════════════════════════════════════════════════════════════════════════

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {k : ℕ}

/-- TODO document -/
public def noop : MultiTapeTM k Symbol := sorry

@[simp]
public theorem noop.eval {tapes : Fin k → BiTape Char} :
  noop.eval tapes = some tapes := by sorry

@[simp]
public theorem noop.eval_struct {views : Fin k → TapeView} :
  noop.eval_struct views = some views := by sorry

/-- TODO document -/
public def right (i : Fin k) : MultiTapeTM k Char := sorry

@[simp]
public theorem right.eval {i : Fin k} {tapes : Fin k → BiTape Char} :
  (right i).eval tapes = .some
    (Function.update tapes i (tapes i).move_right) := by sorry

@[grind =>]
public lemma right.haltsOn {i : Fin k} : ∀ t, (right i).HaltsOn t := by simp

/-- TODO document -/
public def left (i : Fin k) : MultiTapeTM k Char := sorry

@[simp]
public theorem left.eval {i : Fin k} {tapes : Fin k → BiTape Char} :
  (left i).eval tapes = .some
    (Function.update tapes i (tapes i).move_left) := by sorry

@[grind =>]
public lemma left.haltsOn {i : Fin k} : ∀ t, (left i).HaltsOn t := by simp

/-- TODO document -/
public def write (c : Option Char) (i : Fin k) : MultiTapeTM k Char := sorry

@[simp]
public theorem write.eval {c : Option Char} {i : Fin k} {tapes : Fin k → BiTape Char} :
  (write c i).eval tapes = .some
    (Function.update tapes i ((tapes i).write c)) := by sorry

/-- TODO document -/
public def if_eq (c : Char) (i : Fin k) (tm₁ tm₂ : MultiTapeTM k Char) :
  MultiTapeTM k Char := sorry

@[simp]
public theorem if_eq.eval {c : Char} {i : Fin k} {tm₁ tm₂ : MultiTapeTM k Char}
    {tapes : Fin k → BiTape Char} :
  (if_eq c i tm₁ tm₂).eval tapes =
    if (tapes i).head = some c then (tm₁.eval tapes) else (tm₂.eval tapes) := by sorry

/-- TODO document -/
public def while_eq (c : Option Char) (i : Fin k) (tm : MultiTapeTM k Char) :
  MultiTapeTM k Char := sorry

@[simp]
public theorem while_eq.eval'
  (c : Option Char) (i : Fin k)
  (tm : MultiTapeTM k Char)
  (h_halts : ∀ t, tm.HaltsOn t)
  (tapes : Fin k → BiTape Char) :
  (while_eq c i tm).eval tapes =
    ⟨∃ n, (((tm.eval_tot h_halts)^[n] tapes) i).head != c,
     fun h => ((tm.eval_tot h_halts)^[Nat.find h] tapes)⟩ := by sorry

public theorem while_eq.eval
  {c : Option Char} {i : Fin k}
  {tm : MultiTapeTM k Char}
  {h_halts : ∀ t, tm.HaltsOn t}
  {tapes : Fin k → BiTape Char}
  (n : ℕ)
  (h_exists : ((tm.eval_tot h_halts)^[n] tapes i).head ≠ c)
  (h_min : ∀ n' < n, ((tm.eval_tot h_halts)^[n'] tapes i).head = c) :
  (while_eq c i tm).eval tapes = (tm.eval_tot h_halts)^[n] tapes := by sorry

/-- TODO document -/
public def while_neq (c : Option Char) (i : Fin k) (tm : MultiTapeTM k Char) :
  MultiTapeTM k Char := sorry

@[simp]
public theorem while_neq.eval
  (c : Option Char) (i : Fin k)
  (tm : MultiTapeTM k Char)
  (h_halts : ∀ t, tm.HaltsOn t)
  (tapes : Fin k → BiTape Char) :
  (while_neq c i tm).eval tapes =
    ⟨∃ n, (((tm.eval_tot h_halts)^[n] tapes) i).head == c,
     fun h => ((tm.eval_tot h_halts)^[Nat.find h] tapes)⟩ := by sorry

public theorem while_neq.eval'
  {c : Option Char} {i : Fin k}
  {tm : MultiTapeTM k Char}
  {h_halts : ∀ t, tm.HaltsOn t}
  {tapes : Fin k → BiTape Char}
  (n : ℕ)
  (h_exists : (((tm.eval_tot h_halts)^[n] tapes) i).head == c)
  (h_min : ∀ n' < n, (((tm.eval_tot h_halts)^[n'] tapes) i).head ≠ c) :
  (while_neq c i tm).eval tapes = ((tm.eval_tot h_halts)^[n] tapes) := by sorry

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
