/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Basic

/-!
# Sequential execution on shared tapes

`seq` runs two machines with the same work-tape count. The transition that would halt the first
machine instead enters the second machine's initial state. Tape contents, head positions, and
accumulated output are carried across, with no extra transition for the handoff.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State State₀ State₁ : Type*} {input : List Symbol}

/-- Run two machines on the same tapes, handing off on the first halting transition. -/
def seq (tm₀ : MultiTapeTM k Symbol State₀) (tm₁ : MultiTapeTM k Symbol State₁) :
    MultiTapeTM k Symbol (State₀ ⊕ State₁) where
  q₀ := .inl tm₀.q₀
  tr q input work := match q with
    | .inl q =>
      let out := tm₀.tr q input work
      ⟨out.inputMove, out.workActions, out.outS,
        some (out.q'.elim (.inr tm₁.q₀) Sum.inl)⟩
    | .inr q =>
      let out := tm₁.tr q input work
      ⟨out.inputMove, out.workActions, out.outS, out.q'.map Sum.inr⟩

namespace Sequential

/-- A first-machine configuration; a native halt becomes the second machine's initial state. -/
def left (tm₁ : MultiTapeTM k Symbol State₁) (cfg : Cfg k Symbol State₀ input) :
    Cfg k Symbol (State₀ ⊕ State₁) input :=
  cfg.withState (some (cfg.state.elim (.inr tm₁.q₀) Sum.inl))

/-- A second-machine configuration, including a final halt. -/
def right (cfg : Cfg k Symbol State₁ input) : Cfg k Symbol (State₀ ⊕ State₁) input :=
  cfg.withState (cfg.state.map Sum.inr)

variable (tm₀ : MultiTapeTM k Symbol State₀) (tm₁ : MultiTapeTM k Symbol State₁)

/-- The left embedding preserves each step before the native halt. -/
lemma step_left (cfg : Cfg k Symbol State₀ input) (h : cfg.state ≠ none) :
    (seq tm₀ tm₁).step (left tm₁ cfg) = left tm₁ (tm₀.step cfg) := by
  cases hs : cfg.state with
  | none => exact (h hs).elim
  | some q =>
    simp only [step, left, Cfg.withState, seq, hs, Option.elim_some]
    rfl

/-- The right embedding preserves every step, including steps after halting. -/
lemma step_right (cfg : Cfg k Symbol State₁ input) :
    (seq tm₀ tm₁).step (right cfg) = right (tm₁.step cfg) := by
  cases hs : cfg.state <;>
    simp only [step, right, Cfg.withState, seq, hs, Option.map_some, Option.map_none]
  rfl

/-- The first run is preserved up to its earliest halt. -/
lemma runFrom_left (cfg : Cfg k Symbol State₀ input) (n : ℕ)
    (h : ∀ m < n, (tm₀.runFrom cfg m).state ≠ none) :
    (seq tm₀ tm₁).runFrom (left tm₁ cfg) n = left tm₁ (tm₀.runFrom cfg n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runFrom_succ_eq_step', ih (fun m hm => h m (by omega)),
      step_left tm₀ tm₁ _ (h n (by omega)), runFrom_succ_eq_step']

/-- Once in the second phase, runs are exactly the second machine's runs. -/
lemma runFrom_right (cfg : Cfg k Symbol State₁ input) (n : ℕ) :
    (seq tm₀ tm₁).runFrom (right cfg) n = right (tm₁.runFrom cfg n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runFrom_succ_eq_step', ih, step_right, runFrom_succ_eq_step']

end Sequential

/-- Sequential execution starts in the first machine's initial configuration. -/
lemma initCfg_seq (tm₀ : MultiTapeTM k Symbol State₀) (tm₁ : MultiTapeTM k Symbol State₁)
    (input : List Symbol) :
    (tm₀.seq tm₁).initCfg input = Sequential.left tm₁ (tm₀.initCfg input) := rfl

/-- Sequential execution splits at the first machine's earliest halt. The second machine receives
all final tapes and head positions, together with the output accumulated so far. -/
lemma runFrom_seq (tm₀ : MultiTapeTM k Symbol State₀) (tm₁ : MultiTapeTM k Symbol State₁)
    (cfg : Cfg k Symbol State₀ input) (u v : ℕ)
    (hhalt : (tm₀.runFrom cfg u).state = none)
    (hactive : ∀ m < u, (tm₀.runFrom cfg m).state ≠ none) :
    (seq tm₀ tm₁).runFrom (Sequential.left tm₁ cfg) (u + v) =
      Sequential.right (tm₁.runFrom ((tm₀.runFrom cfg u).withState (some tm₁.q₀)) v) := by
  rw [runFrom_add, Sequential.runFrom_left tm₀ tm₁ cfg u hactive]
  rw [show Sequential.left tm₁ (tm₀.runFrom cfg u) =
    Sequential.right ((tm₀.runFrom cfg u).withState (some tm₁.q₀)) by
      simp [Sequential.left, Sequential.right, Cfg.withState, hhalt]]
  exact Sequential.runFrom_right tm₀ tm₁ _ v

/-- Sequential execution uses at most the space of its two phases. The two phases may revisit
each other's cells, so the bound is an inequality. -/
lemma spaceUsed_seq_le (tm₀ : MultiTapeTM k Symbol State₀) (tm₁ : MultiTapeTM k Symbol State₁)
    (cfg : Cfg k Symbol State₀ input) (u v : ℕ)
    (hhalt : (tm₀.runFrom cfg u).state = none)
    (hactive : ∀ m < u, (tm₀.runFrom cfg m).state ≠ none) :
    (tm₀.seq tm₁).spaceUsed (Sequential.left tm₁ cfg) (u + v) ≤
      tm₀.spaceUsed cfg u + tm₁.spaceUsed ((tm₀.runFrom cfg u).withState (some tm₁.q₀)) v := by
  refine ((tm₀.seq tm₁).spaceUsed_add_le _ u v).trans (Nat.add_le_add (le_of_eq ?_) (le_of_eq ?_))
  · refine spaceUsed_eq_of_workTapePos _ _ u fun m hm => ?_
    rw [Sequential.runFrom_left tm₀ tm₁ cfg m fun r hr => hactive r (by omega)]
    rfl
  · rw [Sequential.runFrom_left tm₀ tm₁ cfg u hactive,
      show Sequential.left tm₁ (tm₀.runFrom cfg u) =
        Sequential.right ((tm₀.runFrom cfg u).withState (some tm₁.q₀)) by
          simp [Sequential.left, Sequential.right, Cfg.withState, hhalt]]
    refine spaceUsed_eq_of_workTapePos _ _ v fun m _ => ?_
    rw [Sequential.runFrom_right tm₀ tm₁ _ m]
    rfl

end Turing.MultiTapeTM
