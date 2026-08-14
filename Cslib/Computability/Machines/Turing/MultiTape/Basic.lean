/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Aviv Bar Natan
-/

module

public import Cslib.Init
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Sign.Defs

/-!
# Configurations of Multi-Tape Turing Machines

Configurations of a multi-tape Turing machine with a read-only input tape, `k` work tapes and one
write-only output tape, together with what a single step does to one and the measures read off a
run.

Nothing here mentions a machine. A step is described in two parts: a `TransitionOut`, recording
which way the input head moves, what is written and where the work heads move, which symbol is
emitted and which state follows; and `TransitionOut.apply`, which carries it out on a
configuration.

## Important Declarations

* `Cfg`: the configuration of a machine: the internal state, the tape contents and head positions
* `TransitionOut`: what a machine does in one step
* `TransitionOut.apply`: the effect of one step on a configuration
* `Cfg.Halted`, `Cfg.init`: halting, and the configuration a machine starts in
* `spaceUsedOfCfgs`: work tape cells touched along a list of configurations
* `outputOfLabels`: the string emitted along a run, from the symbols emitted at each step
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/-- The output of the transition function. -/
structure TransitionOut (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputMove : SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workActions : Fin k → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  outS : Option Symbol
  /-- The successor state or none to halt. -/
  q' : Option State


/--
The configurations of a Turing machine is relative to the input of the machine and consist of:
- an `Option`al state (or none for the halting state),
- the position of the input head (shifted by one),
- the contents of the work tape,
- the positions of the work tape heads.
-/
@[ext]
structure Cfg (k : ℕ) (Symbol State : Type*) (input : List Symbol) where
  /-- the state of the TM (or none for the halting state) -/
  state : Option State
  /-- the position of the input head, shifted by one -/
  inputPos : Fin (input.length + 2)
  /-- the work tapes -/
  workTapes : Fin k → ℤ → Option Symbol
  /-- the positions of the heads on the work tapes -/
  workTapePos : Fin k → ℤ
deriving Inhabited

/-- Attempt to move the input tape head.
The machine can only read one empty cell outside of the input,
any attempted movement beyond that results in no movement.

The addition is performed in `ℤ` before clamping. Performing it in `Fin (n + 2)` would wrap an
outward boundary move to the opposite end of the input. -/
@[scoped grind =]
def moveInputPos {n : ℕ} (pos : Fin (n + 2)) (m : SignType) : Fin (n + 2) :=
  let p := ((pos.val : ℤ) + (m.cast : ℤ)).toNat
  if h : p < n + 2 then ⟨p, h⟩ else ⟨n + 1, by omega⟩

@[simp]
lemma moveInputPos_zero {n : ℕ} (pos : Fin (n + 2)) :
    moveInputPos pos 0 = pos := by
  apply Fin.ext
  simp [moveInputPos, pos.isLt]

@[simp]
lemma moveInputPos_leftBoundary {n : ℕ} :
    moveInputPos (0 : Fin (n + 2)) (-1) = 0 := by
  apply Fin.ext
  simp [moveInputPos]

@[simp]
lemma moveInputPos_rightBoundary {n : ℕ} :
    moveInputPos (⟨n + 1, by omega⟩ : Fin (n + 2)) 1 = ⟨n + 1, by omega⟩ := by
  unfold moveInputPos
  rw [dite_eq_right (by simp; omega)]

/-- A left move away from the left input boundary decrements the native input position. -/
lemma moveInputPos_neg_of_ne_left {n : ℕ} (p : Fin (n + 2)) (h : p ≠ 0) :
    moveInputPos p .neg = ⟨p.val - 1, by have := p.isLt; omega⟩ := by
  have hp : 0 < p.val := Nat.pos_of_ne_zero (fun hz => h (Fin.ext hz))
  unfold moveInputPos
  apply Fin.ext
  rw [dite_eq_left] <;> simp <;> omega

/-- A right move away from the right input boundary increments the native input position. -/
lemma moveInputPos_pos_of_ne_right {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ n + 1) :
    moveInputPos p .pos = ⟨p.val + 1, by have := p.isLt; omega⟩ := by
  unfold moveInputPos
  rw [dite_eq_left]
  · apply Fin.ext
    simp
  · simp
    omega

/-- The symbol currently under the input tape head. -/
def Cfg.inputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  if h₁ : cfg.inputPos = 0 then none
  else if h₂ : cfg.inputPos = input.length + 1 then none
  else input[cfg.inputPos.val - 1]'(by grind)

@[simp]
lemma inputSymbolInner {cfg : Cfg k Symbol State input} (p : ℕ)
    (h₁ : cfg.inputPos.val = 1 + p)
    (h₂ : p < input.length) :
    cfg.inputSymbol = some input[p] := by
  grind [Cfg.inputSymbol]

/-- A configuration has halted. Reducible, so that a hypothesis of this form is usable directly as
the underlying equation. -/
abbrev Cfg.Halted (cfg : Cfg k Symbol State input) : Prop := cfg.state = none

/-- The configuration a machine starts in: blank work tapes, every head at the origin, and the
input head on the first input cell. -/
@[simp]
def Cfg.init (q₀ : State) (input : List Symbol) : Cfg k Symbol State input :=
  ⟨some q₀, 1, fun _ _ => none, fun _ => 0⟩

/-- The symbol read by work tape `i`. -/
def Cfg.workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)


/--
The effect of a transition on a configuration: move the input head, write and move on the work
tapes, and go to the successor state. This is the part of a step that does not depend on how the
transition was chosen.
-/
@[simp]
def TransitionOut.apply (out : TransitionOut k Symbol State) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input :=
  {
    state := out.q',
    inputPos := moveInputPos cfg.inputPos out.inputMove,
    workTapes i := match (out.workActions i).1 with
      | none => cfg.workTapes i
      | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
    workTapePos i := (cfg.workTapePos i) + (out.workActions i).2
  }

/-- A work tape head moves by at most one cell when a transition is applied. -/
lemma workTapePos_apply_le (out : TransitionOut k Symbol State) (cfg : Cfg k Symbol State input)
    (i : Fin k) :
    |(out.apply cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  simp only [TransitionOut.apply, add_sub_cancel_left, abs_le, SignType.cast]
  grind

/-- The positions visited by the head of work tape `i` along a list of configurations. -/
def visitedOfCfgs (cfgs : List (Cfg k Symbol State input)) (i : Fin k) : Finset ℤ :=
  (cfgs.map (·.workTapePos i)).toFinset

/--
The number of work tape cells touched along a list of configurations.

This is the space measure once the visited configurations are known, independently of how they were
produced.
-/
def spaceUsedOfCfgs (cfgs : List (Cfg k Symbol State input)) : ℕ :=
  ∑ i, (visitedOfCfgs cfgs i).card

/--
The string emitted along a run, from the symbols emitted at each of its steps: the labels with the
silent steps dropped.
-/
def outputOfLabels (labels : List (Option Symbol)) : List Symbol := labels.flatMap Option.toList

@[simp]
lemma outputOfLabels_nil : outputOfLabels ([] : List (Option Symbol)) = [] := rfl

@[simp]
lemma outputOfLabels_append (labels₁ labels₂ : List (Option Symbol)) :
    outputOfLabels (labels₁ ++ labels₂) = outputOfLabels labels₁ ++ outputOfLabels labels₂ := by
  simp [outputOfLabels]

@[simp]
lemma outputOfLabels_singleton (o : Option Symbol) : outputOfLabels [o] = o.toList := by
  simp [outputOfLabels]

end Turing
