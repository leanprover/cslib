/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Aviv Bar Natan
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Basic.Sign.Defs
public import Cslib.Init

/-!
# Configurations of Multi-Tape Turing Machines

Configurations of a multi-tape Turing machine with a read-only input tape, `k` work tapes and one
write-only output tape, together with what a single transition does to one and the space measure
read off a list of them.

## Design

Nothing here mentions a machine. A step is described in two parts: an `Action`, recording
which way the input head moves, what is written and where the work heads move, which symbol is
emitted and which state follows; and `Action.apply`, which carries it out on a
configuration.

The output tape is part of the configuration, so the string emitted along a run can be read off
the configuration the run ends in.

## Tape conventions

The multi-tape Turing machine uses a read-only input tape, `k` work tapes and a write-only output
tape.
The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement.
An action can optionally output one symbol, which models the write-only output tape.
Because of these restrictions, we ignore the input and output tapes for space usage of the machine.
The space usage is defined as the total number of cells the work tape heads visited during
execution.

Restricting the movement of the input head is not essential, but useful because it allows
us to easily bound the number of possible configurations of a space-bounded machine. Most textbooks
have this restriction.

Instead of considering the cells _visited_ by the work tape heads, some textbooks
(including [AroraBarak09]) only consider the number of cells that contain
a non-blank symbol at some point in the execution or the number of cells written to. This allows
work tape heads to freely move at no cost as long as they do not write. It is
important to note that this causes `DSPACE(1)` to include `DSPACE(log log n)`, a class that
contains e.g. the non-regular language `{0^n 1^n | n ∈ ℕ}` (it is accepted by a TM that writes a
single marker on the work tape and then counts the number of symbols by work tape head movement
without writing).
Defining space usage via "cells visited" thus yields the more fine-grained "complexity world" in
which `DSPACE(1)` is exactly the class of regular languages.

This definition is adapted from the one in [Papadimitriou94], chapter 2.3 including
the sub-linear space modifications from chapter 2.5 with the following changes:
- We allow Turing machines to choose to not write on a tape. This is equivalent to
  writing the read symbol again but makes it easier to reason about the semantics.
- Our tapes are infinite in both directions instead of just to the right. This definition is
  equivalent (see [AroraBarak09], Claim 1.4). It saves us from having to add a "start marker" to
  the alphabet.
- We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
  be distinguished based on the output.
- The way to prevent the input head to move outside the input is enforced by the interpretation
  and not by a restriction on the transition function. The two definitions are equivalent, but
  not restricting the transition function makes it easier to define a universal machine.

## Important Declarations

* `Cfg`: the configuration: the internal state, the tape contents and head positions, and the
    output tape
* `Action`: what a machine does in one step
* `Action.apply`: the effect of one action on a configuration
* `Cfg.Halted`, `Cfg.init`: halting, and the configuration a machine starts in
* `spaceUsedOfCfgs`: work tape cells touched along a list of configurations

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- What a machine does in one step. -/
structure Action (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputTape : SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workTapes : Fin k → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  output : Option Symbol
  /-- The successor state or none to halt. -/
  state : Option State

/--
The configurations of a Turing machine is relative to the input of the machine and consist of:
- an `Option`al state (or none for the halting state),
- the position of the input head (shifted by one),
- the contents of the work tape,
- the positions of the work tape heads,
- the contents of the write-only output tape
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
  /-- the contents of the write-only output tape -/
  output : List Symbol
deriving Inhabited

/-- Two configurations of a machine without work tapes are equal if their states, input head
positions and outputs are equal. -/
lemma Cfg.ext_zero_tapes {Symbol State : Type*} {input : List Symbol}
    {cfg₁ cfg₂ : Cfg 0 Symbol State input} (state : cfg₁.state = cfg₂.state)
    (inputPos : cfg₁.inputPos = cfg₂.inputPos) (output : cfg₁.output = cfg₂.output) :
    cfg₁ = cfg₂ :=
  Cfg.ext state inputPos (funext fun i => i.elim0) (funext fun i => i.elim0) output

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

/-- The symbol read by work tape `i`. -/
def Cfg.workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)

/-- A configuration is halted when it has no state to continue from. -/
abbrev Cfg.Halted (cfg : Cfg k Symbol State input) : Prop := cfg.state = none

/-- The same configuration in a different control state, possibly of a different state type. -/
@[simps] def Cfg.withState (cfg : Cfg k Symbol State input)
    {State' : Type*} (q : Option State') : Cfg k Symbol State' input :=
  ⟨q, cfg.inputPos, cfg.workTapes, cfg.workTapePos, cfg.output⟩

/-- Remap the (optional) state of a configuration through `φ`, leaving the input head, the work
tapes, the work-tape heads and the output alone. This is the shape of embedding used to place a
sub-machine's configurations into a larger machine built from it. -/
@[simps] def Cfg.mapState {State' : Type*} (φ : Option State → Option State')
    (c : Cfg k Symbol State input) : Cfg k Symbol State' input :=
  ⟨φ c.state, c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- The initial configuration for a starting state and an input string. -/
@[simp]
def Cfg.init (q₀ : State) (input : List Symbol) : Cfg k Symbol State input :=
  ⟨some q₀, 1, fun _ _ => none, fun _ => 0, []⟩

/--
The effect of an action on a configuration: move the input head, write and move on the work tapes,
append the emitted symbol to the output tape, and go to the successor state. This is the part of a
step that does not depend on how the action was chosen.
-/
@[simp]
def Action.apply (action : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input where
  state := action.state
  inputPos := moveInputPos cfg.inputPos action.inputTape
  workTapes i := match (action.workTapes i).1 with
    | none => cfg.workTapes i
    | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
  workTapePos i := cfg.workTapePos i + (action.workTapes i).2
  output := cfg.output ++ action.output.toList

/-- A work tape head moves by at most one cell when an action is applied. -/
lemma workTapePos_apply_le (action : Action k Symbol State)
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    |(action.apply cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  simp only [Action.apply, add_sub_cancel_left, abs_le, SignType.cast]
  grind

/-- Applying an action can only change a cell under its work tape head. -/
lemma Action.apply_workTapes_eq_of_ne (action : Action k Symbol State)
    (cfg : Cfg k Symbol State input) (i : Fin k) (z : ℤ)
    (hz : z ≠ cfg.workTapePos i) :
    (action.apply cfg).workTapes i z = cfg.workTapes i z := by
  cases h : (action.workTapes i).1 <;> simp [Action.apply, h, hz]

/-- The work tape cells visited by the head of tape `i` along a list of configurations. -/
def visitedOfCfgs (cfgs : List (Cfg k Symbol State input)) (i : Fin k) : Finset ℤ :=
  (cfgs.map (·.workTapePos i)).toFinset

/-- The number of work tape cells touched by the heads along a list of configurations. -/
def spaceUsedOfCfgs (cfgs : List (Cfg k Symbol State input)) : ℕ :=
  ∑ i, (visitedOfCfgs cfgs i).card

/-- Including more configurations can only increase the visited set. -/
lemma visitedOfCfgs_mono {cfgs cfgs' : List (Cfg k Symbol State input)}
    (h : cfgs ⊆ cfgs') (i : Fin k) : visitedOfCfgs cfgs i ⊆ visitedOfCfgs cfgs' i := by
  intro z hz
  simp only [visitedOfCfgs, List.mem_toFinset, List.mem_map] at hz ⊢
  obtain ⟨c, hc, rfl⟩ := hz
  exact ⟨c, h hc, rfl⟩

/-- A work tape head visits at most one position per configuration. -/
lemma card_visitedOfCfgs_le (cfgs : List (Cfg k Symbol State input)) (i : Fin k) :
    (visitedOfCfgs cfgs i).card ≤ cfgs.length := by
  simpa [visitedOfCfgs] using List.toFinset_card_le (cfgs.map (·.workTapePos i))

/-- Space usage is monotone under inclusion of configuration lists. -/
lemma spaceUsedOfCfgs_mono {cfgs cfgs' : List (Cfg k Symbol State input)}
    (h : cfgs ⊆ cfgs') : spaceUsedOfCfgs cfgs ≤ spaceUsedOfCfgs cfgs' :=
  Finset.sum_le_sum fun i _ => Finset.card_le_card (visitedOfCfgs_mono h i)

/-- Each configuration contributes at most one visited cell per tape. -/
lemma spaceUsedOfCfgs_le (cfgs : List (Cfg k Symbol State input)) :
    spaceUsedOfCfgs cfgs ≤ k * cfgs.length := by
  calc
    spaceUsedOfCfgs cfgs ≤ ∑ i : Fin k, cfgs.length :=
      Finset.sum_le_sum fun i _ => card_visitedOfCfgs_le cfgs i
    _ = k * cfgs.length := by simp

/-- A tape containing exactly the symbols of `xs` at positions `0, ..., xs.length - 1`. -/
def tapeOfList (xs : List Symbol) : ℤ → Option Symbol
  | .ofNat n => xs[n]?
  | .negSucc _ => none

@[simp]
lemma tapeOfList_ofNat (xs : List Symbol) (n : ℕ) : tapeOfList xs n = xs[n]? := rfl

@[simp]
lemma tapeOfList_negSucc (xs : List Symbol) (n : ℕ) :
    tapeOfList xs (.negSucc n) = none := rfl

/-- Appending one symbol writes precisely the cell after the existing word. -/
lemma tapeOfList_append_single (xs : List Symbol) (x : Symbol) :
    tapeOfList (xs ++ [x]) = Function.update (tapeOfList xs) (xs.length : ℤ) (some x) := by
  funext z
  cases z with
  | negSucc n => simp [tapeOfList]
  | ofNat n => grind [tapeOfList]

/-- The blank tape holds the empty word. -/
@[simp]
lemma tapeOfList_nil : tapeOfList ([] : List Symbol) = fun _ => none := by
  funext z
  cases z <;> simp

/-- The cell at position `0` holds the first symbol of the word. -/
lemma tapeOfList_zero (xs : List Symbol) : tapeOfList xs 0 = xs.head? := by
  have h : (0 : ℤ) = ((0 : ℕ) : ℤ) := rfl
  rw [h, tapeOfList_ofNat]
  cases xs <;> rfl

/-- The configuration whose work tape `i` holds exactly the word `ws i` with its head at the
start, whose input head is at the start of the input, in state `q` with output `out`. -/
@[simps]
def wordsCfg (input : List Symbol) (q : Option State)
    (ws : Fin k → List Symbol) (out : List Symbol) : Cfg k Symbol State input :=
  ⟨q, 1, fun i => tapeOfList (ws i), fun _ => 0, out⟩

/-- Remapping the state of a `wordsCfg` remaps its state and leaves the words alone. -/
@[simp]
lemma mapState_wordsCfg {State' : Type*} (φ : Option State → Option State')
    (input : List Symbol) (q : Option State) (ws : Fin k → List Symbol) (out : List Symbol) :
    (wordsCfg input q ws out).mapState φ = wordsCfg input (φ q) ws out := rfl

end Turing
