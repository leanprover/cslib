/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TapeContents
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Substituting a work tape for the input tape

The first work tape contains the virtual input. The remaining tapes are the native work tapes.
A classifier distinguishes the two blank boundaries, preserving native head clamping without
extending the alphabet. One native step takes two steps, and the real input head stays parked.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*}

/-- Location of the virtual input head. -/
inductive InputMode
  | left
  | inside
  | right
deriving DecidableEq

instance : Finite InputMode :=
  Finite.of_injective (fun | .left => (0 : Fin 3) | .inside => 1 | .right => 2)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- Boundary toward which a virtual input-head move was made. -/
inductive InputBoundary
  | left
  | right

instance : Finite InputBoundary :=
  Finite.of_injective (fun | .left => true | .right => false)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- Movement of the virtual input head, with outward boundary moves clamped. -/
def InputMode.move : InputMode → SignType → SignType
  | .left, .neg => 0
  | .right, .pos => 0
  | _, move => move

/-- Boundary to use if the cell reached by a virtual input-head move is blank. -/
def InputMode.nextBoundary :
    InputMode → SignType → InputBoundary
  | _, .neg | .left, .zero => .left
  | _, _ => .right

/-- Convert a boundary classifier result to an input mode. -/
def InputBoundary.inputMode : InputBoundary → InputMode
  | .left => .left
  | .right => .right

/-- Control state for the work-tape input simulation. -/
inductive InputState (State : Type*)
  | run (q : State) (mode : InputMode)
  | classify (q : State) (boundary : InputBoundary)

instance [Finite State] : Finite (InputState State) := by
  let := Fintype.ofFinite State
  let := Fintype.ofFinite InputMode
  let := Fintype.ofFinite InputBoundary
  apply Finite.of_injective (fun s : InputState State => match s with
    | .run q mode => ((q, Sum.inl mode) : State × (InputMode ⊕ InputBoundary))
    | .classify q boundary => (q, Sum.inr boundary))
  intro a b h
  cases a <;> cases b <;> simp_all

/-- Classify the cell reached after a virtual input-head movement. -/
def classifyInput (cell : Option Symbol) (boundary : InputBoundary) : InputMode :=
  if cell.isSome then .inside else boundary.inputMode

/-- Use the first work tape as input, and shift native work tapes one index to the right.
The virtual head starts at cell zero; classification also handles empty input. -/
def inputFromWorkTape (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol (InputState State) where
  q₀ := .classify tm.q₀ .right
  tr q _ work := match q with
    | .run q mode =>
      let out := tm.tr q (if mode = .inside then work 0 else none) (fun i => work i.succ)
      ⟨0, Fin.cases (none, mode.move out.inputMove) out.workActions, out.outS,
        out.q'.map fun q => .classify q (mode.nextBoundary out.inputMove)⟩
    | .classify q boundary =>
      ⟨0, fun _ => (none, 0), none, some (.run q (classifyInput (work 0) boundary))⟩

namespace InputFromWorkTape

/-- View a native input-head position as a work-tape position. -/
def virtualInputPos {input : List Symbol} (p : Fin (input.length + 2)) : ℤ :=
  p.val - 1

/-- Classify a native input-head position as the left boundary, an input cell, or the right
boundary. -/
def inputMode {input : List Symbol}
    (p : Fin (input.length + 2)) : InputMode :=
  if p = 0 then .left else if p.val = input.length + 1 then .right else .inside

/-- Embed a native configuration while parking the real input head at `p`. -/
def embed {outerInput input : List Symbol} (p : Fin (outerInput.length + 2))
    (cfg : Cfg k Symbol State input) : Cfg (k + 1) Symbol (InputState State) outerInput where
  state := cfg.state.map fun q => .run q (inputMode cfg.inputPos)
  inputPos := p
  workTapes := Fin.cases (listTape input) cfg.workTapes
  workTapePos := Fin.cases (virtualInputPos cfg.inputPos) cfg.workTapePos
  output := cfg.output

/-- The classifier configuration between the two halves of a simulated step. -/
def classifyCfg {outerInput input : List Symbol} (p : Fin (outerInput.length + 2))
    (cfg : Cfg k Symbol State input) (boundary : InputBoundary) :
    Cfg (k + 1) Symbol (InputState State) outerInput :=
  { embed p cfg with state := cfg.state.map fun q => .classify q boundary }

end InputFromWorkTape

end Turing.MultiTapeTM
