/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Composition of deterministic multi-tape Turing machines

The composite redirects the first machine's output to an intermediate work tape, rewinds it,
and simulates the second machine with that tape as its input. Work tapes occupy disjoint blocks.
A classification step after each simulated input move restores the native boundary behavior.
Both machines use the same alphabet; no extra tape symbols are required.

`comp` is the executable construction. The `Composition` namespace also contains the
configuration embeddings used by the simulation proofs.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k₀ k₁ : ℕ}
variable {Symbol State₀ State₁ : Type*}

/-- Number of work tapes used by the composition of a `k₀`- and a `k₁`-tape machine. -/
abbrev compositionTapeCount (k₀ k₁ : ℕ) := k₀ + 1 + k₁

/-- Physical coordinate of work tape `i` of the first machine. -/
def compositionFirstTapeIdx (k₁ : ℕ) (i : Fin k₀) : Fin (compositionTapeCount k₀ k₁) :=
  i.castSucc.castAdd k₁

/-- Physical coordinate of the tape containing the intermediate output. -/
def compositionIntermediateTapeIdx (k₀ k₁ : ℕ) : Fin (compositionTapeCount k₀ k₁) :=
  (Fin.last k₀).castAdd k₁

/-- Physical coordinate of work tape `i` of the second machine. -/
def compositionSecondTapeIdx (k₀ k₁ : ℕ) (i : Fin k₁) :
    Fin (compositionTapeCount k₀ k₁) :=
  Fin.natAdd (k₀ + 1) i

@[simp]
lemma compositionFirstTapeIdx_val (k₁ : ℕ) (i : Fin k₀) :
    (compositionFirstTapeIdx k₁ i).val = i.val := rfl

@[simp]
lemma compositionIntermediateTapeIdx_val (k₀ k₁ : ℕ) :
    (compositionIntermediateTapeIdx k₀ k₁).val = k₀ := rfl

@[simp]
lemma compositionSecondTapeIdx_val (k₀ : ℕ) (i : Fin k₁) :
    (compositionSecondTapeIdx k₀ k₁ i).val = k₀ + 1 + i.val := rfl

/-- Location of the virtual input head during the second phase. -/
inductive CompositionInputMode
  | left
  | inside
  | right
deriving DecidableEq

/-- Boundary toward which a virtual input-head move was made. -/
inductive CompositionBoundary
  | left
  | right

/-- Control states of a composed multi-tape Turing machine. -/
inductive CompositionState (State₀ State₁ : Type*)
  | first (q : State₀)
  | rewindStart
  | rewind
  | second (q : State₁) (mode : CompositionInputMode)
  | classify (q : State₁) (boundary : CompositionBoundary)

/-- Assemble the first work-tape block, the intermediate tape, and the second block.
The same layout is used for tape contents, head positions, and transition actions. -/
@[simp]
def Composition.tapes {α : Type*} (first : Fin k₀ → α) (middle : α) (second : Fin k₁ → α)
    (i : Fin (compositionTapeCount k₀ k₁)) : α :=
  if h : i.val < k₀ then first ⟨i, h⟩
  else if hmiddle : i.val = k₀ then middle
  else second ⟨i.val - (k₀ + 1), by have := i.isLt; simp only [compositionTapeCount] at *; omega⟩

/-- A work-tape action that neither writes nor moves. -/
def idleWorkAction : Option (Option Symbol) × SignType := (none, 0)

/-- Movement of the virtual input head, with outward boundary moves clamped. -/
def CompositionInputMode.move : CompositionInputMode → SignType → SignType
  | .left, .neg => 0
  | .right, .pos => 0
  | _, move => move

/-- Boundary to use if the cell reached by a virtual input-head move is blank. -/
def CompositionInputMode.nextBoundary :
    CompositionInputMode → SignType → CompositionBoundary
  | _, .neg | .left, .zero => .left
  | _, _ => .right

/-- Convert a boundary classifier result to an input mode. -/
def CompositionBoundary.inputMode : CompositionBoundary → CompositionInputMode
  | .left => .left
  | .right => .right

/-- Read the work symbols seen by the first component machine. -/
def compositionFirstWorkSymbols
    (work : Fin (compositionTapeCount k₀ k₁) → Option Symbol) :
    Fin k₀ → Option Symbol :=
  fun i => work (compositionFirstTapeIdx k₁ i)

/-- Read the work symbols seen by the second component machine. -/
def compositionSecondWorkSymbols
    (work : Fin (compositionTapeCount k₀ k₁) → Option Symbol) :
    Fin k₁ → Option Symbol :=
  fun i => work (compositionSecondTapeIdx k₀ k₁ i)

/-- Embed the first component's work actions and redirect its output to the intermediate tape. -/
def compositionFirstWorkActions
    (actions : Fin k₀ → Option (Option Symbol) × SignType)
    (outS : Option Symbol) :
    Fin (compositionTapeCount k₀ k₁) →
      Option (Option Symbol) × SignType :=
  Composition.tapes actions
    (match outS with | none => idleWorkAction | some s => (some (some s), 1))
    (fun _ => idleWorkAction)

/-- Park every tape except the intermediate tape and move that tape by `move`. -/
def compositionMoveIntermediate (move : SignType) :
    Fin (compositionTapeCount k₀ k₁) →
      Option (Option Symbol) × SignType :=
  Composition.tapes (fun _ => idleWorkAction) (none, move) (fun _ => idleWorkAction)

/-- Embed the second component's work actions and move the intermediate virtual-input tape. -/
def compositionSecondWorkActions
    (inputMove : SignType)
    (actions : Fin k₁ → Option (Option Symbol) × SignType) :
    Fin (compositionTapeCount k₀ k₁) →
      Option (Option Symbol) × SignType :=
  Composition.tapes (fun _ => idleWorkAction) (none, inputMove) actions

/-- Classify a virtual-input cell after moving onto it. -/
def compositionClassifyMode
    (cell : Option Symbol)
    (boundary : CompositionBoundary) : CompositionInputMode :=
  if cell.isSome then .inside else boundary.inputMode

/-- Sequential composition of two deterministic multi-tape Turing machines. -/
def comp
    (tm₀ : MultiTapeTM k₀ Symbol State₀)
    (tm₁ : MultiTapeTM k₁ Symbol State₁) :
    MultiTapeTM (compositionTapeCount k₀ k₁) Symbol
      (CompositionState State₀ State₁) where
  q₀ := .first tm₀.q₀
  tr q input work :=
    match q with
    | .first q₀ =>
        let out := tm₀.tr q₀ input (compositionFirstWorkSymbols work)
        {
          inputMove := out.inputMove
          workActions := compositionFirstWorkActions out.workActions out.outS
          outS := none
          q' := some (match out.q' with
            | some q' => .first q'
            | none => .rewindStart)
        }
    | .rewindStart =>
        {
          inputMove := 0
          workActions := compositionMoveIntermediate (-1)
          outS := none
          q' := some .rewind
        }
    | .rewind =>
        if (work (compositionIntermediateTapeIdx k₀ k₁)).isSome then
          {
            inputMove := 0
            workActions := compositionMoveIntermediate (-1)
            outS := none
            q' := some .rewind
          }
        else
          {
            inputMove := 0
            workActions := compositionMoveIntermediate 1
            outS := none
            q' := some (.classify tm₁.q₀ .right)
          }
    | .second q₁ mode =>
        let inputMove := mode.move
        let out := tm₁.tr q₁
          (if mode = .inside then work (compositionIntermediateTapeIdx k₀ k₁) else none)
          (compositionSecondWorkSymbols work)
        {
          inputMove := 0
          workActions := compositionSecondWorkActions (inputMove out.inputMove) out.workActions
          outS := out.outS
          q' := out.q'.map fun q' => .classify q' (mode.nextBoundary out.inputMove)
        }
    | .classify q₁ boundary =>
        {
          inputMove := 0
          workActions := fun _ => idleWorkAction
          outS := none
          q' := some (.second q₁
            (compositionClassifyMode (work (compositionIntermediateTapeIdx k₀ k₁)) boundary))
        }

namespace Composition

/-- A tape containing exactly the symbols of `xs` at positions `0, ..., xs.length - 1`. -/
def listTape (xs : List Symbol) : ℤ → Option Symbol
  | .ofNat n => xs[n]?
  | .negSucc _ => none

@[simp]
lemma listTape_ofNat (xs : List Symbol) (n : ℕ) : listTape xs n = xs[n]? := rfl

@[simp]
lemma listTape_negSucc (xs : List Symbol) (n : ℕ) : listTape xs (.negSucc n) = none := rfl

/-- Appending one output symbol writes precisely the cell after the existing output. -/
lemma listTape_append_single (xs : List Symbol) (x : Symbol) :
    listTape (xs ++ [x]) = Function.update (listTape xs) (xs.length : ℤ) (some x) := by
  funext z
  cases z with
  | negSucc n => simp [listTape]
  | ofNat n =>
      by_cases h : n = xs.length
      · subst n; simp
      · by_cases hn : n < xs.length
        · simp [List.getElem?_append, hn, h]
        · simp [List.getElem?_append, hn, h, show n - xs.length ≠ 0 by omega]

/-- Embed a first-machine configuration into the first phase of the composite machine. -/
def embedFirst
    (_tm₀ : MultiTapeTM k₀ Symbol State₀)
    (_tm₁ : MultiTapeTM k₁ Symbol State₁)
    {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input) :
    Cfg (compositionTapeCount k₀ k₁) Symbol (CompositionState State₀ State₁) input where
  state := match cfg.state with
    | some q => some (.first q)
    | none => some .rewindStart
  inputPos := cfg.inputPos
  workTapes := tapes cfg.workTapes (listTape cfg.output) (fun _ _ => none)
  workTapePos := tapes cfg.workTapePos cfg.output.length (fun _ => 0)
  output := []

/-- View a native input-head position as a position on the intermediate work tape. -/
def virtualInputPos {input : List Symbol} (p : Fin (input.length + 2)) : ℤ :=
  p.val - 1

/-- Classify a native input-head position as the left boundary, an input cell, or the right
boundary. -/
def inputMode {input : List Symbol}
    (p : Fin (input.length + 2)) : CompositionInputMode :=
  if p = 0 then .left else if p.val = input.length + 1 then .right else .inside

/-- Embed a second-machine configuration into the second phase of the composite machine. -/
def embedSecond
    (_tm₀ : MultiTapeTM k₀ Symbol State₀)
    (_tm₁ : MultiTapeTM k₁ Symbol State₁)
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput) :
    Cfg (compositionTapeCount k₀ k₁) Symbol
      (CompositionState State₀ State₁) firstInput where
  state := match secondCfg.state with
    | some q => some (.second q (inputMode secondCfg.inputPos))
    | none => none
  inputPos := firstCfg.inputPos
  workTapes := tapes firstCfg.workTapes (listTape secondInput) secondCfg.workTapes
  workTapePos := tapes firstCfg.workTapePos
    (virtualInputPos secondCfg.inputPos) secondCfg.workTapePos
  output := secondCfg.output

/-- The intermediate configuration between the moving and classifying halves of a simulated
second-machine step. -/
def classifyCfg
    (_tm₀ : MultiTapeTM k₀ Symbol State₀)
    (_tm₁ : MultiTapeTM k₁ Symbol State₁)
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (boundary : CompositionBoundary) :
    Cfg (compositionTapeCount k₀ k₁) Symbol
      (CompositionState State₀ State₁) firstInput :=
  { embedSecond _tm₀ _tm₁ firstCfg secondCfg with
    state := secondCfg.state.map fun q => .classify q boundary }

/-- A first-phase boundary configuration with a chosen control state and intermediate head
position. -/
def intermediateCfg
    (_tm₀ : MultiTapeTM k₀ Symbol State₀)
    (_tm₁ : MultiTapeTM k₁ Symbol State₁)
    {input : List Symbol}
    (cfg : Cfg k₀ Symbol State₀ input)
    (state : CompositionState State₀ State₁)
    (pos : ℤ) :
    Cfg (compositionTapeCount k₀ k₁) Symbol (CompositionState State₀ State₁) input :=
  { embedFirst _tm₀ _tm₁ cfg with
    state := some state
    workTapePos := fun i =>
      if i.val = k₀ then pos
      else (embedFirst _tm₀ _tm₁ cfg).workTapePos i }

end Composition

end Turing.MultiTapeTM
