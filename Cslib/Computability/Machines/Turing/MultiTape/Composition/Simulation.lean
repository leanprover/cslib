/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Composition.Defs

/-!
# Second-phase simulation

The virtual input tape follows the native clamped input head. Two composite steps simulate
one second-machine step, including after the second machine has halted.
-/

@[expose] public section

namespace Turing.MultiTapeTM.Composition

variable {k₀ k₁ : ℕ}
variable {Symbol State₀ State₁ : Type*}

variable (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁)

/-- The virtual input cell in a second-phase embedding is exactly the native input symbol. -/
private lemma embedSecond_inputSymbol
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput) :
    (if inputMode secondCfg.inputPos = .inside then
      (embedSecond tm₀ tm₁ firstCfg secondCfg).workTapeSymbols
        (compositionIntermediateTapeIdx k₀ k₁)
    else none) = secondCfg.inputSymbol := by
  simp only [tapes, Cfg.workTapeSymbols, embedSecond, compositionIntermediateTapeIdx]
  by_cases hleft : secondCfg.inputPos = 0
  · simp [inputMode, hleft, Cfg.inputSymbol]
  · by_cases hright : secondCfg.inputPos.val = secondInput.length + 1
    · simp [inputMode, hleft, hright, Cfg.inputSymbol]
    · have hp : 0 < secondCfg.inputPos.val :=
        Nat.pos_of_ne_zero (fun hz => hleft (Fin.ext hz))
      have hi : secondCfg.inputPos.val - 1 < secondInput.length := by omega
      have hmode : inputMode secondCfg.inputPos = .inside := by
        simp [inputMode, hleft, hright]
      simp only [hmode, ↓reduceIte]
      rw [inputSymbolInner (p := secondCfg.inputPos.val - 1) (by omega) hi]
      have hz : ((secondCfg.inputPos.val : ℤ) - 1) =
          (secondCfg.inputPos.val - 1 : ℕ) := by omega
      rw [show virtualInputPos secondCfg.inputPos =
        (secondCfg.inputPos.val : ℤ) - 1 by rfl, hz]
      simp [listTape, hi]

/-- A second-phase embedding preserves every symbol read from a second-machine work tape. -/
private lemma compositionSecondWorkSymbols_embedSecond
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput) :
    compositionSecondWorkSymbols
      (embedSecond tm₀ tm₁ firstCfg secondCfg).workTapeSymbols =
      secondCfg.workTapeSymbols := by
  funext i
  have hlt : ¬k₀ + 1 + i.val < k₀ := by omega
  have hne : k₀ + 1 + i.val ≠ k₀ := by omega
  simp [compositionSecondWorkSymbols, Cfg.workTapeSymbols, embedSecond,
    compositionSecondTapeIdx, hlt, hne]

/-- The virtual work-tape position follows the clamped native input-head movement. -/
private lemma virtualInputPos_move {input : List Symbol}
    (p : Fin (input.length + 2)) (move : SignType) :
    virtualInputPos (moveInputPos p move) =
      virtualInputPos p + (inputMode p).move move := by
  cases move with
  | zero => simp [CompositionInputMode.move]
  | neg =>
      by_cases hleft : p = 0
      · rw [hleft]
        simp [inputMode, CompositionInputMode.move]
      · rw [moveInputPos_neg_of_ne_left p hleft]
        unfold virtualInputPos
        have hp : 0 < p.val := Nat.pos_of_ne_zero (fun hz => hleft (Fin.ext hz))
        by_cases hright : p.val = input.length + 1 <;>
          simp [inputMode, hleft, hright, CompositionInputMode.move] <;> omega
  | pos =>
      by_cases hright : p.val = input.length + 1
      · have hp : p = ⟨input.length + 1, by omega⟩ := Fin.ext hright
        rw [hp]
        simp [inputMode, CompositionInputMode.move]
      · rw [moveInputPos_pos_of_ne_right p hright]
        unfold virtualInputPos
        by_cases hleft : p = 0 <;>
          simp [inputMode, hleft, hright, CompositionInputMode.move]

/-- The boundary hint selected before a move is left whenever the resulting native position is
the left boundary. -/
private lemma compositionNextBoundary_eq_left {input : List Symbol}
    (p : Fin (input.length + 2)) (move : SignType)
    (hmove : moveInputPos p move = 0) :
    (inputMode p).nextBoundary move = .left := by
  cases move with
  | zero =>
      have hp : p = 0 := by simpa using hmove
      simp [hp, inputMode, CompositionInputMode.nextBoundary]
  | neg => rfl
  | pos =>
      by_cases hright : p.val = input.length + 1
      · have hp : p = ⟨input.length + 1, by omega⟩ := Fin.ext hright
        rw [hp] at hmove
        simp at hmove
      · rw [moveInputPos_pos_of_ne_right p hright] at hmove
        have hp := congrArg Fin.val hmove
        simp at hp

/-- The boundary hint selected before a move is right whenever the resulting native position is
the right boundary. -/
private lemma compositionNextBoundary_eq_right {input : List Symbol}
    (p : Fin (input.length + 2)) (move : SignType)
    (hmove : (moveInputPos p move).val = input.length + 1) :
    (inputMode p).nextBoundary move = .right := by
  cases move with
  | zero =>
      have hright : p.val = input.length + 1 := by simpa using hmove
      have hleft : p ≠ 0 := by
        intro h
        rw [h] at hright
        simp at hright
      simp [inputMode, hright, hleft, CompositionInputMode.nextBoundary]
  | pos => rfl
  | neg =>
      by_cases hleft : p = 0
      · rw [hleft] at hmove
        simp at hmove
      · rw [moveInputPos_neg_of_ne_left p hleft] at hmove
        simp at hmove
        have hp : 0 < p.val := Nat.pos_of_ne_zero (fun hz => hleft (Fin.ext hz))
        omega

/-- Classifying the canonical intermediate tape recovers a native input-head mode, provided the
boundary hint agrees at the two blank boundary cells. -/
private lemma compositionClassifyMode_listTape {input : List Symbol}
    (p : Fin (input.length + 2)) (boundary : CompositionBoundary)
    (hleft : p = 0 → boundary = .left)
    (hright : p.val = input.length + 1 → boundary = .right) :
    compositionClassifyMode
      (listTape input (virtualInputPos p)) boundary =
      inputMode p := by
  by_cases hp0 : p = 0
  · have hb := hleft hp0
    rw [hp0]
    have hv : virtualInputPos (0 : Fin (input.length + 2)) = -1 := by
      unfold virtualInputPos
      simp
    rw [hv]
    simp [compositionClassifyMode, inputMode, hb, CompositionBoundary.inputMode]
    rfl
  · by_cases hpr : p.val = input.length + 1
    · have hb := hright hpr
      have hp : p = ⟨input.length + 1, by omega⟩ := Fin.ext hpr
      rw [hp]
      have hv : virtualInputPos
          (⟨input.length + 1, by omega⟩ : Fin (input.length + 2)) = input.length := by
        unfold virtualInputPos
        omega
      rw [hv]
      simp [compositionClassifyMode, inputMode, hb, CompositionBoundary.inputMode]
    · have hp : 0 < p.val := Nat.pos_of_ne_zero (fun hz => hp0 (Fin.ext hz))
      have hi : p.val - 1 < input.length := by omega
      have hv : virtualInputPos p = (p.val - 1 : ℕ) := by
        unfold virtualInputPos
        omega
      rw [hv]
      simp [compositionClassifyMode, inputMode, hp0, hpr, hi]

/-- Classifying the intermediate cell reached by a virtual move recovers the native clamped
input-head mode after that move. -/
private lemma compositionClassifyMode_move {input : List Symbol}
    (p : Fin (input.length + 2)) (move : SignType) :
    compositionClassifyMode
      (listTape input
        (virtualInputPos p + (inputMode p).move move))
      ((inputMode p).nextBoundary move) =
      inputMode (moveInputPos p move) := by
  rw [← virtualInputPos_move p move]
  apply compositionClassifyMode_listTape
  · exact compositionNextBoundary_eq_left p move
  · exact compositionNextBoundary_eq_right p move

/-- The classifying half of a simulated second-machine step only restores the native input mode. -/
lemma step_classifyCfg
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (boundary : CompositionBoundary)
    (hmode :
      compositionClassifyMode
        (listTape secondInput (virtualInputPos secondCfg.inputPos)) boundary =
        inputMode secondCfg.inputPos) :
    (comp tm₀ tm₁).step
        (classifyCfg tm₀ tm₁ firstCfg secondCfg boundary) =
      embedSecond tm₀ tm₁ firstCfg secondCfg := by
  cases hstate : secondCfg.state with
  | none =>
      simp [step, classifyCfg, embedSecond, hstate]
  | some q =>
      apply Cfg.ext
      · simp [step, classifyCfg, embedSecond, comp, hstate,
          Cfg.workTapeSymbols, compositionIntermediateTapeIdx, hmode]
      · simp [step, classifyCfg, embedSecond, comp, hstate]
      · funext i p
        simp [step, classifyCfg, embedSecond, comp, hstate,
          idleWorkAction]
      · funext i
        simp [step, classifyCfg, embedSecond, comp, hstate,
          idleWorkAction]
      · simp [step, classifyCfg, embedSecond, comp, hstate]

/-- The moving half of a simulated second-machine step performs all native tape actions and enters
the classifier state. -/
private lemma step_embedSecond
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (q : State₁) (hstate : secondCfg.state = some q) :
    (comp tm₀ tm₁).step
        (embedSecond tm₀ tm₁ firstCfg secondCfg) =
      classifyCfg tm₀ tm₁ firstCfg (tm₁.step secondCfg)
        ((inputMode secondCfg.inputPos).nextBoundary
          (tm₁.tr q secondCfg.inputSymbol secondCfg.workTapeSymbols).inputMove) := by
  have hinput := embedSecond_inputSymbol
    tm₀ tm₁ firstCfg secondCfg
  have hwork := compositionSecondWorkSymbols_embedSecond
    tm₀ tm₁ firstCfg secondCfg
  unfold step
  rw [show
    (embedSecond tm₀ tm₁ firstCfg secondCfg).state =
      some (.second q (inputMode secondCfg.inputPos)) by
        simp [embedSecond, hstate]]
  rw [hstate]
  simp only [comp]
  rw [hinput, hwork]
  generalize htr : tm₁.tr q secondCfg.inputSymbol secondCfg.workTapeSymbols = out
  obtain ⟨inputMove, workActions, outS, q'⟩ := out
  simp only [htr]
  apply Cfg.ext
  · cases q' <;> rfl
  · simp [classifyCfg, embedSecond]
  · funext i p
    by_cases hfirst : i.val < k₀
    · simp [classifyCfg, embedSecond, compositionSecondWorkActions,
        hstate, hfirst, idleWorkAction]
    · by_cases hmiddle : i.val = k₀
      · simp [classifyCfg, embedSecond, compositionSecondWorkActions,
          hstate, hmiddle]
      · let j : Fin k₁ := ⟨i.val - (k₀ + 1), by
          have hi := i.isLt
          simp only [compositionTapeCount] at hi
          omega⟩
        cases hwrite : (workActions j).1 with
        | none =>
            simp [classifyCfg, embedSecond,
              compositionSecondWorkActions, hstate, hfirst, hmiddle,
              j, hwrite]
        | some s =>
            simp [classifyCfg, embedSecond,
              compositionSecondWorkActions, hstate, hfirst, hmiddle, j, hwrite]
  · funext i
    by_cases hfirst : i.val < k₀
    · simp [classifyCfg, embedSecond, compositionSecondWorkActions,
        hstate, hfirst, idleWorkAction]
    · by_cases hmiddle : i.val = k₀
      · simp only [tapes, embedSecond, hstate, hmiddle, lt_self_iff_false, ↓reduceDIte,
          compositionSecondWorkActions, classifyCfg]
        exact (virtualInputPos_move secondCfg.inputPos inputMove).symm
      · simp [classifyCfg, embedSecond, compositionSecondWorkActions,
          hstate, hfirst, hmiddle]
  · rfl

/-- One native second-machine step is exactly two steps of the composite machine. -/
private lemma runFrom_two_embedSecond
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput) :
    (comp tm₀ tm₁).runFrom
        (embedSecond tm₀ tm₁ firstCfg secondCfg) 2 =
      embedSecond tm₀ tm₁ firstCfg (tm₁.step secondCfg) := by
  cases hstate : secondCfg.state with
  | none => simp [runFrom, embedSecond, step, hstate]
  | some q =>
      change (comp tm₀ tm₁).step
        ((comp tm₀ tm₁).step (embedSecond tm₀ tm₁ firstCfg secondCfg)) = _
      rw [step_embedSecond tm₀ tm₁ firstCfg secondCfg q hstate]
      apply step_classifyCfg
      unfold step
      rw [hstate]
      generalize htr : tm₁.tr q secondCfg.inputSymbol secondCfg.workTapeSymbols = out
      obtain ⟨inputMove, workActions, outS, q'⟩ := out
      simp only [htr]
      rw [virtualInputPos_move]
      exact compositionClassifyMode_move secondCfg.inputPos inputMove

/-- Simulation of the second machine, at a cost of two composite steps per native step. -/
lemma runFrom_secondPhase
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (n : ℕ) :
    (comp tm₀ tm₁).runFrom
        (embedSecond tm₀ tm₁ firstCfg secondCfg) (2 * n) =
      embedSecond tm₀ tm₁ firstCfg
        (tm₁.runFrom secondCfg n) := by
  induction n with
  | zero => simp [runFrom]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, runFrom_add, ih,
      runFrom_two_embedSecond, runFrom_succ_eq_step']

/-- The odd-numbered composite steps of the second phase are precisely the intermediate
classifier configurations. -/
lemma runFrom_secondPhase_odd
    {firstInput : List Symbol}
    (firstCfg : Cfg k₀ Symbol State₀ firstInput)
    {secondInput : List Symbol}
    (secondCfg : Cfg k₁ Symbol State₁ secondInput)
    (n : ℕ) :
    ∃ boundary,
      (comp tm₀ tm₁).runFrom
          (embedSecond tm₀ tm₁ firstCfg secondCfg) (2 * n + 1) =
        classifyCfg tm₀ tm₁ firstCfg
          (tm₁.runFrom secondCfg (n + 1)) boundary := by
  rw [runFrom_add, runFrom_secondPhase]
  cases hstate : (tm₁.runFrom secondCfg n).state with
  | none =>
    refine ⟨.right, ?_⟩
    change (comp tm₀ tm₁).step
      (embedSecond tm₀ tm₁ firstCfg (tm₁.runFrom secondCfg n)) = _
    rw [runFrom_succ_eq_step', step_of_halt hstate]
    simp [step, embedSecond, classifyCfg, hstate]
  | some q =>
    refine ⟨(inputMode (tm₁.runFrom secondCfg n).inputPos).nextBoundary
      (tm₁.tr q (tm₁.runFrom secondCfg n).inputSymbol
        (tm₁.runFrom secondCfg n).workTapeSymbols).inputMove, ?_⟩
    change (comp tm₀ tm₁).step
      (embedSecond tm₀ tm₁ firstCfg (tm₁.runFrom secondCfg n)) = _
    rw [step_embedSecond tm₀ tm₁ firstCfg _ q hstate, runFrom_succ_eq_step']

end Turing.MultiTapeTM.Composition
