/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromWorkTape.Defs

/-! # Correctness of work-tape input substitution -/

@[expose] public section

namespace Turing.MultiTapeTM.InputFromWorkTape

variable {k : ℕ} {Symbol State : Type*}
variable (tm : MultiTapeTM k Symbol State)
variable {outerInput input : List Symbol} (p : Fin (outerInput.length + 2))

/-- The virtual work-tape position follows the clamped native input-head movement. -/
private lemma virtualInputPos_move {input : List Symbol}
    (p : Fin (input.length + 2)) (move : SignType) :
    virtualInputPos (moveInputPos p move) =
      virtualInputPos p + (inputMode p).move move := by
  cases move with
  | zero => simp [InputMode.move]
  | neg =>
      by_cases hleft : p = 0
      · rw [hleft]
        simp [inputMode, InputMode.move]
      · rw [moveInputPos_neg_of_ne_left p hleft]
        unfold virtualInputPos
        have hp : 0 < p.val := Nat.pos_of_ne_zero (fun hz => hleft (Fin.ext hz))
        by_cases hright : p.val = input.length + 1 <;>
          simp [inputMode, hleft, hright, InputMode.move] <;> omega
  | pos =>
      by_cases hright : p.val = input.length + 1
      · have hp : p = ⟨input.length + 1, by omega⟩ := Fin.ext hright
        rw [hp]
        simp [inputMode, InputMode.move]
      · rw [moveInputPos_pos_of_ne_right p hright]
        unfold virtualInputPos
        by_cases hleft : p = 0 <;>
          simp [inputMode, hleft, hright, InputMode.move]

/-- The boundary hint selected before a move is left whenever the resulting native position is
the left boundary. -/
private lemma nextBoundary_eq_left {input : List Symbol}
    (p : Fin (input.length + 2)) (move : SignType)
    (hmove : moveInputPos p move = 0) :
    (inputMode p).nextBoundary move = .left := by
  cases move <;>
    simp_all [inputMode, InputMode.nextBoundary, moveInputPos]
  split_ifs at hmove <;> simp_all

/-- The boundary hint selected before a move is right whenever the resulting native position is
the right boundary. -/
private lemma nextBoundary_eq_right {input : List Symbol}
    (p : Fin (input.length + 2)) (move : SignType)
    (hmove : (moveInputPos p move).val = input.length + 1) :
    (inputMode p).nextBoundary move = .right := by
  cases move <;>
    simp_all [inputMode, InputMode.nextBoundary, moveInputPos] <;>
    split_ifs at * <;> simp_all <;> omega

/-- Classifying the virtual input tape recovers the native input-head mode, provided the
boundary hint agrees at the two blank boundary cells. -/
private lemma classifyInput_listTape {input : List Symbol}
    (p : Fin (input.length + 2)) (boundary : InputBoundary)
    (hleft : p = 0 → boundary = .left)
    (hright : p.val = input.length + 1 → boundary = .right) :
    classifyInput
      (listTape input (virtualInputPos p)) boundary =
      inputMode p := by
  by_cases hp0 : p = 0
  · simp [hp0, hleft hp0, virtualInputPos, inputMode,
      classifyInput, InputBoundary.inputMode, listTape]
    rfl
  · by_cases hpr : p.val = input.length + 1
    · simp [virtualInputPos, hpr, hright hpr, inputMode, hp0,
        classifyInput, InputBoundary.inputMode]
    · have hp : 0 < p.val := Nat.pos_of_ne_zero (fun hz => hp0 (Fin.ext hz))
      have hi : p.val - 1 < input.length := by omega
      have hv : virtualInputPos p = (p.val - 1 : ℕ) := by
        unfold virtualInputPos
        omega
      simp [hv, classifyInput, inputMode, hp0, hpr, hi]

/-- Classifying the cell reached by a virtual move recovers the native clamped
input-head mode after that move. -/
private lemma classifyInput_move {input : List Symbol}
    (p : Fin (input.length + 2)) (move : SignType) :
    classifyInput
      (listTape input
        (virtualInputPos p + (inputMode p).move move))
      ((inputMode p).nextBoundary move) =
      inputMode (moveInputPos p move) := by
  rw [← virtualInputPos_move p move]
  apply classifyInput_listTape
  · exact nextBoundary_eq_left p move
  · exact nextBoundary_eq_right p move


/-- The simulated input symbol is exactly the symbol on the virtual tape. -/
private lemma embed_inputSymbol (cfg : Cfg k Symbol State input) :
    (if inputMode cfg.inputPos = .inside then (embed p cfg).workTapeSymbols 0 else none) =
      cfg.inputSymbol := by
  simp only [Cfg.workTapeSymbols, embed, Fin.cases_zero]
  by_cases hleft : cfg.inputPos = 0
  · simp [inputMode, hleft, Cfg.inputSymbol]
  · by_cases hright : cfg.inputPos.val = input.length + 1
    · simp [inputMode, hleft, hright, Cfg.inputSymbol]
    · have hp : 0 < cfg.inputPos.val := Nat.pos_of_ne_zero (fun hz => hleft (Fin.ext hz))
      have hi : cfg.inputPos.val - 1 < input.length := by omega
      have hv : virtualInputPos cfg.inputPos = (cfg.inputPos.val - 1 : ℕ) := by
        unfold virtualInputPos
        omega
      rw [inputSymbolInner (p := cfg.inputPos.val - 1) (by omega) hi]
      simp [inputMode, hleft, hright, hv, listTape, hi]

/-- Classification restores the native boundary mode and changes no tapes. -/
lemma step_classifyCfg (cfg : Cfg k Symbol State input) (boundary : InputBoundary)
    (hmode : classifyInput (listTape input (virtualInputPos cfg.inputPos)) boundary =
      inputMode cfg.inputPos) :
    tm.inputFromWorkTape.step (classifyCfg p cfg boundary) = embed p cfg := by
  cases hs : cfg.state with
  | none => simp [step, classifyCfg, embed, hs]
  | some q =>
    ext i z <;>
      simp [step, classifyCfg, embed, inputFromWorkTape, hs, Cfg.workTapeSymbols, hmode]

/-- The moving half of a simulated step performs the native tape actions. -/
lemma step_embed (cfg : Cfg k Symbol State input) (q : State) (hs : cfg.state = some q) :
    tm.inputFromWorkTape.step (embed p cfg) =
      classifyCfg p (tm.step cfg)
        ((inputMode cfg.inputPos).nextBoundary
          (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).inputMove) := by
  have hwork : (fun i : Fin k => (embed p cfg).workTapeSymbols i.succ) = cfg.workTapeSymbols := by
    funext i
    simp [embed, Cfg.workTapeSymbols]
  unfold step
  rw [show (embed p cfg).state = some (.run q (inputMode cfg.inputPos)) by
    simp [embed, hs], hs]
  simp only [inputFromWorkTape]
  rw [embed_inputSymbol p cfg, hwork]
  generalize htr : tm.tr q cfg.inputSymbol cfg.workTapeSymbols = out
  simp only [htr]
  apply Cfg.ext
  · rfl
  · simp [classifyCfg, embed]
  · funext i z
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [classifyCfg, embed]
    · cases hw : (out.workActions j).1 <;> simp [classifyCfg, embed, hw]
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [classifyCfg, embed] using (virtualInputPos_move cfg.inputPos out.inputMove).symm
    · simp [classifyCfg, embed]
  · rfl

/-- Every native step is simulated in two steps, including after a native halt. -/
lemma runFrom_two (cfg : Cfg k Symbol State input) :
    tm.inputFromWorkTape.runFrom (embed p cfg) 2 = embed p (tm.step cfg) := by
  cases hs : cfg.state with
  | none => simp [runFrom, step, embed, hs]
  | some q =>
    change tm.inputFromWorkTape.step (tm.inputFromWorkTape.step (embed p cfg)) = _
    rw [step_embed tm p cfg q hs]
    apply step_classifyCfg
    simpa only [step, hs, virtualInputPos_move] using
      classifyInput_move cfg.inputPos (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).inputMove

/-- The native run is simulated on a work tape with a factor of two in time. -/
lemma runFrom_embed (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm.inputFromWorkTape.runFrom (embed p cfg) (2 * n) = embed p (tm.runFrom cfg n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, runFrom_add, ih,
      runFrom_two, runFrom_succ_eq_step']

/-- Odd simulation steps are classifier configurations. -/
lemma runFrom_odd (cfg : Cfg k Symbol State input) (n : ℕ) :
    ∃ boundary, tm.inputFromWorkTape.runFrom (embed p cfg) (2 * n + 1) =
      classifyCfg p (tm.runFrom cfg (n + 1)) boundary := by
  rw [runFrom_add, runFrom_embed]
  cases hs : (tm.runFrom cfg n).state with
  | none =>
    refine ⟨.right, ?_⟩
    change tm.inputFromWorkTape.step (embed p (tm.runFrom cfg n)) = _
    rw [runFrom_succ_eq_step', step_of_halt hs]
    simp [step, embed, classifyCfg, hs]
  | some q =>
    refine ⟨(inputMode (tm.runFrom cfg n).inputPos).nextBoundary
      (tm.tr q (tm.runFrom cfg n).inputSymbol (tm.runFrom cfg n).workTapeSymbols).inputMove, ?_⟩
    change tm.inputFromWorkTape.step (embed p (tm.runFrom cfg n)) = _
    rw [step_embed tm p _ q hs, runFrom_succ_eq_step']

/-- The initial classifier enters the native initial configuration, also for empty input. -/
lemma step_init :
    tm.inputFromWorkTape.step (classifyCfg p (tm.initCfg input) .right) =
      embed p (tm.initCfg input) := by
  apply step_classifyCfg
  cases input <;>
    simp [classifyInput, inputMode, virtualInputPos, InputBoundary.inputMode, listTape]

/-- A prepared work tape can replace the native input at any real input position. -/
lemma runFrom_init (n : ℕ) :
    tm.inputFromWorkTape.runFrom (classifyCfg p (tm.initCfg input) .right) (2 * n + 1) =
      embed p (tm.runFrom (tm.initCfg input) n) := by
  rw [runFrom_succ_eq_step, step_init, runFrom_embed]

end Turing.MultiTapeTM.InputFromWorkTape
