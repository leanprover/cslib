/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TapeContents
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Basic

/-!
# Rewinding a tape

One controller rewinds either the native input head or a selected work-tape head. It first moves
left, scans left through nonblank cells, then moves right and halts. The initial left move handles
a head starting on the right blank boundary, including when the contents are empty.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The head operated by a rewind machine. -/
inductive RewindHead (k : ℕ)
  | input
  | work (i : Fin k)

/-- Enter the contents before scanning for the left blank boundary. -/
inductive RewindState
  | start
  | scan

instance : Finite RewindState :=
  Finite.of_injective (fun | .start => true | .scan => false)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- Rewind the selected head, retaining all tape contents and accumulated output. -/
def rewind (head : RewindHead k) : MultiTapeTM k Symbol RewindState where
  q₀ := .start
  tr q input work :=
    let cell := match head with | .input => input | .work i => work i
    let done := match q with | .start => false | .scan => !cell.isSome
    let move : SignType := if done then 1 else -1
    ⟨(match head with | .input => move | .work _ => 0),
      (fun i => (none, match head with
        | .input => 0
        | .work j => if i = j then move else 0)),
      none, if done then none else some .scan⟩

namespace Rewind

/-- A rewind configuration at a specified work-tape position. -/
def workCfg (cfg : Cfg k Symbol State input) (i : Fin k)
    (q : Option RewindState) (p : ℤ) : Cfg k Symbol RewindState input :=
  { cfg.withState q with workTapePos := Function.update cfg.workTapePos i p }

/-- A rewind configuration at a specified native input position. -/
def inputCfg (cfg : Cfg k Symbol State input)
    (q : Option RewindState) (p : Fin (input.length + 2)) : Cfg k Symbol RewindState input :=
  { cfg.withState q with inputPos := p }

/-- The initial work-tape move enters the contents from their right boundary. -/
lemma step_work_start (cfg : Cfg k Symbol State input) (i : Fin k) (p : ℤ) :
    (rewind (.work i)).step (workCfg cfg i (some .start) p) =
      workCfg cfg i (some .scan) (p - 1) := by
  ext j z <;> simp [step, rewind, workCfg, Cfg.withState, Function.update_apply, sub_eq_add_neg]
  split_ifs <;> simp_all

/-- Scanning a nonblank work-tape cell moves one position left. -/
lemma step_work_scan (cfg : Cfg k Symbol State input) (i : Fin k) (p : ℤ)
    (h : (cfg.workTapes i p).isSome) :
    (rewind (.work i)).step (workCfg cfg i (some .scan) p) =
      workCfg cfg i (some .scan) (p - 1) := by
  have hn := Option.isSome_iff_ne_none.mp h
  ext j z <;>
    simp [step, rewind, workCfg, Cfg.withState, Cfg.workTapeSymbols, hn,
      Function.update_apply, sub_eq_add_neg]
  split_ifs <;> simp_all

/-- Scanning blank finishes with the head one position to its right. -/
lemma step_work_stop (cfg : Cfg k Symbol State input) (i : Fin k) (p : ℤ)
    (h : cfg.workTapes i p = none) :
    (rewind (.work i)).step (workCfg cfg i (some .scan) p) = workCfg cfg i none (p + 1) := by
  ext j z <;>
    simp [step, rewind, workCfg, Cfg.withState, Cfg.workTapeSymbols, h, Function.update_apply]
  split_ifs <;> simp_all

/-- Every prefix of a work-tape rewind traverses exactly the occupied suffix. -/
lemma runFrom_work_scan (cfg : Cfg k Symbol State input) (i : Fin k) (xs : List Symbol)
    (htape : cfg.workTapes i = listTape xs) (r : ℕ) (hr : r ≤ xs.length) :
    (rewind (.work i)).runFrom (workCfg cfg i (some .scan) (xs.length - 1)) r =
      workCfg cfg i (some .scan) (xs.length - 1 - r) := by
  have hstep (s : ℕ) (hs : s < r) := step_work_scan cfg i (xs.length - 1 - s)
    (by rw [htape]; exact listTape_isSome xs (by omega) (by omega))
  convert runFrom_eq_of_step (rewind (.work i))
    (fun s => workCfg cfg i (some .scan) (xs.length - 1 - s)) r (fun s hs => ?_) using 1
  · simp
  · convert hstep s hs using 1
    congr 1
    omega

/-- Rewind contiguous work-tape contents from the blank cell immediately after them.
This takes `xs.length + 2` steps and preserves the other heads, all contents, and output. -/
lemma runFrom_work (cfg : Cfg k Symbol State input) (i : Fin k) (xs : List Symbol)
    (htape : cfg.workTapes i = listTape xs) :
    (rewind (.work i)).runFrom (workCfg cfg i (some .start) xs.length) (xs.length + 2) =
      workCfg cfg i none 0 := by
  rw [runFrom_succ_eq_step, step_work_start, runFrom_succ_eq_step',
    runFrom_work_scan cfg i xs htape xs.length le_rfl]
  rw [show (xs.length : ℤ) - 1 - xs.length = -1 by omega]
  simpa using step_work_stop cfg i (-1) (by rw [htape]; rfl)

/-- The work-tape rewind does not halt before its final move back to the first cell. -/
lemma work_active (cfg : Cfg k Symbol State input) (i : Fin k) (xs : List Symbol)
    (htape : cfg.workTapes i = listTape xs) (r : ℕ) (hr : r < xs.length + 2) :
    ((rewind (.work i)).runFrom (workCfg cfg i (some .start) xs.length) r).state ≠ none := by
  cases r with
  | zero => simp [workCfg]
  | succ r =>
    rw [runFrom_succ_eq_step, step_work_start, runFrom_work_scan cfg i xs htape r (by omega)]
    simp [workCfg]

/-- The first native-input rewind step moves left, with the native boundary clamp. -/
lemma step_input_start (cfg : Cfg k Symbol State input) (p : Fin (input.length + 2)) :
    (rewind .input).step (inputCfg cfg (some .start) p) =
      inputCfg cfg (some .scan) (moveInputPos p (-1)) := by
  ext i z <;> simp [step, rewind, inputCfg, Cfg.withState]

/-- A nonboundary native-input position takes one step to the left. -/
lemma step_input_scan (cfg : Cfg k Symbol State input) (p : Fin (input.length + 2))
    (hp : 0 < p.val) (hlt : p.val ≤ input.length) :
    (rewind .input).step (inputCfg cfg (some .scan) p) =
      inputCfg cfg (some .scan) (moveInputPos p (-1)) := by
  have hleft : p ≠ 0 := by intro h; subst p; simp at hp
  have hright : p.val ≠ input.length + 1 := by omega
  ext i z <;>
    simp [step, rewind, inputCfg, Cfg.withState, Cfg.inputSymbol, hleft, hright]

/-- At the left blank boundary, move to the initial input position and halt. -/
lemma step_input_stop (cfg : Cfg k Symbol State input) :
    (rewind .input).step (inputCfg cfg (some .scan) 0) = inputCfg cfg none 1 := by
  ext i z <;> simp [step, rewind, inputCfg, Cfg.withState, Cfg.inputSymbol, moveInputPos]

/-- A native input scan reaches its left blank boundary. -/
lemma runFrom_input_scan (cfg : Cfg k Symbol State input) (n : ℕ) (hn : n ≤ input.length) :
    (rewind .input).runFrom (inputCfg cfg (some .scan) ⟨n, by omega⟩) n =
      inputCfg cfg (some .scan) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runFrom_succ_eq_step, step_input_scan cfg _ (by simp) hn]
    have hm : moveInputPos (⟨n + 1, by omega⟩ : Fin (input.length + 2)) (-1) =
        ⟨n, by omega⟩ := by
      apply Fin.ext
      simp [moveInputPos, show n < input.length + 2 by omega]
    rw [hm]
    exact ih (by omega)

/-- Rewind the native input from any legal head position. Both blank boundaries and empty input
are allowed. Only the input head and control state change. -/
lemma runFrom_input (cfg : Cfg k Symbol State input) :
    (rewind .input).runFrom (inputCfg cfg (some .start) cfg.inputPos)
        (cfg.inputPos.val - 1 + 2) = inputCfg cfg none 1 := by
  rw [runFrom_succ_eq_step, step_input_start, runFrom_succ_eq_step']
  have hm : moveInputPos cfg.inputPos (-1) =
      (⟨cfg.inputPos.val - 1, by have := cfg.inputPos.isLt; omega⟩ : Fin (input.length + 2)) := by
    apply Fin.ext
    simp [moveInputPos]
    split_ifs <;> simp_all <;> omega
  rw [hm, runFrom_input_scan cfg _ (by have := cfg.inputPos.isLt; omega), step_input_stop]

end Rewind

end Turing.MultiTapeTM
