/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Reading the input from a work tape

`inputFromTape tm` behaves like `tm`, except that it reads its input from a work tape — the
*virtual input tape* — instead of the real one, which it never touches. The virtual input head
lives at cell `p - 1` when the simulated input head is at position `p`, so the word cells
`0, …, len - 1` are the input positions `1, …, len` and the two boundary positions read the blanks
at cells `-1` and `len`.

The one thing a blank cell cannot tell the machine is *which* boundary it is at — and it must
know, because the input head clamps there. This ambiguity is resolved by tracking a boundary
classification. A second fresh work tape, the *flag tape*, moves in lockstep with the virtual input
head and carries a single non-blank `mark` at cell `-1`, so the left boundary is recognised by
reading the flag. Reading blank on both the virtual input tape and the flag tape means the right
boundary.

The configuration map `inCfg` places the simulated input on the virtual input tape, places the
marker on the flag tape, and leaves the real input tape unused. `RunPath.inputFromTape` transports
a path of `tm` to the redirected machine. The main lemmas show that one step and an entire run
of the redirected machine mirror the corresponding step and run of `tm`.
-/

namespace Turing.MultiTapeNTM

variable {k : ℕ} {Symbol State : Type*}

/-- The clamped move of the virtual input head: at the left boundary (blank under the virtual
head, flag marked) left moves are blocked, at the right boundary (blank on both) right moves
are. -/
@[expose] public def clampMove (wvip wflag : Option Symbol) (m : SignType) : SignType :=
  match wvip with
  | some _ => m
  | none =>
    match wflag with
    | some _ => (match m with | SignType.neg => SignType.zero | _ => m)
    | none => (match m with | SignType.pos => SignType.zero | _ => m)

/-- `tm`, reading its input from the virtual input tape `Fin.natAdd k 0`, with the flag tape
`Fin.natAdd k 1` marking the cell left of the input. The real input tape is never read and never
moved. -/
@[expose] public def inputFromTape (tm : MultiTapeNTM k Symbol State) :
    MultiTapeNTM (k + 2) Symbol State where
  q₀ := tm.q₀
  Tr q _ work b := ∃ a, tm.Tr q (work (Fin.natAdd k 0)) (fun j ↦ work (j.castAdd 2)) a ∧
    b = { a with inputTape := 0, workTapes := Fin.append a.workTapes fun _ ↦
      (none, clampMove (work (Fin.natAdd k 0)) (work (Fin.natAdd k 1)) a.inputTape) }

/-- Redirecting the input preserves determinism. -/
public lemma IsDeterministic.inputFromTape {tm : MultiTapeNTM k Symbol State}
    (h : tm.IsDeterministic) : tm.inputFromTape.IsDeterministic := by
  intro q inp work
  obtain ⟨a, ha, hu⟩ := h q (work (Fin.natAdd k 0)) (fun j ↦ work (j.castAdd 2))
  refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
  rintro b ⟨a', ha', rfl⟩
  rw [hu a' ha']

/-- A configuration of `tm` on `input`, as the redirecting machine sees it, over an arbitrary
ambient input: `input` sits on the virtual input tape with the head at cell `inputPos - 1`, the flag
tape carries its mark at `-1` with its head in lockstep, and the ambient input head rests at
`1`. -/
@[expose] public def inCfg (mark : Symbol) {input : List Symbol} (c : Cfg k Symbol State input)
    (outerInput : List Symbol) : Cfg (k + 2) Symbol State outerInput where
  state := c.state
  inputPos := 1
  workTapes := Fin.append c.workTapes
    ![tapeOfList input, Function.update (fun _ ↦ none) (-1) (some mark)]
  workTapePos := Fin.append c.workTapePos (fun _ : Fin 2 ↦ (c.inputPos : ℤ) - 1)
  output := c.output

section Projections

variable {mark : Symbol} {input : List Symbol} {outerInput : List Symbol}

@[simp]
public lemma inCfg_inputPos (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).inputPos = 1 := rfl

@[simp]
public lemma inCfg_workTapes_castAdd (c : Cfg k Symbol State input) (j : Fin k) :
    (inCfg mark c outerInput).workTapes (j.castAdd 2) = c.workTapes j := by
  simp [inCfg]

@[simp]
public lemma inCfg_workTapes_vip (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).workTapes (Fin.natAdd k 0) = tapeOfList input := by
  simp [inCfg]

@[simp]
public lemma inCfg_workTapes_flag (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).workTapes (Fin.natAdd k 1) =
      Function.update (fun _ => none) (-1) (some mark) := by
  simp [inCfg]

@[simp]
public lemma inCfg_workTapePos_castAdd (c : Cfg k Symbol State input) (j : Fin k) :
    (inCfg mark c outerInput).workTapePos (j.castAdd 2) = c.workTapePos j := by
  simp [inCfg]

/-- The virtual input head and the flag head both stand at cell `inputPos - 1`. -/
@[simp]
public lemma inCfg_workTapePos_natAdd (c : Cfg k Symbol State input) (i : Fin 2) :
    (inCfg mark c outerInput).workTapePos (Fin.natAdd k i) = (c.inputPos.val : ℤ) - 1 := by
  simp [inCfg]

@[simp]
public lemma inCfg_workTapeSymbols_castAdd (c : Cfg k Symbol State input) (j : Fin k) :
    (inCfg mark c outerInput).workTapeSymbols (j.castAdd 2) = c.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- The virtual input head reads exactly what the simulated input head reads: the word cells are
the input positions, the two boundary cells are blank. -/
@[simp]
public lemma inCfg_workTapeSymbols_vip (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).workTapeSymbols (Fin.natAdd k 0) = c.inputSymbol := by
  have := c.inputPos.isLt
  rw [Cfg.workTapeSymbols, inCfg_workTapes_vip, inCfg_workTapePos_natAdd]
  obtain h | h | h : c.inputPos.val = 0 ∨ c.inputPos.val = input.length + 1 ∨
      (0 < c.inputPos.val ∧ c.inputPos.val < input.length + 1) := by omega
  · rw [inputSymbol_eq_none_of_boundary (.inl h), h]
    exact tapeOfList_negSucc input 0
  · rw [inputSymbol_eq_none_of_boundary (.inr h), h]; simp
  · rw [inputSymbolInner (c.inputPos.val - 1) (by omega) (by omega),
      show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val - 1 : ℕ) by omega, tapeOfList_ofNat,
      List.getElem?_eq_getElem (by omega)]

/-- The flag head reads the mark exactly at the left boundary. -/
@[simp]
public lemma inCfg_workTapeSymbols_flag (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).workTapeSymbols (Fin.natAdd k 1) =
      if c.inputPos.val = 0 then some mark else none := by
  simp [Cfg.workTapeSymbols, Function.update_apply]

/-- The clamped move of the virtual input head tracks the simulated input head exactly. -/
public lemma val_moveInputPos_sub_one_eq_clampMove (mark : Symbol) (c : Cfg k Symbol State input)
    (m : SignType) :
    ((moveInputPos c.inputPos m).val : ℤ) - 1 =
      ((c.inputPos.val : ℤ) - 1) +
        (clampMove c.inputSymbol (if c.inputPos.val = 0 then some mark else none) m : ℤ) := by
  have := c.inputPos.isLt
  rw [val_moveInputPos_eq]
  obtain h | h | h : c.inputPos.val = 0 ∨ c.inputPos.val = input.length + 1 ∨
      (0 < c.inputPos.val ∧ c.inputPos.val < input.length + 1) := by omega
  · -- left boundary: virtual head blank, flag marked
    rw [inputSymbol_eq_none_of_boundary (.inl h), ite_eq_left h]
    rcases m with _ | _ | _ <;> simp only [clampMove, SignType.cast] <;> omega
  · -- right boundary: virtual head blank, flag unmarked
    rw [inputSymbol_eq_none_of_boundary (.inr h), ite_eq_right (by omega)]
    rcases m with _ | _ | _ <;> simp only [clampMove, SignType.cast] <;> omega
  · -- inside the input: virtual head nonblank
    rw [inputSymbolInner (c.inputPos.val - 1) (by omega) (by omega)]
    rcases m with _ | _ | _ <;> simp only [clampMove, SignType.cast] <;> omega

/-- **The redirection preserves steps.** One step of the machine reading its input from
the virtual tape mirrors one step of the original, under the embedding `inCfg`.
`RunPath.inputFromTape` transports the whole path. -/
public lemma step_inCfg (tm : MultiTapeNTM k Symbol State) (mark : Symbol)
    (outerInput : List Symbol) {c c' : Cfg k Symbol State input} (h : tm.Step c c') :
    tm.inputFromTape.Step (inCfg mark c outerInput) (inCfg mark c' outerInput) := by
  cases hq : c.state with
  | none =>
    obtain rfl := (step_of_halt hq).mp h
    exact (step_of_halt (c := inCfg mark c' outerInput) hq).mpr rfl
  | some q =>
    obtain ⟨a, ha, rfl⟩ := (step_of_state hq).mp h
    refine (step_of_state (c := inCfg mark c outerInput) hq).mpr
      ⟨_, ⟨a, by simpa using ha, rfl⟩, ?_⟩
    simp only [inCfg_workTapeSymbols_vip, inCfg_workTapeSymbols_flag]
    refine Cfg.ext rfl (by simp [inCfg]) ?_ ?_ rfl <;> funext l <;>
      induction l using Fin.addCases <;> simp [inCfg, val_moveInputPos_sub_one_eq_clampMove mark]

/-- A path with its input placed on the virtual input tape, over an arbitrary ambient input. -/
@[expose] public def RunPath.inputFromTape {tm : MultiTapeNTM k Symbol State}
    (p : tm.RunPath input) (mark : Symbol) (outerInput : List Symbol) :
    tm.inputFromTape.RunPath outerInput :=
  p.map ⟨(inCfg mark · outerInput), step_inCfg tm mark outerInput⟩

/-- **Space of the input-redirected machine.** The `k` inner tapes visit exactly what the original
does; the two extra tapes (virtual input, flag) each move only with the simulated input head,
which stays within `[-1, input.length]` — so they add at most `2 * (input.length + 2)`. -/
public lemma RunPath.space_inputFromTape_le {tm : MultiTapeNTM k Symbol State}
    (p : tm.RunPath input) (mark : Symbol) (outerInput : List Symbol) :
    (p.inputFromTape mark outerInput).space ≤ p.space + 2 * (input.length + 2) := by
  simpa [RunPath.inputFromTape] using p.space_map_le
    ⟨(inCfg mark · outerInput), step_inCfg tm mark outerInput⟩ (Fin.castAddEmb 2) (input.length + 2)
    (fun _ _ _ ↦ by simp) fun l hl ↦ by
      induction l using Fin.addCases with
      | left j => exact absurd ⟨j, rfl⟩ hl
      | right i =>
        refine (RunPath.spaceUsedByTape_le_card _ (S := .Icc (-1) input.length) ?_).trans
          (by rw [Int.card_Icc]; omega)
        rintro _ ⟨n, rfl⟩
        change (inCfg mark (p n) outerInput).workTapePos (Fin.natAdd k i) ∈ _
        rw [inCfg_workTapePos_natAdd, Finset.mem_Icc]
        have := (p n).inputPos.isLt
        omega

end Projections

end Turing.MultiTapeNTM
