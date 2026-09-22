/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.StepLemmas
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Reading the input from a work tape

`inputFromTape tm mark` behaves like `tm`, except that it reads its input from a work tape — the
*virtual input tape* — instead of the real one, which it never touches. The virtual input head
lives at cell `p - 1` when the simulated input head is at position `p`, so the word cells
`0, …, len - 1` are the input positions `1, …, len` and the two boundary positions read the blanks
at cells `-1` and `len`.

The one thing a blank cell cannot tell the machine is *which* boundary it is at — and it must
know, because the input head clamps there. Redirecting the input through a work tape is due to
Samuel Schlesinger (leanprover/cslib#872), who resolves the ambiguity by tracking a boundary
classification in the finite control. Here a *flag tape* is used instead, in the spirit of the
footprint anchors of the tidy normal form: a second fresh tape, whose head moves in lockstep with
the virtual input head, carries a single `mark` at cell `-1` — placed by a two-step prologue — so
the left boundary is recognised by reading the flag. Reading blank on both tapes then means the
right boundary. With the classification on a tape rather than in the control, the simulated
configuration determines the simulating one, and the redirection is an unconditional
step-semiconjugation: one `Turing.MultiTapeTM.runFrom_comm_of_step`, no bisimulation.
-/

namespace Turing.MultiTapeTM

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

/-- `tm`, reading its input from the virtual input tape `⟨k, _⟩`, with the flag tape `⟨k + 1, _⟩`
marking the cell left of the input. The real input tape is never read and never moved. -/
@[expose] public def inputFromTape (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 2) Symbol State where
  q₀ := tm.q₀
  tr q _ work :=
    let a := tm.tr q (work ⟨k, by omega⟩) fun j => work (j.castAdd 2)
    let m := clampMove (work ⟨k, by omega⟩) (work ⟨k + 1, by omega⟩) a.inputTape
    { inputTape := 0
      workTapes := fun l =>
        if h : l.val < k then a.workTapes ⟨l.val, h⟩ else (none, m)
      output := a.output
      state := a.state }

/-- A configuration of `tm` on input `I`, as the redirecting machine sees it, over an arbitrary
ambient input: `I` sits on the virtual input tape with the head at cell `inputPos - 1`, the flag
tape carries its mark at `-1` with its head in lockstep, and the ambient input head rests at
`1`. -/
@[expose] public def inCfg (mark : Symbol) {I : List Symbol} (c : Cfg k Symbol State I)
    (outerInput : List Symbol) : Cfg (k + 2) Symbol State outerInput :=
  ⟨c.state, 1,
    fun l => if h : l.val < k then c.workTapes ⟨l.val, h⟩
      else if l.val = k then tapeOfList I
      else Function.update (fun _ => none) (-1) (some mark),
    fun l => if h : l.val < k then c.workTapePos ⟨l.val, h⟩ else ((c.inputPos.val : ℤ) - 1),
    c.output⟩

section Projections

variable {mark : Symbol} {I : List Symbol} {outerInput : List Symbol}

@[simp]
public lemma inCfg_inputPos (c : Cfg k Symbol State I) :
    (inCfg mark c outerInput).inputPos = 1 := rfl

@[simp]
public lemma inCfg_workTapes_castAdd (c : Cfg k Symbol State I) (j : Fin k) :
    (inCfg mark c outerInput).workTapes (j.castAdd 2) = c.workTapes j := by
  have h : (j.castAdd 2).val < k := j.isLt
  change (if h : (j.castAdd 2).val < k then c.workTapes ⟨(j.castAdd 2).val, h⟩ else _) = _
  rw [dite_eq_left h]
  exact congrArg _ (Fin.ext (by simp))

@[simp]
public lemma inCfg_workTapes_vip (c : Cfg k Symbol State I) :
    (inCfg mark c outerInput).workTapes ⟨k, by omega⟩ = tapeOfList I := by
  change (if h : k < k then _ else if (k : ℕ) = k then tapeOfList I else _) = _
  rw [dite_eq_right (by omega), ite_eq_left rfl]

@[simp]
public lemma inCfg_workTapes_flag (c : Cfg k Symbol State I) :
    (inCfg mark c outerInput).workTapes ⟨k + 1, by omega⟩ =
      Function.update (fun _ => none) (-1) (some mark) := by
  change (if h : k + 1 < k then _ else if k + 1 = k then _ else
    Function.update (fun _ => none) (-1) (some mark)) = _
  rw [dite_eq_right (by omega), ite_eq_right (by omega)]

@[simp]
public lemma inCfg_workTapePos_castAdd (c : Cfg k Symbol State I) (j : Fin k) :
    (inCfg mark c outerInput).workTapePos (j.castAdd 2) = c.workTapePos j := by
  have h : (j.castAdd 2).val < k := j.isLt
  change (if h : (j.castAdd 2).val < k then c.workTapePos ⟨(j.castAdd 2).val, h⟩ else _) = _
  rw [dite_eq_left h]
  exact congrArg _ (Fin.ext (by simp))

@[simp]
public lemma inCfg_workTapePos_vip (c : Cfg k Symbol State I) :
    (inCfg mark c outerInput).workTapePos ⟨k, by omega⟩ = ((c.inputPos.val : ℤ) - 1) := by
  change (if h : k < k then _ else ((c.inputPos.val : ℤ) - 1)) = _
  rw [dite_eq_right (by omega)]

@[simp]
public lemma inCfg_workTapePos_flag (c : Cfg k Symbol State I) :
    (inCfg mark c outerInput).workTapePos ⟨k + 1, by omega⟩ = ((c.inputPos.val : ℤ) - 1) := by
  change (if h : k + 1 < k then _ else ((c.inputPos.val : ℤ) - 1)) = _
  rw [dite_eq_right (by omega)]

@[simp]
public lemma inCfg_workTapeSymbols_castAdd (c : Cfg k Symbol State I) (j : Fin k) :
    (inCfg mark c outerInput).workTapeSymbols (j.castAdd 2) = c.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- The virtual input head reads exactly what the simulated input head reads: the word cells are
the input positions, the two boundary cells are blank. -/
public lemma vip_read (c : Cfg k Symbol State I) :
    tapeOfList I ((c.inputPos.val : ℤ) - 1) = c.inputSymbol := by
  rcases Nat.eq_zero_or_pos c.inputPos.val with h0 | h1
  · rw [show ((c.inputPos.val : ℤ) - 1) = Int.negSucc 0 from by omega, tapeOfList_negSucc,
      inputSymbol_eq_none_of_boundary (Or.inl h0)]
  · rw [show ((c.inputPos.val : ℤ) - 1) = ((c.inputPos.val - 1 : ℕ) : ℤ) from by omega,
      tapeOfList_ofNat]
    rcases Nat.lt_or_ge (c.inputPos.val) (I.length + 1) with hlt | hge
    · rw [Cfg.inputSymbol, dite_eq_right (fun he => by rw [he] at h1; simp at h1),
        dite_eq_right (fun he => by
          have hv : c.inputPos.val = I.length + 1 := by rw [he]
          omega)]
      rw [List.getElem?_eq_getElem (by omega)]
    · have hv : c.inputPos.val = I.length + 1 := by have := c.inputPos.isLt; omega
      rw [List.getElem?_eq_none (by omega), inputSymbol_eq_none_of_boundary (Or.inr hv)]

/-- The flag head reads the mark exactly at the left boundary. -/
public lemma flag_read (mark : Symbol) (c : Cfg k Symbol State I) :
    Function.update (fun _ => (none : Option Symbol)) (-1) (some mark)
      ((c.inputPos.val : ℤ) - 1) = if c.inputPos.val = 0 then some mark else none := by
  by_cases h0 : c.inputPos.val = 0
  · rw [ite_eq_left h0, show ((c.inputPos.val : ℤ) - 1) = -1 from by omega, Function.update_self]
  · rw [ite_eq_right h0, Function.update_of_ne (by omega)]

/-- The clamped move tracks the simulated input head exactly. -/
public lemma clampMove_correct (mark : Symbol) (c : Cfg k Symbol State I) (m : SignType) :
    ((moveInputPos c.inputPos m).val : ℤ) - 1 =
      ((c.inputPos.val : ℤ) - 1) +
        (clampMove c.inputSymbol (if c.inputPos.val = 0 then some mark else none) m : ℤ) := by
  have hlen : c.inputPos.val ≤ I.length + 1 := by have := c.inputPos.isLt; omega
  rcases Nat.eq_zero_or_pos c.inputPos.val with h0 | h1
  · -- left boundary: virtual head blank, flag marked
    rw [inputSymbol_eq_none_of_boundary (Or.inl h0), ite_eq_left h0]
    rcases m with _ | _ | _ <;>
      simp only [clampMove, val_moveInputPos_eq, min_def, max_def, SignType.cast] <;>
      split_ifs <;> omega
  · rcases Nat.lt_or_ge (c.inputPos.val) (I.length + 1) with hlt | hge
    · -- inside the input: virtual head nonblank
      obtain ⟨b, hb⟩ : ∃ b, c.inputSymbol = some b := by
        rw [Cfg.inputSymbol, dite_eq_right (fun he => by rw [he] at h1; simp at h1),
          dite_eq_right (fun he => by
            have hv : c.inputPos.val = I.length + 1 := by rw [he]
            omega)]
        exact ⟨_, rfl⟩
      rw [hb]
      rcases m with _ | _ | _ <;>
        simp only [clampMove, val_moveInputPos_eq, min_def, max_def, SignType.cast] <;>
        split_ifs <;> omega
    · -- right boundary: virtual head blank, flag unmarked
      have hv : c.inputPos.val = I.length + 1 := by omega
      rw [inputSymbol_eq_none_of_boundary (Or.inr hv), ite_eq_right (by omega)]
      rcases m with _ | _ | _ <;>
        simp only [clampMove, val_moveInputPos_eq, min_def, max_def, SignType.cast] <;>
        split_ifs <;> omega

/-- Reading the sim machine's input argument: the virtual input head reads what the simulated
input head reads. -/
private lemma inCfg_vip_symbol (mark : Symbol) (c : Cfg k Symbol State I)
    (outerInput : List Symbol) :
    (inCfg mark c outerInput).workTapeSymbols ⟨k, by omega⟩ = c.inputSymbol := by
  rw [Cfg.workTapeSymbols, inCfg_workTapes_vip, inCfg_workTapePos_vip, vip_read]

/-- Reading the sim machine's flag: marked exactly at the left boundary. -/
private lemma inCfg_flag_symbol (mark : Symbol) (c : Cfg k Symbol State I)
    (outerInput : List Symbol) :
    (inCfg mark c outerInput).workTapeSymbols ⟨k + 1, by omega⟩ =
      (if c.inputPos.val = 0 then some mark else none) := by
  rw [Cfg.workTapeSymbols, inCfg_workTapes_flag, inCfg_workTapePos_flag, flag_read]

/-- Decompose a tape index of the redirecting machine: an original work tape, the virtual input
tape, or the flag tape. -/
private lemma tape_cases (l : Fin (k + 2)) :
    (∃ j : Fin k, l = j.castAdd 2 ∧ l.val < k) ∨ l = ⟨k, by omega⟩ ∨ l = ⟨k + 1, by omega⟩ := by
  rcases Nat.lt_trichotomy l.val k with h | h | h
  · refine Or.inl ⟨⟨l.val, h⟩, ?_, h⟩
    apply Fin.ext
    simp
  · exact Or.inr (Or.inl (Fin.ext (by simp [h])))
  · have := l.isLt
    exact Or.inr (Or.inr (Fin.ext (by simp; omega)))

/-- **The redirection is a step-semiconjugation.** One step of the machine reading its input from
the virtual tape mirrors one step of the original, under the embedding `inCfg`. -/
public lemma step_inCfg (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (c : Cfg k Symbol State I) (outerInput : List Symbol) :
    tm.inputFromTape.step (inCfg mark c outerInput) =
      inCfg mark (tm.step c) outerInput := by
  cases hq : c.state with
  | none =>
    have h1 : (inCfg mark c outerInput).state = none := by rw [inCfg]; exact hq
    rw [step_of_halt h1, step_of_halt hq]
  | some q =>
    have h1 : (inCfg mark c outerInput).state = some q := by rw [inCfg]; exact hq
    have harg : tm.inputFromTape.tr q (inCfg mark c outerInput).inputSymbol
        (inCfg mark c outerInput).workTapeSymbols =
        (let a := tm.tr q c.inputSymbol c.workTapeSymbols
          let m := clampMove c.inputSymbol
            (if c.inputPos.val = 0 then some mark else none) a.inputTape
          { inputTape := 0
            workTapes := fun l => if h : l.val < k then a.workTapes ⟨l.val, h⟩ else (none, m)
            output := a.output
            state := a.state } : Action (k + 2) Symbol State) := by
      simp only [inputFromTape, inCfg_vip_symbol, inCfg_flag_symbol,
        inCfg_workTapeSymbols_castAdd]
    rw [step_apply_of_state h1, harg]
    set a := tm.tr q c.inputSymbol c.workTapeSymbols with ha
    have hstepc : tm.step c = a.apply c := step_apply_of_state hq
    rw [hstepc]
    have hmc := clampMove_correct (I := I) mark c a.inputTape
    have hip : (a.apply c).inputPos = moveInputPos c.inputPos a.inputTape := rfl
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · simp only [Action.apply_inputPos, moveInputPos_zero, inCfg]
    · funext l z
      rcases tape_cases l with ⟨j, rfl, hjk⟩ | rfl | rfl
      · simp only [Action.apply_workTapes, Fin.val_castAdd, dite_eq_left j.isLt, Fin.eta,
          inCfg_workTapes_castAdd, inCfg_workTapePos_castAdd]
      · have hnk : ¬ ((⟨k, by omega⟩ : Fin (k + 2)).val < k) := by simp
        simp only [Action.apply_workTapes, dite_eq_right hnk, inCfg_workTapes_vip]
      · have hnk1 : ¬ ((⟨k + 1, by omega⟩ : Fin (k + 2)).val < k) := by simp
        simp only [Action.apply_workTapes, dite_eq_right hnk1, inCfg_workTapes_flag]
    · funext l
      rcases tape_cases l with ⟨j, rfl, hjk⟩ | rfl | rfl
      · simp only [Action.apply_workTapePos, Fin.val_castAdd, dite_eq_left j.isLt, Fin.eta,
          inCfg_workTapePos_castAdd]
      · have hnk : ¬ ((⟨k, by omega⟩ : Fin (k + 2)).val < k) := by simp
        simp only [Action.apply_workTapePos, dite_eq_right hnk, inCfg_workTapePos_vip,
          Action.apply_inputPos]
        omega
      · have hnk1 : ¬ ((⟨k + 1, by omega⟩ : Fin (k + 2)).val < k) := by simp
        simp only [Action.apply_workTapePos, dite_eq_right hnk1, inCfg_workTapePos_flag,
          Action.apply_inputPos]
        omega

/-- The redirected run mirrors the original. -/
public lemma runFrom_inCfg (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (c : Cfg k Symbol State I) (outerInput : List Symbol) (n : ℕ) :
    tm.inputFromTape.runFrom (inCfg mark c outerInput) n =
      inCfg mark (tm.runFrom c n) outerInput :=
  runFrom_comm_of_step (fun c => inCfg mark c outerInput)
    (fun c => step_inCfg tm mark c outerInput) c n

/-- **Space of the input-redirected machine.** The `k` inner tapes visit exactly what the original
does; the two extra tapes (virtual input, flag) each move only with the simulated input head,
which stays within `[-1, I.length]` — so they add at most `2 * (I.length + 2)`. -/
public lemma spaceUsed_inputFromTape (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (c : Cfg k Symbol State I) (outerInput : List Symbol) (n : ℕ) :
    tm.inputFromTape.spaceUsed (inCfg mark c outerInput) n ≤
      tm.spaceUsed c n + 2 * (I.length + 2) := by
  classical
  have hmir : ∀ m, tm.inputFromTape.runFrom (inCfg mark c outerInput) m =
      inCfg mark (tm.runFrom c m) outerInput := fun m => runFrom_inCfg tm mark c outerInput m
  -- the inner tapes: same visited set as the original (heads agree under `inCfg`)
  have hcast : ∀ j : Fin k, tm.inputFromTape.visitedByTapeHead (inCfg mark c outerInput) n
      (j.castAdd 2) = tm.visitedByTapeHead c n j := by
    intro j
    refine Finset.image_congr fun m _ => ?_
    rw [hmir m, inCfg_workTapePos_castAdd]
  -- an extra tape's head lies in `[-1, I.length]` at every step
  have hextra : ∀ l : Fin (k + 2), l = ⟨k, by omega⟩ ∨ l = ⟨k + 1, by omega⟩ →
      tm.inputFromTape.visitedByTapeHead (inCfg mark c outerInput) n l ⊆
        Finset.Icc (-1 : ℤ) (I.length : ℤ) := by
    intro l hl z hz
    obtain ⟨m, hm, rfl⟩ := mem_visitedByTapeHead.mp hz
    rw [hmir m]
    have hb := (tm.runFrom c m).inputPos.isLt
    rcases hl with rfl | rfl
    · rw [inCfg_workTapePos_vip]; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · rw [inCfg_workTapePos_flag]; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hextra_card : ∀ l : Fin (k + 2), l = ⟨k, by omega⟩ ∨ l = ⟨k + 1, by omega⟩ →
      tm.inputFromTape.spaceUsedByTape (inCfg mark c outerInput) n l ≤ I.length + 2 := by
    intro l hl
    refine le_trans (Finset.card_le_card (hextra l hl)) ?_
    rw [Int.card_Icc]; omega
  -- split the tape sum: inner tapes + the two extra
  rw [spaceUsed, Fin.sum_univ_add]
  have hinner : ∑ j : Fin k, tm.inputFromTape.spaceUsedByTape (inCfg mark c outerInput) n
      (j.castAdd 2) = tm.spaceUsed c n := by
    rw [spaceUsed]
    exact Finset.sum_congr rfl fun j _ => congrArg Finset.card (hcast j)
  have htwo : ∑ j : Fin 2, tm.inputFromTape.spaceUsedByTape (inCfg mark c outerInput) n
      (j.natAdd k) ≤ 2 * (I.length + 2) := by
    rw [Fin.sum_univ_two]
    have e0 := hextra_card ((0 : Fin 2).natAdd k) (Or.inl (Fin.ext (by simp)))
    have e1 := hextra_card ((1 : Fin 2).natAdd k) (Or.inr (Fin.ext (by simp)))
    omega
  rw [hinner]
  exact Nat.add_le_add_left htwo _


end Projections

end Turing.MultiTapeTM
