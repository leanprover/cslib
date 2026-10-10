/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.MarkWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
public import Cslib.Foundations.Data.Fin.Tuple

/-!
# Reading the input from a word on a work tape

`inputFromWord M mark` runs `M` with its input read from a word on the work tape `Fin.natAdd k 0`
(the *virtual input tape*) instead of from the real input tape, which it never touches.

The head of the virtual input tape stands at cell `p - 1` when the input head of `M` is at position
`p`, so the cells `0, …, w.length - 1` hold the input `w` and the blank cells `-1` and `w.length`
are its two ends. To tell the ends apart, the work tape `Fin.natAdd k 1` (the *flag tape*) holds
`mark` at cell `-1`, and its head moves together with the head of the virtual input tape: a blank
on the virtual input tape is the left end if the flag tape shows `mark` and the right end
otherwise.

`inputFromWord M mark` runs three machines in sequence:

1. `markFlag k (some mark)` writes `mark` to cell `-1` of the flag tape;
2. `inputFromTape M` runs `M` on the virtual input tape;
3. `markFlag k none` erases the mark again.

## Main results

* `Turing.MultiTapeTM.inputFromWord`: the composed machine.
* `Turing.MultiTapeTM.transformsTapes_inputFromWord_of_runFrom`: a run of `M` on the virtual input
  word, from and to `Turing.MultiTapeTM.wordsCfg` configurations, gives a specification of
  `inputFromWord M mark`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*}

/-! ### Reading the input from a work tape -/

/-- The clamped move of the virtual input head: at the left boundary (blank under the virtual
head, flag marked) left moves are blocked, at the right boundary (blank on both) right moves
are. -/
def clampMove (wvip wflag : Option Symbol) (m : SignType) : SignType :=
  match wvip with
  | some _ => m
  | none =>
    match wflag with
    | some _ => (match m with | SignType.neg => SignType.zero | _ => m)
    | none => (match m with | SignType.pos => SignType.zero | _ => m)

/-- `tm`, reading its input from the virtual input tape `Fin.natAdd k 0`, with the flag tape
`Fin.natAdd k 1` marking the cell left of the input. The real input tape is never read and never
moved. -/
noncomputable def inputFromTape (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 2) Symbol State :=
  ofTr tm.q₀ fun q _ work =>
    let a := tm.tr q (work (Fin.natAdd k 0)) fun j => work (j.castAdd 2)
    let m := clampMove (work (Fin.natAdd k 0)) (work (Fin.natAdd k 1)) a.inputTape
    { a with
      inputTape := 0
      workTapes := Fin.append a.workTapes fun _ => (none, m) }

/-- A configuration of `tm` on `input`, as the redirecting machine sees it, over an arbitrary
ambient input: `input` sits on the virtual input tape with the head at cell `inputPos - 1`, the flag
tape carries its mark at `-1` with its head in lockstep, and the ambient input head rests at
`1`. -/
def inCfg (mark : Symbol) {input : List Symbol} (c : Cfg k Symbol State input)
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
lemma inCfg_inputPos (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).inputPos = 1 := rfl

@[simp]
lemma inCfg_workTapes_castAdd (c : Cfg k Symbol State input) (j : Fin k) :
    (inCfg mark c outerInput).workTapes (j.castAdd 2) = c.workTapes j := by
  simp [inCfg]

@[simp]
lemma inCfg_workTapes_vip (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).workTapes (Fin.natAdd k 0) = tapeOfList input := by
  simp [inCfg]

@[simp]
lemma inCfg_workTapes_flag (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).workTapes (Fin.natAdd k 1) =
      Function.update (fun _ => none) (-1) (some mark) := by
  simp [inCfg]

@[simp]
lemma inCfg_workTapePos_castAdd (c : Cfg k Symbol State input) (j : Fin k) :
    (inCfg mark c outerInput).workTapePos (j.castAdd 2) = c.workTapePos j := by
  simp [inCfg]

/-- The virtual input head and the flag head both stand at cell `inputPos - 1`. -/
@[simp]
lemma inCfg_workTapePos_natAdd (c : Cfg k Symbol State input) (i : Fin 2) :
    (inCfg mark c outerInput).workTapePos (Fin.natAdd k i) = (c.inputPos.val : ℤ) - 1 := by
  simp [inCfg]

@[simp]
lemma inCfg_workTapeSymbols_castAdd (c : Cfg k Symbol State input) (j : Fin k) :
    (inCfg mark c outerInput).workTapeSymbols (j.castAdd 2) = c.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- The virtual input head reads exactly what the simulated input head reads: the word cells are
the input positions, the two boundary cells are blank. -/
@[simp]
lemma inCfg_workTapeSymbols_vip (c : Cfg k Symbol State input) :
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
lemma inCfg_workTapeSymbols_flag (c : Cfg k Symbol State input) :
    (inCfg mark c outerInput).workTapeSymbols (Fin.natAdd k 1) =
      if c.inputPos.val = 0 then some mark else none := by
  simp [Cfg.workTapeSymbols, Function.update_apply]

/-- The clamped move of the virtual input head tracks the simulated input head exactly. -/
lemma val_moveInputPos_sub_one_eq_clampMove (mark : Symbol) (c : Cfg k Symbol State input)
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

/-- **The redirection is a step-semiconjugation.** One step of the machine reading its input from
the virtual tape mirrors one step of the original, under the embedding `inCfg`. -/
lemma step_inCfg (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (c : Cfg k Symbol State input) (outerInput : List Symbol) :
    tm.inputFromTape.step (inCfg mark c outerInput) =
      inCfg mark (tm.step c) outerInput := by
  cases hq : c.state with
  | none => simp [inCfg, hq]
  | some q =>
    rw [step_of_state (cfg := inCfg mark c outerInput) hq, step_of_state hq]
    simp only [inputFromTape, tr_ofTr, inCfg_workTapeSymbols_vip, inCfg_workTapeSymbols_flag,
      inCfg_workTapeSymbols_castAdd]
    refine Cfg.ext rfl (by simp [inCfg]) ?_ ?_ rfl <;> funext l <;>
      induction l using Fin.addCases <;> simp [inCfg, val_moveInputPos_sub_one_eq_clampMove mark]

/-- The redirected run mirrors the original. -/
lemma runFrom_inCfg (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (c : Cfg k Symbol State input) (outerInput : List Symbol) (n : ℕ) :
    tm.inputFromTape.runFrom (inCfg mark c outerInput) n =
      inCfg mark (tm.runFrom c n) outerInput :=
  (Function.Semiconj.iterate_right (f := (inCfg mark · outerInput))
    (fun c => (step_inCfg tm mark c outerInput).symm) n c).symm

/-- **Space of the input-redirected machine.** The `k` inner tapes visit exactly what the original
does; the two extra tapes (virtual input, flag) each move only with the simulated input head,
which stays within `[-1, input.length]` — so they add at most `2 * (input.length + 2)`. -/
lemma spaceUsed_inputFromTape (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (c : Cfg k Symbol State input) (outerInput : List Symbol) (n : ℕ) :
    tm.inputFromTape.spaceUsed (inCfg mark c outerInput) n ≤
      tm.spaceUsed c n + 2 * (input.length + 2) := by
  simpa using tm.spaceUsed_le_of_workTapePos_embedding (Fin.castAddEmb 2) c
    (inCfg mark c outerInput) (input.length + 2) (fun m _ j => by simp [runFrom_inCfg])
    fun l hl => by
      induction l using Fin.addCases with
      | left j => exact absurd ⟨j, rfl⟩ hl
      | right i =>
        refine (spaceUsedByTape_le_card _ (S := .Icc (-1) input.length) fun m _ => ?_).trans
          (by rw [Int.card_Icc]; omega)
        have := (tm.runFrom c m).inputPos.isLt
        simp only [runFrom_inCfg, inCfg_workTapePos_natAdd, Finset.mem_Icc]
        omega

end Projections

/-! ### Setting and erasing the flag -/

/-- `markWork write` placed on the flag tape `Fin.natAdd k 1` of a machine with `k + 2` work
tapes: it writes `write` to the cell left of the head of that tape. -/
public noncomputable def markFlag (k : ℕ) (write : Option Symbol) :
    MultiTapeTM (k + 2) Symbol MarkWorkState :=
  (markWork Symbol write).extendTapes (tapeEmb (Fin.natAdd k 1))

/-- `M`, reading its input from the virtual input tape `Fin.natAdd k 0`, with the flag `mark`
written to cell `-1` of the flag tape `Fin.natAdd k 1` before and erased after. -/
public noncomputable def inputFromWord (M : MultiTapeTM k Symbol State) (mark : Symbol) :
    MultiTapeTM (k + 2) Symbol (MarkWorkState ⊕ State ⊕ MarkWorkState) :=
  (markFlag k (some mark)).seq (M.inputFromTape.seq (markFlag k none))

/-- `Turing.MultiTapeTM.inCfg` of a `wordsCfg` configuration: the input `w` on the virtual input
tape, `mark` at cell `-1` of the flag tape, every head at cell `0`. -/
lemma inCfg_wordsCfg (mark : Symbol) {w : List Symbol} (q : Option State)
    (ws : Fin k → List Symbol) (o outer : List Symbol) :
    inCfg mark (wordsCfg w q ws o) outer =
      ⟨q, 1, Fin.append (fun j => tapeOfList (ws j))
          ![tapeOfList w, Function.update (fun _ => none) (-1) (some mark)],
        fun _ => 0, o⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l
  · change (inCfg mark (wordsCfg w q ws o) outer).workTapes l =
      Fin.append (fun j => tapeOfList (ws j))
        ![tapeOfList w, Function.update (fun _ => none) (-1) (some mark)] l
    refine Fin.addCases (fun j => ?_) (fun i => ?_) l
    · rw [Fin.append_left]
      exact inCfg_workTapes_castAdd (mark := mark) (outerInput := outer) (wordsCfg w q ws o) j
    · rw [Fin.append_right]
      match i with
      | 0 | 1 => simp
  · change (inCfg mark (wordsCfg w q ws o) outer).workTapePos l = 0
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) l <;> simp

/-- Updating the flag tape of an appended family of tapes only changes the flag entry. -/
private lemma update_append_flag {α : Type*} (ws₀ : Fin k → α) (a b c : α) :
    Function.update (Fin.append ws₀ ![a, b]) (Fin.natAdd k 1) c = Fin.append ws₀ ![a, c] := by
  rw [← Fin.append_update_right]
  congr 1
  simp [funext_iff, Fin.forall_fin_two]

private lemma markFlag_q₀ (write : Option Symbol) :
    (markFlag k write).q₀ = (markWork Symbol write).q₀ := rfl

/-- The flag tape of a configuration whose tapes are `Fin.append WS ![vip, flag]`, as a one-tape
configuration of `markWork`. -/
private lemma oneTapeCfg_flag {input : List Symbol} (write : Option Symbol)
    (WS : Fin k → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) :
    oneTapeCfg (Fin.natAdd k 1)
        (⟨some (markWork Symbol write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩ :
          Cfg (k + 2) Symbol MarkWorkState input) =
      ⟨some (markWork Symbol write).q₀, ip, fun _ => flag, fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg, Fin.append_right]

/-- In two steps, `markFlag k write` writes `write` to cell `-1` of the flag tape and changes
nothing else. -/
private lemma runFrom_markFlag {input : List Symbol} (write : Option Symbol)
    (WS : Fin k → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) :
    (markFlag k write).runFrom
        (⟨some (markFlag k write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩ :
          Cfg (k + 2) Symbol MarkWorkState input) 2 =
      ⟨none, ip, Fin.append WS ![vip, Function.update flag (-1) write], fun _ => 0, out⟩ := by
  rw [markFlag_q₀, markFlag, runFrom_tapeEmb, oneTapeCfg_flag, runFrom_markWork, embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · simpa using update_append_flag WS vip flag (Function.update flag (-1) write)
  · funext l; simp [Function.update_apply]

/-- `markFlag k write` visits at most `k + 3` cells: two on the flag tape and the starting cell
of each other tape. -/
private lemma spaceUsed_markFlag_le {input : List Symbol} (write : Option Symbol)
    (WS : Fin k → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) (n : ℕ) :
    (markFlag k write).spaceUsed
        (⟨some (markFlag k write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩ :
          Cfg (k + 2) Symbol MarkWorkState input) n ≤ k + 3 := by
  rw [markFlag_q₀]
  refine (spaceUsed_tapeEmb_le (markWork Symbol write) (Fin.natAdd k 1) _ n).trans ?_
  rw [oneTapeCfg_flag]
  have := spaceUsed_markWork_le write ip flag out 0 n
  omega

/-- A `wordsCfg` configuration whose last two words are `w` and the empty word, written out. -/
private lemma wordsCfg_append_words {State' : Type*} {outer : List Symbol} (q : Option State')
    (ws : Fin k → List Symbol) (w out : List Symbol) :
    wordsCfg outer q (Fin.append ws ![w, []]) out =
      ⟨q, 1, Fin.append (fun j => tapeOfList (ws j)) ![tapeOfList w, fun _ => none],
        fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl
    ((Fin.comp_append tapeOfList ws ![w, []]).trans (congrArg _ (funext fun i => ?_))) rfl rfl
  match i with
  | 0 | 1 => simp

open Sequential in
/-- If `M`, run on the input `w` with work tapes `ws₀`, halts after `t` steps with work tapes `ws₁`
and every head back at its start, having emitted `e`, then `inputFromWord M mark` takes the work
tapes `Fin.append ws₀ ![w, []]` to `Fin.append ws₁ ![w, []]` and emits `e`. -/
public theorem transformsTapes_inputFromWord_of_runFrom (mark : Symbol)
    {M : MultiTapeTM k Symbol State} {w e : List Symbol} {ws₀ ws₁ : Fin k → List Symbol}
    {t s : ℕ} (hrun : M.runFrom (wordsCfg w (some M.q₀) ws₀ []) t = wordsCfg w none ws₁ e)
    (hspace : M.spaceUsed (wordsCfg w (some M.q₀) ws₀ []) t ≤ s) :
    TransformsTapes (M.inputFromWord mark)
      (fun _ ws => ws = Fin.append ws₀ ![w, []])
      (fun _ _ ws' em => ws' = Fin.append ws₁ ![w, []] ∧ em = e)
      (t + 4) (s + 2 * (w.length + 2) + 2 * k + 6) := by
  rw [transformsTapes_iff_nil_output]
  rintro outer ws rfl
  -- the three phases of the composed machine
  set setter := markFlag k (some mark) (Symbol := Symbol)
  set eraser := markFlag k none (Symbol := Symbol)
  set core := M.inputFromTape
  -- the configurations in which the core starts and halts
  set cfgCore := inCfg mark (wordsCfg w (some M.q₀) ws₀ []) outer with hcfgCore
  set midCore := inCfg mark (wordsCfg w none ws₁ e) outer with hmidCore
  -- the setter writes the flag
  set midSet : Cfg (k + 2) Symbol MarkWorkState outer :=
    ⟨none, 1, Fin.append (fun j => tapeOfList (ws₀ j))
        ![tapeOfList w, Function.update (fun _ => none) (-1) (some mark)], fun _ => 0, []⟩
    with hmidSet
  have hmid₀ : setter.runFrom
      (wordsCfg outer (some setter.q₀) (Fin.append ws₀ ![w, []]) []) 2 = midSet := by
    rw [wordsCfg_append_words, runFrom_markFlag]
  -- the core mirrors the run of `M`
  have hmid₁ : core.runFrom cfgCore t = midCore := by
    rw [hcfgCore, hmidCore, runFrom_inCfg, hrun]
  have hjunction : midCore.withState (some eraser.q₀) =
      ⟨some eraser.q₀, 1, Fin.append (fun j => tapeOfList (ws₁ j))
          ![tapeOfList w, Function.update (fun _ => none) (-1) (some mark)], fun _ => 0, e⟩ := by
    rw [hmidCore, inCfg_wordsCfg mark (State := State) none ws₁ e outer]
    rfl
  -- the eraser erases the flag
  have hmid₂ : eraser.runFrom (midCore.withState (some eraser.q₀)) 2 =
      wordsCfg outer none (Fin.append ws₁ ![w, []]) e := by
    rw [hjunction, runFrom_markFlag, wordsCfg_append_words, Function.update_idem]
    simp
  have hinner := runFrom_seq (tm₀ := core) (tm₁ := eraser) hmid₁ rfl hmid₂ rfl
  -- the setter halts where the core starts, up to the state
  have hhandoff : midSet.withState (some (core.seq eraser).q₀) = leftCfg eraser cfgCore := by
    rw [hmidSet, hcfgCore, inCfg_wordsCfg mark (State := State) (some M.q₀) ws₀ [] outer]
    rfl
  have hstart : wordsCfg outer (some (M.inputFromWord mark).q₀) (Fin.append ws₀ ![w, []]) [] =
      leftCfg (core.seq eraser)
        (wordsCfg outer (some setter.q₀) (Fin.append ws₀ ![w, []]) []) := rfl
  rw [hstart, show t + 4 = 2 + (t + 2) by omega]
  refine ⟨Fin.append ws₁ ![w, []], e, ?_, ⟨rfl, rfl⟩, ?_⟩
  · rw [inputFromWord, runFrom_seq hmid₀ rfl (hhandoff ▸ hinner) rfl]
    rfl
  · have hsetSpace : setter.spaceUsed
        (wordsCfg outer (some setter.q₀) (Fin.append ws₀ ![w, []]) []) 2 ≤ k + 3 := by
      rw [wordsCfg_append_words]
      exact spaceUsed_markFlag_le (some mark) _ _ _ [] 1 2
    have hcoreSpace : core.spaceUsed cfgCore t ≤ s + 2 * (w.length + 2) :=
      (spaceUsed_inputFromTape M mark (wordsCfg w (some M.q₀) ws₀ []) outer t).trans
        (Nat.add_le_add_right hspace _)
    have herSpace : eraser.spaceUsed (midCore.withState (some eraser.q₀)) 2 ≤ k + 3 := by
      rw [hjunction]
      exact spaceUsed_markFlag_le none _ _ _ e 1 2
    have hinnerSpace :=
      spaceUsed_seq_le (tm₀ := core) (tm₁ := eraser) hmid₁ rfl (by rw [hmid₂]; rfl)
    have houterSpace := spaceUsed_seq_le (tm₀ := setter) (tm₁ := core.seq eraser) hmid₀ rfl
      (by rw [hhandoff, hinner]; rfl)
    rw [hhandoff] at houterSpace
    rw [inputFromWord]
    omega

end Turing.MultiTapeTM
