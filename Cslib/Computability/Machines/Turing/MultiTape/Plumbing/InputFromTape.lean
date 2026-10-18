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
marker on the flag tape, and leaves the real input tape unused. The main lemmas show that one step
and an entire run path of the redirected machine mirror the corresponding step and run path of `tm`.

`inputFromWord M mark` reads the input from a word on the virtual input tape, with blank work tapes
around it. It runs three machines in sequence:

1. `markFlag k (some mark)` writes `mark` to cell `-1` of the flag tape;
2. `inputFromTape M` runs `M` on the virtual input tape;
3. `markFlag k none` erases the mark again.

## Main definitions

* `Turing.MultiTapeTM.inputFromTape`: the machine reading its input from a work tape.
* `Turing.MultiTapeTM.inCfgHom`: the configuration map `inCfg` as a step-preserving map, which maps
  run paths.
* `Turing.MultiTapeTM.inputFromWord`: the machine reading its input from a word on a work tape.

## Main results

* `Turing.MultiTapeTM.step_inCfg`: one step of the redirected machine mirrors one step of `tm`.
* `Turing.MultiTapeTM.space_map_inCfgHom_le`: the space bound for a redirected path.
* `Turing.MultiTapeTM.transformsTapes_inputFromWord`: a run path of `M` on the virtual input word,
  from and to `Turing.MultiTapeTM.wordsCfg` configurations, gives a specification of
  `inputFromWord M mark`.
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

/-- `tm`, reading its input from the virtual input tape `Fin.natAdd k 0`, with the flag tape
`Fin.natAdd k 1` marking the cell left of the input. The real input tape is never read and never
moved. -/
@[expose] public noncomputable def inputFromTape (tm : MultiTapeTM k Symbol State) :
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

/-- **The redirection is a step-semiconjugation.** One step of the machine reading its input from
the virtual tape mirrors one step of the original, under the embedding `inCfg`. -/
public lemma step_inCfg (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (outerInput : List Symbol) :
    Function.Semiconj (inCfg (input := input) mark · outerInput) tm.step tm.inputFromTape.step := by
  intro c
  symm
  cases hq : c.state with
  | none => simp [inCfg, hq]
  | some q =>
    rw [step_of_state (cfg := inCfg mark c outerInput) hq, step_of_state hq]
    simp only [inputFromTape, tr_ofTr, inCfg_workTapeSymbols_vip, inCfg_workTapeSymbols_flag,
      inCfg_workTapeSymbols_castAdd]
    refine Cfg.ext rfl (by simp [inCfg]) ?_ ?_ rfl <;> funext l <;>
      induction l using Fin.addCases <;> simp [inCfg, val_moveInputPos_sub_one_eq_clampMove mark]

/-- The redirection preserves steps, so it maps run paths of `tm` to run paths of the redirected
machine. -/
@[expose, simps! apply] public noncomputable def inCfgHom (tm : MultiTapeTM k Symbol State)
    (mark : Symbol) (outerInput : List Symbol) :
    (tm.stepRel input).Hom (tm.inputFromTape.stepRel outerInput) :=
  stepHom (inCfg mark · outerInput) (step_inCfg tm mark outerInput)

/-- **Space of the input-redirected path.** The `k` inner tapes visit exactly what the original
path visits; the two extra tapes (virtual input, flag) each move only with the simulated input
head, which stays within `[-1, input.length]`, so they add at most `2 * (input.length + 2)`. -/
public lemma space_map_inCfgHom_le (tm : MultiTapeTM k Symbol State) (mark : Symbol)
    (outerInput : List Symbol) (p : tm.RunPath input) :
    (p.map (inCfgHom tm mark outerInput)).space ≤ p.space + 2 * (input.length + 2) := by
  refine (p.space_map_le _ (Fin.castAddEmb 2) (fun _ => .Icc (-1) input.length)
    (fun c _ => inCfg_workTapePos_castAdd c) fun c _ l hl => ?_).trans
    (by simp [Finset.card_compl]; omega)
  induction l using Fin.addCases with
  | left j => exact absurd ⟨j, rfl⟩ hl
  | right i =>
    have := c.inputPos.isLt
    simp only [inCfgHom_apply, inCfg_workTapePos_natAdd, Finset.mem_Icc]
    omega

end Projections

/-! ### Setting and erasing the flag -/

/-- `markWork write` placed on the flag tape, the last of `k + 2` work tapes: it writes `write` to
the cell left of the head of that tape. -/
@[expose] public noncomputable def markFlag (k : ℕ) (write : Option Symbol) :
    MultiTapeTM (k + 2) Symbol MarkWorkState :=
  (markWork Symbol write).extendTapes (tapeEmb (Fin.natAdd k 1))

/-- `M`, reading its input from a word on the virtual input tape `Fin.natAdd k 0`, with `mark`
written to cell `-1` of the flag tape, the last work tape, before and erased after. -/
@[expose] public noncomputable def inputFromWord (M : MultiTapeTM k Symbol State) (mark : Symbol) :
    MultiTapeTM (k + 2) Symbol (MarkWorkState ⊕ State ⊕ MarkWorkState) :=
  (markFlag k (some mark)).seq (M.inputFromTape.seq (markFlag k none))

/-- `Turing.MultiTapeTM.inCfg` of a `wordsCfg` configuration: the input `w` on the virtual input
tape, `mark` at cell `-1` of the flag tape, every head at cell `0`. -/
public lemma inCfg_wordsCfg (mark : Symbol) {w : List Symbol} (q : Option State)
    (ws : Fin k → List Symbol) (o outer : List Symbol) :
    inCfg mark (wordsCfg w q ws o) outer =
      ⟨q, 1, Fin.append (fun j => tapeOfList (ws j))
          ![tapeOfList w, Function.update (fun _ => none) (-1) (some mark)],
        fun _ => 0, o⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> cases l using Fin.addCases with
  | left j => simp [inCfg, wordsCfg]
  | right i => match i with | 0 | 1 => simp [inCfg, wordsCfg]

/-- Updating the flag tape of an appended family of tapes only changes the flag entry. -/
private lemma update_append_flag {α : Type*} (ws₀ : Fin k → α) (a b c : α) :
    Function.update (Fin.append ws₀ ![a, b]) (Fin.natAdd k 1) c = Fin.append ws₀ ![a, c] := by
  rw [← Fin.append_update_right]
  congr 1
  simp [funext_iff, Fin.forall_fin_two]

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
nothing else: it runs `markWork write` on the flag tape. -/
private lemma exists_runPath_markFlag {input : List Symbol} (write : Option Symbol)
    (WS : Fin k → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) :
    ∃ p : (markFlag k write).RunPath input,
      p.head = ⟨some (markFlag k write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩ ∧
      p.last = ⟨none, ip, Fin.append WS ![vip, Function.update flag (-1) write], fun _ => 0, out⟩ ∧
      p.time = 2 ∧ p.space ≤ k + 4 := by
  let cfg : Cfg (k + 2) Symbol MarkWorkState input :=
    ⟨some (markWork Symbol write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩
  let r := MultiTapeNTM.RunPath.ofDeterministic (markWork Symbol write)
    (oneTapeCfg (Fin.natAdd k 1) cfg) 2
  refine ⟨r.map (embedHom _ (tapeEmb (Fin.natAdd k 1)) cfg.workTapes cfg.workTapePos),
    embed_oneTapeCfg _ cfg, ?_, rfl, ?_⟩
  · change embed _ ((markWork Symbol write).runFrom (oneTapeCfg _ cfg) 2) _ _ = _
    rw [oneTapeCfg_flag, runFrom_markWork, embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · simpa [cfg] using update_append_flag WS vip flag (Function.update flag (-1) write)
    · funext l; simp [cfg, Function.update_apply]
  · -- `markWork` takes two steps on one tape, every other tape stays where it is
    have : r.space ≤ 1 * (2 + 1) := r.space_le_mul_time_add_one
    exact (space_map_embedHom_le ..).trans (by omega)

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

section Flag

variable (mark : Symbol) (ws : Fin k → List Symbol) (w out outer : List Symbol)

/-- Setting the flag on a `wordsCfg` configuration leads to the configuration in which
`inputFromTape` starts. -/
private lemma exists_runPath_setFlag :
    ∃ p : (markFlag k (some mark)).RunPath outer,
      p.head = wordsCfg outer (some (markFlag k (some mark)).q₀) (Fin.append ws ![w, []]) out ∧
      p.last = inCfg mark (wordsCfg w (none : Option MarkWorkState) ws out) outer ∧
      p.time = 2 ∧ p.space ≤ k + 4 := by
  rw [wordsCfg_append_words, inCfg_wordsCfg]
  exact exists_runPath_markFlag _ _ _ _ _ _

/-- Erasing the flag on the configuration in which `inputFromTape` halts leads to a `wordsCfg`
configuration. -/
private lemma exists_runPath_eraseFlag :
    ∃ p : (markFlag (Symbol := Symbol) k none).RunPath outer,
      p.head = (inCfg mark (wordsCfg w (none : Option State) ws out) outer).withState
        (some (markFlag (Symbol := Symbol) k none).q₀) ∧
      p.last = wordsCfg outer none (Fin.append ws ![w, []]) out ∧
      p.time = 2 ∧ p.space ≤ k + 4 := by
  obtain ⟨p, hh, hl, ht, hs⟩ := exists_runPath_markFlag none (fun j => tapeOfList (ws j))
    (tapeOfList w) (Function.update (fun _ => none) (-1) (some mark)) out
    (1 : Fin (outer.length + 2))
  refine ⟨p, by rw [hh, inCfg_wordsCfg]; rfl, ?_, ht, hs⟩
  rw [hl, wordsCfg_append_words, Function.update_idem]
  simp

end Flag

open Sequential in
/-- If `M`, run on the input `w` with work tapes `ws₀`, has a run path of at most `t` steps and `s`
cells to the halting configuration with work tapes `ws₁`, every head back at its start, having
emitted `e`, then `inputFromWord M mark` takes the work tapes `Fin.append ws₀ ![w, []]` to
`Fin.append ws₁ ![w, []]` and emits `e`. -/
public theorem transformsTapes_inputFromWord (mark : Symbol)
    {M : MultiTapeTM k Symbol State} {w e : List Symbol} {ws₀ ws₁ : Fin k → List Symbol}
    {t s : ℕ} (hM : ∃ p : M.RunPath w, p.head = wordsCfg w (some M.q₀) ws₀ [] ∧
      p.last = wordsCfg w none ws₁ e ∧ p.time ≤ t ∧ p.space ≤ s) :
    TransformsTapes (M.inputFromWord mark)
      (fun _ ws => ws = Fin.append ws₀ ![w, []])
      (fun _ _ ws' em => ws' = Fin.append ws₁ ![w, []] ∧ em = e)
      (t + 4) (s + 2 * w.length + 2 * k + 12) := by
  obtain ⟨pM, hh, hl, ht, hs⟩ := hM
  unfold inputFromWord
  rw [transformsTapes_iff_nil_output]
  rintro outer _ rfl
  -- set the flag, run `M` on the virtual input tape, erase the flag
  obtain ⟨p₀, hh₀, hl₀, ht₀, hs₀⟩ := exists_runPath_setFlag mark ws₀ w [] outer
  let p₁ := pM.map (inCfgHom M mark outer)
  have hl₁ : p₁.last = inCfg mark (wordsCfg w none ws₁ e) outer := by simp [p₁, hl]
  have hs₁ : p₁.space ≤ pM.space + 2 * (w.length + 2) := space_map_inCfgHom_le M mark outer pM
  obtain ⟨p₂, hh₂, hl₂, ht₂, hs₂⟩ := exists_runPath_eraseFlag (State := State) mark ws₁ w e outer
  obtain ⟨p₁₂, hh₁₂, hl₁₂, ht₁₂, hs₁₂⟩ := exists_runPath_seq_space_le (p₀ := p₁) (p₁ := p₂)
    (by rw [hl₁]; rfl) (by rw [hh₂, hl₁]) (by rw [hl₂]; rfl)
  obtain ⟨p, hph, hpl, hpt, hps⟩ := exists_runPath_seq_space_le (p₀ := p₀) (p₁ := p₁₂)
    (by rw [hl₀]; rfl) (by simp [hh₁₂, p₁, hh, hl₀]; rfl) (by rw [hl₁₂, hl₂]; rfl)
  refine ⟨_, e, ⟨rfl, rfl⟩, p, by rw [hph, hh₀]; rfl, by simp [hpl, hl₁₂, hl₂, rightCfg], ?_, ?_⟩
  · simp only [MultiTapeNTM.RunPath.time] at ht ht₀ ht₂ ⊢
    have : p₁.length = pM.length := rfl
    omega
  · omega

end Turing.MultiTapeTM
