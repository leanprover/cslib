/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.MarkWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg

/-!
# Reading the input from a word on a work tape

`inputFromWord M mark` turns `M` into a machine that reads its input from a *word* sitting on a
work tape — the virtual input tape — instead of the real input tape, which it never touches. It is
the input-redirection `Turing.MultiTapeTM.inputFromTape` wrapped in the two-step bookkeeping that
sets up and tears down the boundary flag the redirection relies on: a setter writes the flag `mark`
into the cell left of the word before the core runs, and an eraser removes it afterwards, so the
machine starts and finishes in the word normal form.

The flag tape is the last of the two added tapes, `Fin.natAdd k' 1`; the virtual input word lives
on `Fin.natAdd k' 0`. The word on the virtual input tape is read but never written, so it survives
the run unchanged; the inner machine's emitted output is forwarded to the real output.

## Main results

* `Turing.MultiTapeTM.inputFromWord`: the composed machine.
* `Turing.MultiTapeTM.transformsTapes_inputFromWord_of_runFrom`: given a tidy run of `M` on the
  virtual input word, the composed machine transforms its tapes accordingly.
-/

namespace Turing.MultiTapeTM

variable {k' : ℕ} {Symbol State : Type*}

/-- `inputFromWord M mark`: `M`, reading its input from the virtual input word on tape
`Fin.natAdd k' 0`, with the boundary flag `mark` on tape `Fin.natAdd k' 1` set before the core runs
and erased afterwards. -/
public noncomputable def inputFromWord (M : MultiTapeTM k' Symbol State) (mark : Symbol) :
    MultiTapeTM (k' + 2) Symbol (MarkWorkState ⊕ State ⊕ MarkWorkState) :=
  ((markWork Symbol (some mark)).extendTapes (tapeEmb (Fin.natAdd k' 1))).seq
    (M.inputFromTape.seq ((markWork Symbol none).extendTapes (tapeEmb (Fin.natAdd k' 1))))

/-- The configuration the input-redirection sees on a `wordsCfg`: the virtual input word `w` on
tape `Fin.natAdd k' 0`, the flag `mark` at cell `-1` on tape `Fin.natAdd k' 1`, the inner words on
the remaining tapes, every head at its start. This is the junction between the bookkeeping phases
and the core. -/
public lemma inCfg_wordsCfg (mark : Symbol) {w : List Symbol} (q : Option State)
    (ws : Fin k' → List Symbol) (o outer : List Symbol) :
    inCfg mark (wordsCfg w q ws o) outer =
      ⟨q, 1, Fin.append (fun j => tapeOfList (ws j))
          ![tapeOfList w, Function.update (fun _ => none) (-1) (some mark)],
        fun _ => 0, o⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext l
    change (inCfg mark (wordsCfg w q ws o) outer).workTapes l =
      Fin.append (fun j => tapeOfList (ws j))
        ![tapeOfList w, Function.update (fun _ => none) (-1) (some mark)] l
    refine Fin.addCases (fun j => ?_) (fun i => ?_) l
    · rw [Fin.append_left]
      exact inCfg_workTapes_castAdd (mark := mark) (outerInput := outer) (wordsCfg w q ws o) j
    · rw [Fin.append_right]
      match i with
      | 0 => simp
      | 1 => simp
  · funext l
    change (inCfg mark (wordsCfg w q ws o) outer).workTapePos l = 0
    refine Fin.addCases (fun j => ?_) (fun i => ?_) l
    · simp
    · simp

/-- Updating the flag tape of an appended tape family at the last index rewrites only the flag
slot of the `![·, ·]` pair. -/
private lemma update_append_flag {α : Type*} (ws₀ : Fin k' → α) (a b c : α) :
    Function.update (Fin.append ws₀ ![a, b]) (Fin.natAdd k' 1) c = Fin.append ws₀ ![a, c] := by
  funext l
  refine Fin.addCases (fun j => ?_) (fun i => ?_) l
  · rw [Function.update_of_ne (Fin.ne_of_val_ne (by simp [Fin.natAdd, Fin.castAdd]; omega)),
      Fin.append_left, Fin.append_left]
  · rw [Fin.append_right]
    match i with
    | 0 =>
      rw [Function.update_of_ne (Fin.ne_of_val_ne (by simp [Fin.natAdd])), Fin.append_right]
      simp
    | 1 => rw [Function.update_self]; simp

/-- One bookkeeping phase: placing `markWork write` on the flag tape `Fin.natAdd k' 1` and running
it for its two steps writes `write` into the flag's cell `-1`, touching nothing else. -/
private lemma runFrom_bookkeeping {input : List Symbol} (write : Option Symbol)
    (WS : Fin k' → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) :
    ((markWork Symbol write).extendTapes (tapeEmb (Fin.natAdd k' (1 : Fin 2)))).runFrom
        (⟨some ((markWork Symbol write).extendTapes
            (tapeEmb (Fin.natAdd k' (1 : Fin 2)))).q₀, ip,
          Fin.append WS ![vip, flag], fun _ => 0, out⟩ :
          Cfg (k' + 2) Symbol MarkWorkState input) 2 =
      ⟨none, ip, Fin.append WS ![vip, Function.update flag (-1) write], fun _ => 0, out⟩ := by
  rw [extendTapes_q₀, runFrom_tapeEmb]
  have hone : oneTapeCfg (Fin.natAdd k' 1)
      (⟨some (markWork Symbol write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩ :
        Cfg (k' + 2) Symbol MarkWorkState input) =
      ⟨some (markWork Symbol write).q₀, ip, fun _ => flag, fun _ => 0, out⟩ := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg, Fin.append_right]
  rw [hone, runFrom_markWork, embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · simpa using update_append_flag WS vip flag (Function.update flag (-1) write)
  · funext l; simp [Function.update_apply]

/-- A word configuration whose last two words are `w` and the empty flag word, as an explicit
configuration: the shape in which a bookkeeping phase starts and finishes. -/
private lemma wordsCfg_append_words {State' : Type*} {outer : List Symbol} (q : Option State')
    (ws : Fin k' → List Symbol) (w out : List Symbol) :
    wordsCfg outer q (Fin.append ws ![w, []]) out =
      ⟨q, 1, Fin.append (fun j => tapeOfList (ws j)) ![tapeOfList w, fun _ => none],
        fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl
    ((tapeOfList_comp_append ws ![w, []]).trans (congrArg _ (funext fun i => ?_))) rfl rfl
  match i with
  | 0 => simp
  | 1 => simp

/-- The one-tape `markWork` machine visits at most two cells: its head stays within `[p-1, p]`. -/
private lemma spaceUsed_markWork_le {input : List Symbol} (write : Option Symbol)
    (ip : Fin (input.length + 2)) (tp : ℤ → Option Symbol) (out : List Symbol) (p : ℤ) (n : ℕ) :
    (markWork Symbol write).spaceUsed ⟨some (markWork Symbol write).q₀, ip,
        fun _ => tp, fun _ => p, out⟩ n ≤ 2 := by
  rw [spaceUsed, Fin.sum_univ_one]
  refine (spaceUsedByTape_le_card _ (S := .Icc (p - 1) p) fun m _ => ?_).trans ?_
  · exact Finset.mem_Icc.2 (workTapePos_runFrom_markWork write ip tp out p m)
  · rw [Int.card_Icc]; omega

/-- A bookkeeping phase visits at most `k' + 3` cells: two on the flag tape, one on each of the
`k' + 1` tapes it never touches. -/
private lemma spaceUsed_bookkeeping_le {input : List Symbol} (write : Option Symbol)
    (WS : Fin k' → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) :
    ((markWork Symbol write).extendTapes (tapeEmb (Fin.natAdd k' (1 : Fin 2)))).spaceUsed
        (⟨some ((markWork Symbol write).extendTapes (tapeEmb (Fin.natAdd k' (1 : Fin 2)))).q₀, ip,
          Fin.append WS ![vip, flag], fun _ => 0, out⟩ :
          Cfg (k' + 2) Symbol MarkWorkState input) n ≤ k' + 3 := by
  refine (spaceUsed_tapeEmb_le (markWork Symbol write) (Fin.natAdd k' (1 : Fin 2)) _ n).trans ?_
  have hone : oneTapeCfg (Fin.natAdd k' (1 : Fin 2))
      (⟨some ((markWork Symbol write).extendTapes (tapeEmb (Fin.natAdd k' (1 : Fin 2)))).q₀, ip,
          Fin.append WS ![vip, flag], fun _ => 0, out⟩ :
        Cfg (k' + 2) Symbol MarkWorkState input) =
      ⟨some (markWork Symbol write).q₀, ip, fun _ => flag, fun _ => 0, out⟩ := by
    rw [extendTapes_q₀]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg, Fin.append_right]
  rw [hone]
  have := spaceUsed_markWork_le write ip flag out 0 n
  omega

open Sequential in
/-- **Reading the input from a work tape.** Given a tidy run of `M` that reads the virtual input
word `w` from its first tape, resetting the simulated input head so the virtual input head returns
to cell `0`, the composed machine `inputFromWord M mark` performs the same transformation on the
`k' + 2` work tapes — the inner words become `ws₁`, the virtual input word `w` and the flag word
stay as they were — and forwards the inner emission `e` to the real output. -/
public theorem transformsTapes_inputFromWord_of_runFrom {k' : ℕ} {Symbol State : Type*}
    (mark : Symbol) {M : MultiTapeTM k' Symbol State} {w e : List Symbol}
    {ws₀ ws₁ : Fin k' → List Symbol} {t s : ℕ}
    (hrun : M.runFrom (wordsCfg w (some M.q₀) ws₀ []) t = wordsCfg w none ws₁ e)
    (hspace : M.spaceUsed (wordsCfg w (some M.q₀) ws₀ []) t ≤ s) :
    TransformsTapes (M.inputFromWord mark)
      (fun _ ws => ws = Fin.append ws₀ ![w, []])
      (fun _ _ ws' em => ws' = Fin.append ws₁ ![w, []] ∧ em = e)
      (t + 4) (s + 2 * (w.length + 2) + 2 * k' + 6) := by
  rw [transformsTapes_iff_nil_output]
  rintro outer ws rfl
  -- the three phases of the composed machine
  set setter := (markWork Symbol (some mark)).extendTapes (tapeEmb (Fin.natAdd k' (1 : Fin 2)))
    with hsetter
  set eraser := (markWork Symbol none).extendTapes (tapeEmb (Fin.natAdd k' (1 : Fin 2)))
    with heraser
  set core := M.inputFromTape with hcore
  -- the core's initial configuration on the virtual input word, and the junction it halts in
  set cfgCore := inCfg mark (wordsCfg w (some M.q₀) ws₀ []) outer with hcfgCore
  set midCore := inCfg mark (wordsCfg w none ws₁ e) outer with hmidCore
  -- the setter writes the flag, halting in the core's initial words (bar its state)
  set midSet : Cfg (k' + 2) Symbol MarkWorkState outer :=
    ⟨none, 1, Fin.append (fun j => tapeOfList (ws₀ j))
        ![tapeOfList w, Function.update (fun _ => none) (-1) (some mark)], fun _ => 0, []⟩
    with hmidSet
  have hmid₀ : setter.runFrom
      (wordsCfg outer (some setter.q₀) (Fin.append ws₀ ![w, []]) []) 2 = midSet := by
    rw [hsetter, wordsCfg_append_words, runFrom_bookkeeping]
  -- the core mirrors the run of `M`, leaving the junction for the eraser
  have hmid₁ : core.runFrom cfgCore t = midCore := by
    rw [hcfgCore, hmidCore, hcore, runFrom_inCfg, hrun]
  -- the junction the core halts in, seen as the eraser's starting configuration
  have hjunction : midCore.withState (some eraser.q₀) =
      ⟨some eraser.q₀, 1, Fin.append (fun j => tapeOfList (ws₁ j))
          ![tapeOfList w, Function.update (fun _ => none) (-1) (some mark)], fun _ => 0, e⟩ := by
    rw [hmidCore, inCfg_wordsCfg mark (State := State) none ws₁ e outer]
    rfl
  -- the eraser clears the flag, returning to the word normal form
  have hmid₂ : eraser.runFrom (midCore.withState (some eraser.q₀)) 2 =
      wordsCfg outer none (Fin.append ws₁ ![w, []]) e := by
    rw [hjunction, heraser, runFrom_bookkeeping, wordsCfg_append_words]
    refine Cfg.ext rfl rfl ?_ rfl rfl
    rw [show Function.update (Function.update (fun _ : ℤ => none) (-1) (some mark)) (-1) none =
      (fun _ => none) by rw [Function.update_idem]; simp]
  -- the inner sequential composition: core, then eraser
  have hinner := runFrom_seq (tm₀ := core) (tm₁ := eraser) hmid₁ rfl hmid₂ rfl
  -- the handoff from the setter to the inner machine agrees on the state-free part
  have hhandoff : midSet.withState (some (core.seq eraser).q₀) = leftCfg eraser cfgCore := by
    rw [hmidSet, hcfgCore, inCfg_wordsCfg mark (State := State) (some M.q₀) ws₀ [] outer]
    refine Cfg.ext rfl rfl rfl rfl rfl
  -- the outer composition: setter, then the inner machine
  have hwo : M.inputFromWord mark = setter.seq (core.seq eraser) := rfl
  have hstart : wordsCfg outer (some (setter.seq (core.seq eraser)).q₀)
      (Fin.append ws₀ ![w, []]) [] =
      leftCfg (core.seq eraser)
        (wordsCfg outer (some setter.q₀) (Fin.append ws₀ ![w, []]) []) := rfl
  have ht : t + 4 = 2 + (t + 2) := by omega
  refine ⟨Fin.append ws₁ ![w, []], e, ?_, ⟨rfl, rfl⟩, ?_⟩
  · rw [hwo, hstart, ht, runFrom_seq hmid₀ rfl (hhandoff ▸ hinner) rfl]
    rfl
  · rw [hwo, hstart, ht]
    -- the setter and the eraser: bookkeeping phases; the core: the inner run on the virtual word
    have hsetSpace : setter.spaceUsed
        (wordsCfg outer (some setter.q₀) (Fin.append ws₀ ![w, []]) []) 2 ≤ k' + 3 := by
      rw [hsetter, wordsCfg_append_words]
      exact spaceUsed_bookkeeping_le (some mark) _ _ _ [] 1
    have hcoreSpace : core.spaceUsed cfgCore t ≤ s + 2 * (w.length + 2) := by
      rw [hcfgCore, hcore]
      exact (spaceUsed_inputFromTape M mark (wordsCfg w (some M.q₀) ws₀ []) outer t).trans
        (Nat.add_le_add_right hspace _)
    have herSpace : eraser.spaceUsed (midCore.withState (some eraser.q₀)) 2 ≤ k' + 3 := by
      rw [hjunction, heraser]
      exact spaceUsed_bookkeeping_le none _ _ _ e 1
    -- split outer, then inner, and bound each phase
    have hinnerSpace :=
      spaceUsed_seq_le (tm₀ := core) (tm₁ := eraser) hmid₁ rfl (by rw [hmid₂]; rfl)
    have houterSpace := spaceUsed_seq_le (tm₀ := setter) (tm₁ := core.seq eraser) hmid₀ rfl
      (by rw [hhandoff, hinner]; rfl)
    rw [hhandoff] at houterSpace
    omega

end Turing.MultiTapeTM
