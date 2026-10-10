/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Foundations.Data.Fin.Tuple
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.MarkWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg

/-!
# Reading the input from a word on a work tape

`inputFromWord M mark` runs `M` with its input read from a word on the work tape
`Fin.natAdd k' 0` (the *virtual input tape*) instead of from the real input tape, which it never
touches. It runs three machines in sequence:

1. `markFlag k' (some mark)` writes `mark` to cell `-1` of the work tape `Fin.natAdd k' 1` (the
   *flag tape*);
2. `Turing.MultiTapeTM.inputFromTape M` runs `M` on the virtual input tape, using the flag to
   recognise the left end of the input;
3. `markFlag k' none` erases the flag again.

So if `M` restores its input head, `inputFromWord M mark` takes `Turing.MultiTapeTM.wordsCfg`
configurations to `Turing.MultiTapeTM.wordsCfg` configurations; the virtual input word is never
written, and the output of `M` goes to the real output.

## Main results

* `Turing.MultiTapeTM.inputFromWord`: the composed machine.
* `Turing.MultiTapeTM.transformsTapes_inputFromWord_of_runFrom`: a run of `M` on the virtual input
  word, from and to `Turing.MultiTapeTM.wordsCfg` configurations, gives a specification of
  `inputFromWord M mark`.
-/

namespace Turing.MultiTapeTM

variable {k' : ℕ} {Symbol State : Type*}

/-- `markWork write` placed on the flag tape `Fin.natAdd k' 1` of a machine with `k' + 2` work
tapes: it writes `write` to the cell left of the head of that tape. -/
public noncomputable def markFlag (k' : ℕ) (write : Option Symbol) :
    MultiTapeTM (k' + 2) Symbol MarkWorkState :=
  (markWork Symbol write).extendTapes (tapeEmb (Fin.natAdd k' 1))

/-- `M`, reading its input from the virtual input tape `Fin.natAdd k' 0`, with the flag `mark`
written to cell `-1` of the flag tape `Fin.natAdd k' 1` before and erased after. -/
public noncomputable def inputFromWord (M : MultiTapeTM k' Symbol State) (mark : Symbol) :
    MultiTapeTM (k' + 2) Symbol (MarkWorkState ⊕ State ⊕ MarkWorkState) :=
  (markFlag k' (some mark)).seq (M.inputFromTape.seq (markFlag k' none))

/-- `Turing.MultiTapeTM.inCfg` of a `wordsCfg` configuration: the input `w` on the virtual input
tape, `mark` at cell `-1` of the flag tape, every head at cell `0`. -/
public lemma inCfg_wordsCfg (mark : Symbol) {w : List Symbol} (q : Option State)
    (ws : Fin k' → List Symbol) (o outer : List Symbol) :
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
private lemma update_append_flag {α : Type*} (ws₀ : Fin k' → α) (a b c : α) :
    Function.update (Fin.append ws₀ ![a, b]) (Fin.natAdd k' 1) c = Fin.append ws₀ ![a, c] := by
  rw [← Fin.append_update_right]
  congr 1
  simp [funext_iff, Fin.forall_fin_two]

private lemma markFlag_q₀ (write : Option Symbol) :
    (markFlag k' write).q₀ = (markWork Symbol write).q₀ := rfl

/-- The flag tape of a configuration whose tapes are `Fin.append WS ![vip, flag]`, as a one-tape
configuration of `markWork`. -/
private lemma oneTapeCfg_flag {input : List Symbol} (write : Option Symbol)
    (WS : Fin k' → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) :
    oneTapeCfg (Fin.natAdd k' 1)
        (⟨some (markWork Symbol write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩ :
          Cfg (k' + 2) Symbol MarkWorkState input) =
      ⟨some (markWork Symbol write).q₀, ip, fun _ => flag, fun _ => 0, out⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg, Fin.append_right]

/-- In two steps, `markFlag k' write` writes `write` to cell `-1` of the flag tape and changes
nothing else. -/
private lemma runFrom_markFlag {input : List Symbol} (write : Option Symbol)
    (WS : Fin k' → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) :
    (markFlag k' write).runFrom
        (⟨some (markFlag k' write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩ :
          Cfg (k' + 2) Symbol MarkWorkState input) 2 =
      ⟨none, ip, Fin.append WS ![vip, Function.update flag (-1) write], fun _ => 0, out⟩ := by
  rw [markFlag_q₀, markFlag, runFrom_tapeEmb, oneTapeCfg_flag, runFrom_markWork, embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · simpa using update_append_flag WS vip flag (Function.update flag (-1) write)
  · funext l; simp [Function.update_apply]

/-- `markFlag k' write` visits at most `k' + 3` cells: two on the flag tape and the starting cell
of each other tape. -/
private lemma spaceUsed_markFlag_le {input : List Symbol} (write : Option Symbol)
    (WS : Fin k' → ℤ → Option Symbol) (vip flag : ℤ → Option Symbol) (out : List Symbol)
    (ip : Fin (input.length + 2)) (n : ℕ) :
    (markFlag k' write).spaceUsed
        (⟨some (markFlag k' write).q₀, ip, Fin.append WS ![vip, flag], fun _ => 0, out⟩ :
          Cfg (k' + 2) Symbol MarkWorkState input) n ≤ k' + 3 := by
  rw [markFlag_q₀]
  refine (spaceUsed_tapeEmb_le (markWork Symbol write) (Fin.natAdd k' 1) _ n).trans ?_
  rw [oneTapeCfg_flag]
  have := spaceUsed_markWork_le write ip flag out 0 n
  omega

/-- A `wordsCfg` configuration whose last two words are `w` and the empty word, written out. -/
private lemma wordsCfg_append_words {State' : Type*} {outer : List Symbol} (q : Option State')
    (ws : Fin k' → List Symbol) (w out : List Symbol) :
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
    {M : MultiTapeTM k' Symbol State} {w e : List Symbol} {ws₀ ws₁ : Fin k' → List Symbol}
    {t s : ℕ} (hrun : M.runFrom (wordsCfg w (some M.q₀) ws₀ []) t = wordsCfg w none ws₁ e)
    (hspace : M.spaceUsed (wordsCfg w (some M.q₀) ws₀ []) t ≤ s) :
    TransformsTapes (M.inputFromWord mark)
      (fun _ ws => ws = Fin.append ws₀ ![w, []])
      (fun _ _ ws' em => ws' = Fin.append ws₁ ![w, []] ∧ em = e)
      (t + 4) (s + 2 * (w.length + 2) + 2 * k' + 6) := by
  rw [transformsTapes_iff_nil_output]
  rintro outer ws rfl
  -- the three phases of the composed machine
  set setter := markFlag k' (some mark) (Symbol := Symbol)
  set eraser := markFlag k' none (Symbol := Symbol)
  set core := M.inputFromTape
  -- the configurations in which the core starts and halts
  set cfgCore := inCfg mark (wordsCfg w (some M.q₀) ws₀ []) outer with hcfgCore
  set midCore := inCfg mark (wordsCfg w none ws₁ e) outer with hmidCore
  -- the setter writes the flag
  set midSet : Cfg (k' + 2) Symbol MarkWorkState outer :=
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
        (wordsCfg outer (some setter.q₀) (Fin.append ws₀ ![w, []]) []) 2 ≤ k' + 3 := by
      rw [wordsCfg_append_words]
      exact spaceUsed_markFlag_le (some mark) _ _ _ [] 1 2
    have hcoreSpace : core.spaceUsed cfgCore t ≤ s + 2 * (w.length + 2) :=
      (spaceUsed_inputFromTape M mark (wordsCfg w (some M.q₀) ws₀ []) outer t).trans
        (Nat.add_le_add_right hspace _)
    have herSpace : eraser.spaceUsed (midCore.withState (some eraser.q₀)) 2 ≤ k' + 3 := by
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
