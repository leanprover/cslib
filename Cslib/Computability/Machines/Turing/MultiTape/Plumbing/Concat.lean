/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Fin.Embedding
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.NormalForms.RewindInput

/-!
# Concatenating the outputs of two machines

`concat tm₀ tm₁` runs `tm₀`, rewinds the native input head, and then runs `tm₁`. Since the output
tape is write-only and a machine only ever appends to it, the output of the composite is the output
of `tm₀` followed by the output of `tm₁`, and no intermediate result has to be stored anywhere.

The two machines are placed on disjoint blocks of work tapes: `tm₀` on the first `k₀` and `tm₁` on
the last `k₁`. So `tm₁` starts on blank tapes, exactly as it would when started on its own, and the
tapes `tm₀` leaves behind are never touched again. Giving `tm₁` fresh tapes is what makes it
unnecessary to know anything about the configuration `tm₀` halts in, and rewinding the input head
in between is what lets `tm₁` read the same input as `tm₀`.

## Main definitions

* `Turing.MultiTapeTM.concatTapeLeft`, `Turing.MultiTapeTM.concatTapeRight`: the two blocks of work
  tapes.
* `Turing.MultiTapeTM.concatPrefix`: the first phase, the first machine followed by the rewind.
* `Turing.MultiTapeTM.concat`: the composite machine.

## Main results

* `Turing.MultiTapeTM.computesInTimeAndSpace_concat`: the composite computes the concatenation of
  the two outputs. The extra time is one input rewind. The extra space is `k₀ + k₁`: whichever
  machine is not running has an idle head on each of its tapes, and each such head still counts for
  the one cell it sits on. The rewind itself costs no space at all, by
  `spaceUsed_rewindInput_le` — it moves no work-tape head, so it visits no new cell.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k₀ k₁ : ℕ} {Symbol State₀ State₁ : Type*}

/-- The block of work tapes the first machine of a concatenation runs on. -/
def concatTapeLeft (k₀ k₁ : ℕ) : Fin k₀ ↪ Fin (k₀ + k₁) := Fin.castAddEmb k₁

/-- The block of work tapes the second machine of a concatenation runs on. -/
def concatTapeRight (k₀ k₁ : ℕ) : Fin k₁ ↪ Fin (k₀ + k₁) := Fin.natAddEmb k₀

/-- The two blocks of work tapes are disjoint, so the second machine of a concatenation starts on
tapes that the first one never touched. -/
lemma concatTapeRight_notMem_range_left (j : Fin k₁) :
    concatTapeRight k₀ k₁ j ∉ Set.range (concatTapeLeft k₀ k₁) := by
  rintro ⟨i, hi⟩
  have hval := congrArg Fin.val hi
  simp only [concatTapeLeft, concatTapeRight, Fin.castAddEmb_apply, Fin.natAddEmb_apply,
    Fin.val_castAdd, Fin.val_natAdd] at hval
  have := i.isLt
  omega

/-- The first phase of a concatenation: the first machine, on its block of work tapes, followed by
the native-input rewind. -/
def concatPrefix (k₁ : ℕ) (tm₀ : MultiTapeTM k₀ Symbol State₀) :
    MultiTapeTM (k₀ + k₁) Symbol (State₀ ⊕ RewindState) :=
  (tm₀.extendTapes (concatTapeLeft k₀ k₁)).rewindInput

/-- Run `tm₀`, rewind the input head, then run `tm₁` on a disjoint block of work tapes. -/
def concat (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁) :
    MultiTapeTM (k₀ + k₁) Symbol ((State₀ ⊕ RewindState) ⊕ State₁) :=
  (concatPrefix k₁ tm₀).seq (tm₁.extendTapes (concatTapeRight k₀ k₁))

namespace Concat

variable (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁)
  {input : List Symbol}

/-- The composite is the sequential composition of its two phases. -/
lemma concat_eq_seq :
    concat tm₀ tm₁ = (concatPrefix k₁ tm₀).seq (tm₁.extendTapes (concatTapeRight k₀ k₁)) := rfl

/-- The configuration in which the first phase halts, in terms of the first machine's own run. -/
def prefixCfg (t₀ : ℕ) : Cfg (k₀ + k₁) Symbol (State₀ ⊕ RewindState) input :=
  Sequential.right (Rewind.inputCfg (ExtendTapes.embed (concatTapeLeft k₀ k₁)
    (tm₀.runFrom (tm₀.initCfg input) t₀) (fun _ _ => none) (fun _ => 0)) none 1)

/-- The first phase halts with the input head rewound, having produced exactly the output of the
first machine and used its space plus the one cell each idle tape's head sits on.

This is `rewindInput_halts_spaceUsed` read on the left block of tapes: the normal form carries its
own cost, so nothing about the rewind has to be unfolded here. -/
lemma exists_concatPrefix (k₁ : ℕ) {t₀ : ℕ}
    (hhalt : (tm₀.runFrom (tm₀.initCfg input) t₀).state = none) :
    ∃ u ≤ t₀ + input.length + 2,
      (concatPrefix k₁ tm₀).runFrom ((concatPrefix k₁ tm₀).initCfg input) u =
          prefixCfg tm₀ (k₁ := k₁) t₀ ∧
        (concatPrefix k₁ tm₀).spaceUsed ((concatPrefix k₁ tm₀).initCfg input) u ≤
          tm₀.spaceUsed (tm₀.initCfg input) t₀ + k₁ := by
  have hrun := runFrom_extendTapes tm₀ (concatTapeLeft k₀ k₁) input
  have hhalt' : ((tm₀.extendTapes (concatTapeLeft k₀ k₁)).runFrom
      ((tm₀.extendTapes (concatTapeLeft k₀ k₁)).initCfg input) t₀).state = none := by
    rw [hrun]; exact hhalt
  obtain ⟨u, hule, hucfg, huspace⟩ :=
    rewindInput_halts_spaceUsed (tm₀.extendTapes (concatTapeLeft k₀ k₁)) t₀ hhalt'
  refine ⟨u, hule, ?_, ?_⟩
  · unfold concatPrefix
    rw [hucfg, hrun t₀]
    rfl
  · refine huspace.trans ?_
    rw [spaceUsed_extendTapes tm₀ _ input t₀]
    omega

/-- Everything the second machine of a concatenation needs of the configuration handed to it: its
own block of tapes is blank and rewound and the input head is back at the start. The tapes of the
first machine may hold anything, and the output produced so far is kept.

All of the content is `ExtendTapes.eq_embed_initCfg`; what is left here is only that the second
machine's block of tapes is disjoint from the first machine's, so the first machine left it
blank. -/
lemma handoff_eq (t₀ : ℕ) (out : List Symbol)
    (hout : (tm₀.runFrom (tm₀.initCfg input) t₀).output = out) :
    (prefixCfg tm₀ (k₁ := k₁) t₀).withState
        (some (tm₁.extendTapes (concatTapeRight k₀ k₁)).q₀) =
      (ExtendTapes.embed (concatTapeRight k₀ k₁) (tm₁.initCfg input)
        (prefixCfg tm₀ (k₁ := k₁) (input := input) t₀).workTapes
        (prefixCfg tm₀ (k₁ := k₁) (input := input) t₀).workTapePos).prependOutput out := by
  have houtH : ((prefixCfg tm₀ (k₁ := k₁) t₀).withState
      (some (tm₁.extendTapes (concatTapeRight k₀ k₁)).q₀)).output = out := hout
  rw [← houtH]
  refine ExtendTapes.eq_embed_initCfg (concatTapeRight k₀ k₁) tm₁ _ rfl rfl ?_ ?_
  · intro j
    simp [prefixCfg, Sequential.right, Rewind.inputCfg, concatTapeRight_notMem_range_left j]
  · intro j
    simp [prefixCfg, Sequential.right, Rewind.inputCfg, concatTapeRight_notMem_range_left j]

end Concat

/-- **Correctness of output concatenation.** If `tm₀` computes `out₀` and `tm₁` computes `out₁`
from the same input, then `concat tm₀ tm₁` computes `out₀ ++ out₁`.

The extra time is the cost of one input rewind, which `rewindInput` accounts for. The extra space is
`k₀ + k₁`: whichever machine is not running has an idle head on each of its tapes, and each such
head still counts for the one cell it sits on. The rewind contributes nothing, since it moves no
work-tape head. -/
theorem computesInTimeAndSpace_concat
    (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁)
    {input out₀ out₁ : List Symbol} {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : ComputesInTimeAndSpace tm₀ input out₀ t₀ s₀)
    (h₁ : ComputesInTimeAndSpace tm₁ input out₁ t₁ s₁) :
    ∃ t ≤ t₀ + t₁ + input.length + 2, ∃ s ≤ s₀ + s₁ + (k₀ + k₁),
      ComputesInTimeAndSpace (concat tm₀ tm₁) input (out₀ ++ out₁) t s := by
  obtain ⟨hhalt₀, hout₀, hspace₀⟩ := h₀
  obtain ⟨hhalt₁, hout₁, hspace₁⟩ := h₁
  -- ### The first phase
  obtain ⟨v, hvle, hvcfg, hvspace⟩ := Concat.exists_concatPrefix tm₀ k₁ hhalt₀
  have hvhalt : ((concatPrefix k₁ tm₀).runFrom ((concatPrefix k₁ tm₀).initCfg input) v).state
      = none := by
    rw [hvcfg]; rfl
  obtain ⟨u, hule, huhalt, huactive⟩ :=
    exists_minimal_halting_time _ ((concatPrefix k₁ tm₀).initCfg input) v hvhalt
  have hucfg : (concatPrefix k₁ tm₀).runFrom ((concatPrefix k₁ tm₀).initCfg input) u =
      Concat.prefixCfg tm₀ (k₁ := k₁) t₀ := by
    rw [← hvcfg]
    exact (runFrom_eq_of_halt _ hule huhalt).symm
  -- ### The second phase, on its own blank block of tapes and with the output so far
  have hhandoff := Concat.handoff_eq tm₀ tm₁ t₀ out₀ hout₀
  rw [← hucfg] at hhandoff
  have hNhalt : ((tm₁.extendTapes (concatTapeRight k₀ k₁)).runFrom
      (((concatPrefix k₁ tm₀).runFrom ((concatPrefix k₁ tm₀).initCfg input) u).withState
        (some (tm₁.extendTapes (concatTapeRight k₀ k₁)).q₀)) t₁).state = none := by
    rw [hhandoff, runFrom_prependOutput, ExtendTapes.runFrom_embed]
    simpa [ExtendTapes.embed] using hhalt₁
  have hNout : ((tm₁.extendTapes (concatTapeRight k₀ k₁)).runFrom
      (((concatPrefix k₁ tm₀).runFrom ((concatPrefix k₁ tm₀).initCfg input) u).withState
        (some (tm₁.extendTapes (concatTapeRight k₀ k₁)).q₀)) t₁).output = out₀ ++ out₁ := by
    rw [hhandoff, runFrom_prependOutput, ExtendTapes.runFrom_embed]
    simpa [ExtendTapes.embed] using congrArg (out₀ ++ ·) hout₁
  -- ### The composite
  refine ⟨u + t₁, by omega, (concat tm₀ tm₁).spaceUsed ((concat tm₀ tm₁).initCfg input) (u + t₁),
    ?_, ?_, ?_, rfl⟩
  · -- space: the two phases, each paying one cell for every tape of the other machine
    have hsplit : (concat tm₀ tm₁).spaceUsed ((concat tm₀ tm₁).initCfg input) (u + t₁) ≤
        (concatPrefix k₁ tm₀).spaceUsed ((concatPrefix k₁ tm₀).initCfg input) u +
          (tm₁.extendTapes (concatTapeRight k₀ k₁)).spaceUsed
            (((concatPrefix k₁ tm₀).runFrom ((concatPrefix k₁ tm₀).initCfg input) u).withState
              (some (tm₁.extendTapes (concatTapeRight k₀ k₁)).q₀)) t₁ := by
      rw [Concat.concat_eq_seq, initCfg_seq]
      exact spaceUsed_seq_le _ _ _ u t₁ huhalt huactive
    have hsecond : (tm₁.extendTapes (concatTapeRight k₀ k₁)).spaceUsed
        (((concatPrefix k₁ tm₀).runFrom ((concatPrefix k₁ tm₀).initCfg input) u).withState
          (some (tm₁.extendTapes (concatTapeRight k₀ k₁)).q₀)) t₁ = s₁ + (k₀ + k₁ - k₁) := by
      rw [hhandoff, spaceUsed_prependOutput, ExtendTapes.spaceUsed_embed, hspace₁]
    have hfirst : (concatPrefix k₁ tm₀).spaceUsed ((concatPrefix k₁ tm₀).initCfg input) u ≤
        s₀ + k₁ := by
      refine (spaceUsed_mono _ _ hule).trans ?_
      rwa [hspace₀] at hvspace
    omega
  · -- halting
    rw [Concat.concat_eq_seq, initCfg_seq, runFrom_seq _ _ _ u t₁ huhalt huactive]
    simp only [Sequential.right, Cfg.withState_state, hNhalt]
    rfl
  · -- output
    rw [Concat.concat_eq_seq, initCfg_seq, runFrom_seq _ _ _ u t₁ huhalt huactive]
    simp only [Sequential.right, Cfg.withState_output]
    exact hNout

end Turing.MultiTapeTM
