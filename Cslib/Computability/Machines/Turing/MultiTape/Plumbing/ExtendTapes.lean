/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Inv
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Extending a machine with additional work tapes

`extendTapes tm e`, for an embedding `e : Fin k ↪ Fin k'`, runs `tm` inside a machine with more
work tapes. The tapes selected by `e` are used by `tm`: target tape `e j` plays the role of source
tape `j`. The remaining tapes are left unchanged.

The configuration map `embed e cfg extraTapes extraPos` places `cfg` on the selected tapes and
initialises the remaining tapes from `extraTapes` and `extraPos`.

The main lemmas show that one step and an entire run of the larger machine mirror the corresponding
step and run of `tm`.

## Main definitions

* `Turing.MultiTapeTM.partialInv`: the partial inverse of the tape embedding.
* `Turing.MultiTapeTM.extendTapes`: the machine with reindexed work tapes.
* `Turing.MultiTapeTM.embed`: the corresponding configuration map.

## Main results

* `Turing.MultiTapeTM.step_embed` and `Turing.MultiTapeTM.runFrom_embed`: the one-step and run-level
  mirroring lemmas.
* `Turing.MultiTapeTM.workTapePos_embed_of_not_range`: the extra tapes never move.
* `Turing.MultiTapeTM.spaceUsed_embed_le`: the resulting space bound.
-/

namespace Turing.MultiTapeTM

variable {k k' : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The computable analogue of `Function.partialInv` for an embedding `e`: `partialInv e l = some j`
when `e j = l` (such `j` is unique by injectivity), and `none` when `l` lies outside the range of
`e`. -/
@[expose] public def partialInv (e : Fin k ↪ Fin k') (l : Fin k') : Option (Fin k) :=
  if h : l ∈ Set.range e then some (e.invOfMemRange ⟨l, h⟩) else none

/-- `partialInv e` is a partial inverse of `e`. -/
public lemma partialInv_isPartialInv (e : Fin k ↪ Fin k') :
    Function.IsPartialInv e (partialInv e) := fun j l => by
  grind [partialInv, Function.Embedding.left_inv_of_invOfMemRange,
    Function.Embedding.right_inv_of_invOfMemRange]

/-- `tm` run on the tapes selected by the embedding `e`, leaving other tapes untouched: work tape
`e j` plays the role of `tm`'s tape `j`, and any tape outside `range e` is never written and never
moves. -/
@[expose] public def extendTapes (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k') :
    MultiTapeTM k' Symbol State where
  q₀ := tm.q₀
  tr q inp work :=
    let a := tm.tr q inp fun j => work (e j)
    { inputTape := a.inputTape
      workTapes := fun l => match partialInv e l with
        | some j => a.workTapes j
        | none => (none, 0)
      output := a.output
      state := a.state }

/-- A configuration of `tm`, embedded: tape `j` goes to tape `e j`, the tapes outside `range e`
carry the given `extraTapes` contents and `extraPos` head positions. -/
@[expose] public def embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    Cfg k' Symbol State input :=
  ⟨cfg.state, cfg.inputPos,
    fun l => match partialInv e l with
      | some j => cfg.workTapes j
      | none => extraTapes l,
    fun l => match partialInv e l with
      | some j => cfg.workTapePos j
      | none => extraPos l,
    cfg.output⟩

/-- The partial inverse recovers the source tape of an embedded tape. -/
@[simp]
public lemma partialInv_embed (e : Fin k ↪ Fin k') (j : Fin k) : partialInv e (e j) = some j :=
  (partialInv_isPartialInv e).eq j

/-- Outside the range of `e`, the partial inverse is undefined. -/
public lemma partialInv_eq_none (e : Fin k ↪ Fin k') {l : Fin k'} (hl : l ∉ Set.range e) :
    partialInv e l = none :=
  dite_eq_right hl

/-- If the partial inverse is `some j`, then `e j = l`. -/
public lemma partialInv_eq_some (e : Fin k ↪ Fin k') {l : Fin k'} {j : Fin k}
    (h : partialInv e l = some j) : e j = l :=
  (partialInv_isPartialInv e j l).mp h

@[simp]
public lemma embed_inputSymbol (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    (embed e cfg extraTapes extraPos).inputSymbol = cfg.inputSymbol := rfl

@[simp]
public lemma embed_workTapes_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapes (e j) = cfg.workTapes j := by
  simp [embed]

@[simp]
public lemma embed_workTapePos_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapePos (e j) = cfg.workTapePos j := by
  simp [embed]

@[simp]
public lemma embed_workTapeSymbols_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapeSymbols (e j) = cfg.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- Reindexing is a step-semiconjugation: the reindexed machine acts on the embedded tapes exactly
as `tm` does, and never touches the extra tapes. -/
public lemma step_embed (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) :
    (tm.extendTapes e).step (embed e cfg extraTapes extraPos)
      = embed e (tm.step cfg) extraTapes extraPos := by
  cases hq : cfg.state with
  | none => simp [embed, hq]
  | some q =>
    rw [step_apply_of_state (cfg := embed e cfg extraTapes extraPos) hq, step_apply_of_state hq]
    simp only [extendTapes, embed_inputSymbol, embed_workTapeSymbols_embed]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> simp only [Action.apply, embed] <;>
      cases partialInv e l <;> simp

/-- The reindexed run mirrors the original, with the extra tapes held fixed throughout. -/
public lemma runFrom_embed (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) :
    (tm.extendTapes e).runFrom (embed e cfg extraTapes extraPos) n
      = embed e (tm.runFrom cfg n) extraTapes extraPos :=
  (Function.Semiconj.iterate_right (f := (embed e · extraTapes extraPos))
    (fun c => (step_embed tm e c extraTapes extraPos).symm) n cfg).symm

section Space

/-- The head of a tape outside `range e` never leaves its starting position. -/
public lemma workTapePos_embed_of_not_range (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) {l : Fin k'} (hl : l ∉ Set.range e) :
    ((tm.extendTapes e).runFrom (embed e cfg extraTapes extraPos) n).workTapePos l
      = extraPos l := by
  rw [runFrom_embed]
  simp only [embed, partialInv_eq_none e hl]

/-- **Space bound for a reindexed run.** The embedded tapes contribute the space used by `tm`, while
each of the remaining `k' - k` tapes never moves and contributes at most one cell. -/
public lemma spaceUsed_embed_le (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) :
    (tm.extendTapes e).spaceUsed (embed e cfg extraTapes extraPos) n
      ≤ tm.spaceUsed cfg n + (k' - k) := by
  simpa using tm.spaceUsed_le_of_workTapePos_embedding e cfg _ 1
    (fun m _ j => by rw [runFrom_embed, embed_workTapePos_embed])
    fun l hl => spaceUsedByTape_le_one _ fun m _ => by
      rw [workTapePos_embed_of_not_range tm e cfg extraTapes extraPos m hl]
      simp only [embed, partialInv_eq_none e hl]

end Space

end Turing.MultiTapeTM
