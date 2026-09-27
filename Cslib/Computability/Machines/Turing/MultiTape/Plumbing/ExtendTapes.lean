/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Fintype.Inv
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

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
* `Turing.MultiTapeTM.tapeEmb`: the embedding placing the only tape of a one-tape machine on
  tape `i`, and `Turing.MultiTapeTM.noTapes`: the embedding of a machine without work tapes.

## Main results

* `Turing.MultiTapeTM.step_embed` and `Turing.MultiTapeTM.runFrom_embed`: the one-step and run-level
  mirroring lemmas.
* `Turing.MultiTapeTM.workTapePos_embed_of_not_range`: the extra tapes never move.
* `Turing.MultiTapeTM.spaceUsed_embed_le`: the resulting space bound.
* `Turing.MultiTapeTM.oneTapeCfg`: the one-tape view of a configuration.
* `Turing.MultiTapeTM.runFrom_tapeEmb`, `Turing.MultiTapeTM.spaceUsed_tapeEmb_le`: the run and the
  space of a one-tape machine placed on work tape `i`.
* `Turing.MultiTapeTM.TransformsTapes.tapeEmb`: a one-tape specification, read on tape `i`.
* `Turing.MultiTapeTM.runFrom_noTapes`, `Turing.MultiTapeTM.spaceUsed_noTapes_le`: the run and the
  space of a machine without work tapes, placed in a machine with `k` of them.
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
@[expose] public noncomputable def extendTapes (tm : MultiTapeTM k Symbol State)
    (e : Fin k ↪ Fin k') : MultiTapeTM k' Symbol State :=
  ofTr tm.q₀ fun q inp work =>
    let a := tm.tr q inp fun j => work (e j)
    { inputTape := a.inputTape
      workTapes := fun l => match partialInv e l with
        | some j => a.workTapes j
        | none => (none, 0)
      output := a.output
      state := a.state }

@[simp]
public lemma extendTapes_q₀ (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k') :
    (tm.extendTapes e).q₀ = tm.q₀ := rfl

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
    rw [step_of_state (cfg := embed e cfg extraTapes extraPos) hq, step_of_state hq]
    simp only [extendTapes, tr_ofTr, embed_inputSymbol, embed_workTapeSymbols_embed]
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

/-! ### Placing a one-tape machine on a single work tape -/

section OneTape

variable {k : ℕ}

/-- The embedding that places the only work tape of a one-tape machine on tape `i`. -/
@[expose] public def tapeEmb (i : Fin k) : Fin 1 ↪ Fin k :=
  ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩

@[simp]
public lemma tapeEmb_apply (i : Fin k) (j : Fin 1) : tapeEmb i j = i := rfl

@[simp]
public lemma range_tapeEmb (i : Fin k) : Set.range (tapeEmb i) = {i} := by
  ext l
  simp [eq_comm]

/-- Tape `i` is the image of the only tape of a one-tape machine, and no other tape is. -/
@[simp]
public lemma partialInv_tapeEmb (i l : Fin k) :
    partialInv (tapeEmb i) l = if l = i then some 0 else none := by
  split_ifs with h
  · exact h ▸ partialInv_embed (tapeEmb i) 0
  · exact partialInv_eq_none _ (by simp [h])

/-- A one-tape configuration placed on tape `i` leaves every other tape as it was. -/
public lemma embed_tapeEmb (i : Fin k) (cfg : Cfg 1 Symbol State input)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ) :
    embed (tapeEmb i) cfg tapes heads =
      ⟨cfg.state, cfg.inputPos, Function.update tapes i (cfg.workTapes 0),
        Function.update heads i (cfg.workTapePos 0), cfg.output⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> by_cases hl : l = i <;> simp [embed, hl]

/-- The one-tape view of a configuration of a machine with `k` work tapes: the tape and head of
tape `i`, with everything else as it is. -/
@[expose] public def oneTapeCfg (i : Fin k) (cfg : Cfg k Symbol State input) :
    Cfg 1 Symbol State input :=
  ⟨cfg.state, cfg.inputPos, fun _ => cfg.workTapes i, fun _ => cfg.workTapePos i, cfg.output⟩

/-- A configuration is its own one-tape view on tape `i`, placed back on tape `i`. -/
public lemma embed_oneTapeCfg (i : Fin k) (cfg : Cfg k Symbol State input) :
    embed (tapeEmb i) (oneTapeCfg i cfg) cfg.workTapes cfg.workTapePos = cfg := by
  rw [embed_tapeEmb]
  simp [oneTapeCfg]

/-- **Running a one-tape machine on work tape `i`.** The run is the run on the one-tape view of the
configuration, placed back on tape `i`; every other tape and head keeps its starting value. Combine
with `embed_tapeEmb` to read off the resulting configuration. -/
public lemma runFrom_tapeEmb (tm : MultiTapeTM 1 Symbol State) (i : Fin k)
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    (tm.extendTapes (tapeEmb i)).runFrom cfg n =
      embed (tapeEmb i) (tm.runFrom (oneTapeCfg i cfg) n) cfg.workTapes cfg.workTapePos := by
  rw [← runFrom_embed, embed_oneTapeCfg]

/-- **Space bound for a one-tape machine placed on tape `i`:** the space of the one-tape run, plus
one cell for each tape the machine does not use. -/
public lemma spaceUsed_tapeEmb_le (tm : MultiTapeTM 1 Symbol State) (i : Fin k)
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    (tm.extendTapes (tapeEmb i)).spaceUsed cfg n ≤ tm.spaceUsed (oneTapeCfg i cfg) n + (k - 1) := by
  conv_lhs => rw [← embed_oneTapeCfg i cfg]
  exact spaceUsed_embed_le _ _ _ _ _ _

/-- **A one-tape specification on tape `i`.** A one-tape machine placed on tape `i` transforms the
word on that tape as it did on its own tape and leaves every other word alone; each remaining tape
costs one cell. -/
public theorem TransformsTapes.tapeEmb {tm : MultiTapeTM 1 Symbol State}
    {P : (input : List Symbol) → (Fin 1 → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin 1 → List Symbol) → (Fin 1 → List Symbol) → Prop} {t s : ℕ}
    (h : TransformsTapes tm P Q t s) (i : Fin k) :
    TransformsTapes (tm.extendTapes (MultiTapeTM.tapeEmb i))
      (fun input ws => P input fun _ => ws i)
      (fun input ws ws' => ∃ v, Q input (fun _ => ws i) v ∧ ws' = Function.update ws i (v 0))
      t (s + (k - 1)) := by
  intro input ws out hP
  obtain ⟨v, hrun, hQ, hspace⟩ := h input (fun _ => ws i) out hP
  simp only [wordsCfg] at hrun hspace
  refine ⟨Function.update ws i (v 0), ?_, ⟨v, hQ, rfl⟩, ?_⟩
  · rw [extendTapes_q₀, runFrom_tapeEmb]
    simp only [oneTapeCfg, wordsCfg, hrun]
    rw [embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> by_cases hl : l = i <;> simp [hl]
  · rw [extendTapes_q₀]
    exact (spaceUsed_tapeEmb_le _ _ _ _).trans (Nat.add_le_add_right hspace _)

end OneTape

section NoTapes

variable {k : ℕ}

/-- The embedding of a machine without work tapes into a machine with `k` of them. -/
@[expose] public def noTapes (k : ℕ) : Fin 0 ↪ Fin k := ⟨Fin.elim0, fun a => a.elim0⟩

/-- No tape is in the range of `noTapes`. -/
@[simp]
public lemma partialInv_noTapes (l : Fin k) : partialInv (noTapes k) l = none :=
  partialInv_eq_none _ (by simp)

/-- The view of a configuration as a configuration of a machine without work tapes. -/
@[expose] public def noTapesCfg (cfg : Cfg k Symbol State input) : Cfg 0 Symbol State input :=
  ⟨cfg.state, cfg.inputPos, nofun, nofun, cfg.output⟩

/-- A configuration without work tapes, placed in a machine with `k` of them, only contributes its
state, its input head and its output. -/
public lemma embed_noTapes (cfg : Cfg 0 Symbol State input)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ) :
    embed (noTapes k) cfg tapes heads = ⟨cfg.state, cfg.inputPos, tapes, heads, cfg.output⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> simp [embed]

/-- A configuration is its tapeless view, placed back on its tapes. -/
public lemma embed_noTapesCfg (cfg : Cfg k Symbol State input) :
    embed (noTapes k) (noTapesCfg cfg) cfg.workTapes cfg.workTapePos = cfg := by
  rw [embed_noTapes]
  rfl

/-- **Running a machine without work tapes inside a machine with `k` of them.** Only the state, the
input head and the output change; every work tape and work head keeps its starting value. -/
public lemma runFrom_noTapes (tm : MultiTapeTM 0 Symbol State) (cfg : Cfg k Symbol State input)
    (n : ℕ) :
    (tm.extendTapes (noTapes k)).runFrom cfg n =
      ⟨(tm.runFrom (noTapesCfg cfg) n).state, (tm.runFrom (noTapesCfg cfg) n).inputPos,
        cfg.workTapes, cfg.workTapePos, (tm.runFrom (noTapesCfg cfg) n).output⟩ := by
  rw [← embed_noTapesCfg cfg, runFrom_embed, embed_noTapes]
  simp [embed_noTapesCfg]

/-- **Space bound for a machine without work tapes:** one cell for each tape it does not use. -/
public lemma spaceUsed_noTapes_le (tm : MultiTapeTM 0 Symbol State)
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    (tm.extendTapes (noTapes k)).spaceUsed cfg n ≤ k := by
  conv_lhs => rw [← embed_noTapesCfg cfg]
  simpa using spaceUsed_embed_le tm (noTapes k) (noTapesCfg cfg) cfg.workTapes cfg.workTapePos n

end NoTapes

end Turing.MultiTapeTM
