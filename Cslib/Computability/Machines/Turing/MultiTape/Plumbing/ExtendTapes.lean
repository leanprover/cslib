/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Aviv Bar Natan
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

* `Turing.MultiTapeNTM.partialInv`: the partial inverse of the tape embedding.
* `Turing.MultiTapeNTM.extendTapes`: the machine with reindexed work tapes.
* `Turing.MultiTapeNTM.embed`: the corresponding configuration map.
* `Turing.MultiTapeNTM.restrictCfg`: the view of a configuration on the selected tapes.
* `Turing.MultiTapeNTM.RunPath.extendTapes`: a path embedded on the selected tapes.
* `Turing.MultiTapeNTM.RunPath.restrictTapes`: a path projected onto the selected tapes.
* `Turing.MultiTapeNTM.tapeEmb`: the embedding placing the only tape of a one-tape machine on
  tape `i`, and `Turing.MultiTapeNTM.noTapes`: the embedding of a machine without work tapes.
* `Turing.MultiTapeNTM.RunPath.oneTape`: the one-tape view of a path of the extended machine.

## Main results

* `Turing.MultiTapeNTM.step_embed`: the one-step mirroring lemma.
* `Turing.MultiTapeNTM.step_extendTapes_iff`: a step of the larger machine projects to a step of
  the original machine and leaves the extra tapes unchanged.
* `Turing.MultiTapeNTM.RunPath.space_restrictTapes_le`: the space bound for any extended path.
* `Turing.MultiTapeNTM.RunPath.space_extendTapes_le`: the resulting space bound.
* `Turing.MultiTapeNTM.oneTapeCfg`: the one-tape view of a configuration.
* `Turing.MultiTapeNTM.step_tapeEmb`, `Turing.MultiTapeNTM.RunPath.space_tapeEmb_le`: the steps and
  space of a one-tape machine placed on work tape `i`.
* `Turing.MultiTapeNTM.TransformsTapes.tapeEmb`: a one-tape specification, read on tape `i`.
* `Turing.MultiTapeNTM.step_noTapes`, `Turing.MultiTapeNTM.RunPath.space_noTapes_le`: the steps and
  space of a machine without work tapes, placed in a machine with `k` of them.
-/

namespace Turing.MultiTapeNTM

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
@[expose] public def extendTapes (tm : MultiTapeNTM k Symbol State)
    (e : Fin k ↪ Fin k') : MultiTapeNTM k' Symbol State where
  q₀ := tm.q₀
  Tr q inp work b := ∃ a, tm.Tr q inp (fun j ↦ work (e j)) a ∧ b =
    { inputTape := a.inputTape
      workTapes := fun l ↦ match partialInv e l with
        | some j => a.workTapes j
        | none => (none, 0)
      output := a.output
      state := a.state }

@[simp]
public lemma extendTapes_q₀ (tm : MultiTapeNTM k Symbol State) (e : Fin k ↪ Fin k') :
    (tm.extendTapes e).q₀ = tm.q₀ := rfl

/-- Extending the tapes preserves determinism. -/
public lemma IsDeterministic.extendTapes {tm : MultiTapeNTM k Symbol State}
    (h : tm.IsDeterministic) (e : Fin k ↪ Fin k') : (tm.extendTapes e).IsDeterministic := by
  intro q inp work
  obtain ⟨a, ha, hu⟩ := h q inp (fun j ↦ work (e j))
  refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
  rintro b ⟨a', ha', rfl⟩
  rw [hu a' ha']

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

/-- The view of a configuration on the tapes selected by `e`, with all other fields unchanged. -/
@[expose] public def restrictCfg (e : Fin k ↪ Fin k') (cfg : Cfg k' Symbol State input) :
    Cfg k Symbol State input :=
  ⟨cfg.state, cfg.inputPos, fun j ↦ cfg.workTapes (e j), fun j ↦ cfg.workTapePos (e j), cfg.output⟩

/-- Projecting an embedded configuration recovers the original configuration. -/
@[simp]
public lemma restrictCfg_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    restrictCfg e (embed e cfg extraTapes extraPos) = cfg := by
  simp [restrictCfg, embed]

/-- Placing the selected tapes back into their original configuration recovers that
configuration. -/
@[simp]
public lemma embed_restrictCfg (e : Fin k ↪ Fin k') (cfg : Cfg k' Symbol State input) :
    embed e (restrictCfg e cfg) cfg.workTapes cfg.workTapePos = cfg := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> cases hl : partialInv e l with
  | none => simp [embed, hl]
  | some j => simp [embed, restrictCfg, hl, partialInv_eq_some e hl]

/-- A step of the extended machine is exactly a step on the selected tapes, with the remaining
tapes and heads unchanged. -/
public lemma step_extendTapes_iff (tm : MultiTapeNTM k Symbol State) (e : Fin k ↪ Fin k')
    {c c' : Cfg k' Symbol State input} :
    (tm.extendTapes e).Step c c' ↔
      tm.Step (restrictCfg e c) (restrictCfg e c') ∧
      c' = embed e (restrictCfg e c') c.workTapes c.workTapePos := by
  constructor
  · intro h
    cases hq : c.state with
    | none =>
      obtain rfl := (step_of_halt hq).mp h
      exact ⟨(step_of_halt (c := restrictCfg e c') hq).mpr rfl, (embed_restrictCfg e c').symm⟩
    | some q =>
      obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := (step_of_state hq).mp h
      constructor
      · refine (step_of_state (c := restrictCfg e c) hq).mpr ⟨a, ha, ?_⟩
        refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext j <;> simp [restrictCfg, Action.apply]
      · refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> cases hl : partialInv e l with
        | none => simp [embed, restrictCfg, Action.apply, hl]
        | some j => simp [embed, restrictCfg, Action.apply, hl, partialInv_eq_some e hl]
  · rintro ⟨h, he⟩
    cases hq : c.state with
    | none =>
      have hc := (step_of_halt (c := restrictCfg e c) hq).mp h
      exact (step_of_halt hq).mpr (by rw [he, hc, embed_restrictCfg])
    | some q =>
      obtain ⟨a, ha, hc⟩ := (step_of_state (c := restrictCfg e c) hq).mp h
      refine (step_of_state hq).mpr ⟨_, ⟨a, ha, rfl⟩, ?_⟩
      rw [he, hc]
      refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> cases hl : partialInv e l with
      | none => simp [embed, restrictCfg, Action.apply, hl]
      | some j => simp [embed, restrictCfg, Action.apply, hl, partialInv_eq_some e hl]

/-- Reindexing preserves steps: the reindexed machine acts on the embedded tapes exactly
as `tm` does, and never touches the extra tapes. `RunPath.extendTapes` transports an entire path. -/
public lemma step_embed (tm : MultiTapeNTM k Symbol State) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ)
    {c c' : Cfg k Symbol State input} (h : tm.Step c c') :
    (tm.extendTapes e).Step (embed e c extraTapes extraPos) (embed e c' extraTapes extraPos) := by
  rw [step_extendTapes_iff, restrictCfg_embed, restrictCfg_embed]
  refine ⟨h, ?_⟩
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;>
    cases hl : partialInv e l <;> simp [embed, hl]

/-- Embed a path on the tapes selected by `e`, keeping the extra tapes and heads fixed. -/
@[expose] public def RunPath.extendTapes {tm : MultiTapeNTM k Symbol State}
    (p : tm.RunPath input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    (tm.extendTapes e).RunPath input :=
  p.map ⟨(embed e · extraTapes extraPos), step_embed tm e extraTapes extraPos⟩

/-- Project a path of the extended machine onto the tapes selected by `e`. -/
@[expose] public def RunPath.restrictTapes {tm : MultiTapeNTM k Symbol State}
    {e : Fin k ↪ Fin k'} (p : (tm.extendTapes e).RunPath input) : tm.RunPath input :=
  p.map ⟨restrictCfg e, fun h ↦ ((step_extendTapes_iff tm e).mp h).1⟩

/-- Projecting an embedded path recovers the original path. -/
@[simp]
public lemma RunPath.restrictTapes_extendTapes {tm : MultiTapeNTM k Symbol State}
    (p : tm.RunPath input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    (p.extendTapes e extraTapes extraPos).restrictTapes = p := by
  refine RelSeries.ext (x := _) (y := p) rfl ?_
  funext n
  exact restrictCfg_embed e (p n) extraTapes extraPos

/-- The selected tapes contribute the space used by the projected path, and each remaining tape
contributes at most one cell. -/
public lemma RunPath.space_restrictTapes_le {tm : MultiTapeNTM k Symbol State}
    {e : Fin k ↪ Fin k'} (p : (tm.extendTapes e).RunPath input) :
    p.space ≤ p.restrictTapes.space + (k' - k) := by
  simpa using RunPath.space_le_of_workTapePos_embedding p.restrictTapes p rfl
    e 1 (fun _ _ ↦ rfl) fun j hj ↦ by
      apply RunPath.spaceUsedByTape_le_one
      rintro _ ⟨n, rfl⟩
      induction n using Fin.induction with
      | zero => rfl
      | succ n ih =>
        have he := ((step_extendTapes_iff tm e).mp (p.step n)).2
        have hpos := congrArg (fun c ↦ c.workTapePos j) he
        simpa [embed, partialInv_eq_none e hj, ih] using hpos

/-- **Space bound for a reindexed path.** The embedded tapes contribute the space used by `tm`,
while each of the remaining `k' - k` tapes never moves and contributes at most one cell. -/
public lemma RunPath.space_extendTapes_le {tm : MultiTapeNTM k Symbol State}
    (p : tm.RunPath input) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    (p.extendTapes e extraTapes extraPos).space ≤ p.space + (k' - k) := by
  simpa using (p.extendTapes e extraTapes extraPos).space_restrictTapes_le

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
  restrictCfg (tapeEmb i) cfg

/-- A configuration is its own one-tape view on tape `i`, placed back on tape `i`. -/
public lemma embed_oneTapeCfg (i : Fin k) (cfg : Cfg k Symbol State input) :
    embed (tapeEmb i) (oneTapeCfg i cfg) cfg.workTapes cfg.workTapePos = cfg :=
  embed_restrictCfg (tapeEmb i) cfg

/-- **Running a one-tape machine on work tape `i`.** A step is exactly a step on the one-tape view,
placed back on tape `i`; every other tape and head keeps its starting value. Combine
with `embed_tapeEmb` to read off the resulting configuration. -/
public lemma step_tapeEmb (tm : MultiTapeNTM 1 Symbol State) (i : Fin k)
    {c c' : Cfg k Symbol State input} :
    (tm.extendTapes (tapeEmb i)).Step c c' ↔
      tm.Step (oneTapeCfg i c) (oneTapeCfg i c') ∧
      c' = embed (tapeEmb i) (oneTapeCfg i c') c.workTapes c.workTapePos :=
  step_extendTapes_iff tm (tapeEmb i)

/-- The one-tape view of a path of a one-tape machine placed on work tape `i`. -/
@[expose] public def RunPath.oneTape {tm : MultiTapeNTM 1 Symbol State} {i : Fin k}
    (p : (tm.extendTapes (tapeEmb i)).RunPath input) : tm.RunPath input :=
  p.restrictTapes

/-- **Space bound for a one-tape machine placed on tape `i`:** the space of the one-tape path, plus
one cell for each tape the machine does not use. -/
public lemma RunPath.space_tapeEmb_le {tm : MultiTapeNTM 1 Symbol State} {i : Fin k}
    (p : (tm.extendTapes (tapeEmb i)).RunPath input) :
    p.space ≤ p.oneTape.space + (k - 1) :=
  p.space_restrictTapes_le

/-- **A one-tape specification on tape `i`.** A one-tape machine placed on tape `i` transforms the
word on that tape as it did on its own tape and leaves every other word alone; each remaining tape
costs one cell. -/
public theorem TransformsTapes.tapeEmb {tm : MultiTapeNTM 1 Symbol State}
    {P : (input : List Symbol) → (Fin 1 → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin 1 → List Symbol) → (Fin 1 → List Symbol) →
      List Symbol → Prop} {t s : ℕ}
    (h : TransformsTapes tm P Q t s) (i : Fin k) :
    TransformsTapes (tm.extendTapes (MultiTapeNTM.tapeEmb i))
      (fun input ws ↦ P input fun _ ↦ ws i)
      (fun input ws ws' emitted ↦
        ∃ v, Q input (fun _ ↦ ws i) v emitted ∧ ws' = Function.update ws i (v 0))
      t (s + (k - 1)) := by
  intro input ws out hP
  obtain ⟨v, emitted, p, hp, hlast, hQ, ht, hs⟩ := h input (fun _ ↦ ws i) out hP
  let tapes := fun j ↦ tapeOfList (ws j)
  let heads := fun _ : Fin k ↦ (0 : ℤ)
  let q := p.extendTapes (MultiTapeNTM.tapeEmb i) tapes heads
  refine ⟨Function.update ws i (v 0), emitted, q, ?_, ?_, ⟨v, hQ, rfl⟩, ht,
    (p.space_extendTapes_le (MultiTapeNTM.tapeEmb i) tapes heads).trans
      (Nat.add_le_add_right hs _)⟩
  · change embed _ p.head _ _ = _
    rw [hp, embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> simp [tapes, heads, wordsCfg]
  · change embed _ p.last _ _ = _
    rw [hlast, embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> by_cases hl : l = i <;>
      simp [tapes, heads, wordsCfg, hl]

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
public lemma step_noTapes (tm : MultiTapeNTM 0 Symbol State) (cfg : Cfg k Symbol State input)
    {c' : Cfg 0 Symbol State input} (h : tm.Step (noTapesCfg cfg) c') :
    (tm.extendTapes (noTapes k)).Step cfg
      ⟨c'.state, c'.inputPos, cfg.workTapes, cfg.workTapePos, c'.output⟩ := by
  simpa only [embed_noTapes, noTapesCfg] using
    step_embed tm (noTapes k) cfg.workTapes cfg.workTapePos h

/-- **Space bound for a machine without work tapes:** one cell for each tape it does not use. -/
public lemma RunPath.space_noTapes_le {tm : MultiTapeNTM 0 Symbol State} (p : tm.RunPath input)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ) :
    (p.extendTapes (noTapes k) tapes heads).space ≤ k := by
  simpa using p.space_extendTapes_le (noTapes k) tapes heads

end NoTapes

end Turing.MultiTapeNTM
