/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Basic
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Data.Fintype.Card

/-!
# Extending and reindexing work tapes

`extendTapes` embeds a machine's work tapes along an injection. The extra tapes are idle, and each
native step still takes exactly one step. The configuration embedding permits arbitrary contents
and head positions on the extra tapes, so the transformation also applies to intermediate runs.

`eq_embed_initCfg` is the converse reading, and is what hands a fresh block of tapes to a machine:
a configuration in that machine's initial state, with the input head at the start and its own block
of tapes blank and rewound, *is* its embedded initial configuration, whatever the other tapes hold
and whatever output has been produced. A machine placed on such a block therefore runs exactly as
it would on its own.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k k' : ℕ} {Symbol State : Type*} {input : List Symbol}

namespace ExtendTapes

/-- Extend a tape-indexed family along an injection, using `extra` outside its image. -/
def extend {α : Type*} (e : Fin k ↪ Fin k') (values : Fin k → α) (extra : Fin k' → α)
    (j : Fin k') : α :=
  if h : j ∈ Set.range e then values (e.invOfMemRange ⟨j, h⟩) else extra j

@[simp]
lemma extend_apply {α : Type*} (e : Fin k ↪ Fin k') (values : Fin k → α)
    (extra : Fin k' → α) (i : Fin k) : extend e values extra (e i) = values i := by
  simp [extend]

/-- A family that already agrees with the values on the image is unchanged by extension. -/
lemma extend_eq_self {α : Type*} (e : Fin k ↪ Fin k') (values : Fin k → α)
    (extra : Fin k' → α) (h : ∀ i, extra (e i) = values i) : extend e values extra = extra := by
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    rw [extend_apply, h i]
  · simp [extend, hj]

/-- Embed a native configuration while retaining arbitrary data on the unused tapes. -/
def embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    Cfg k' Symbol State input where
  state := cfg.state
  inputPos := cfg.inputPos
  workTapes := extend e cfg.workTapes extraTapes
  workTapePos := extend e cfg.workTapePos extraPos
  output := cfg.output

/-- A tape outside the image of `e` holds whatever was supplied for it. -/
@[simp]
lemma workTapes_embed_of_notMem_range (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) {j : Fin k'}
    (hj : j ∉ Set.range e) :
    (embed e cfg extraTapes extraPos).workTapes j = extraTapes j := by
  simp [embed, extend, hj]

/-- The head of a tape outside the image of `e` sits where it was supplied to. -/
@[simp]
lemma workTapePos_embed_of_notMem_range (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) {j : Fin k'}
    (hj : j ∉ Set.range e) :
    (embed e cfg extraTapes extraPos).workTapePos j = extraPos j := by
  simp [embed, extend, hj]

/-- **Handing a fresh block of tapes to a machine.** A configuration in `tm`'s initial state, with
the input head at the start and the tapes in the image of `e` blank and rewound, is the embedded
initial configuration of `tm`, with whatever the other tapes hold and with the output produced so
far. This is what lets a machine be started inside a bigger one without knowing anything about the
configuration the previous machine left behind, beyond its output and that it did not touch this
block. -/
lemma eq_embed_initCfg (e : Fin k ↪ Fin k') (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k' Symbol State input) (hstate : cfg.state = some tm.q₀) (hpos : cfg.inputPos = 1)
    (hblank : ∀ i, cfg.workTapes (e i) = fun _ => none)
    (hzero : ∀ i, cfg.workTapePos (e i) = 0) :
    cfg = (embed e (tm.initCfg input) cfg.workTapes cfg.workTapePos).prependOutput cfg.output := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simpa [embed] using hstate
  · simpa [embed] using hpos
  · exact (extend_eq_self e _ cfg.workTapes hblank).symm
  · exact (extend_eq_self e _ cfg.workTapePos hzero).symm
  · simp [embed]

end ExtendTapes

/-- Relabel the work tapes by an injection, leaving every tape outside its image idle. -/
def extendTapes (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k') :
    MultiTapeTM k' Symbol State where
  q₀ := tm.q₀
  tr q input work :=
    let out := tm.tr q input (work ∘ e)
    ⟨out.inputMove, ExtendTapes.extend e out.workActions (fun _ => (none, 0)), out.outS, out.q'⟩

namespace ExtendTapes

variable (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
variable (cfg : Cfg k Symbol State input)
variable (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ)

/-- Tape extension preserves a step and every unused tape. -/
lemma step_embed :
    (tm.extendTapes e).step (embed e cfg extraTapes extraPos) =
      embed e (tm.step cfg) extraTapes extraPos := by
  have hwork : (embed e cfg extraTapes extraPos).workTapeSymbols ∘ e = cfg.workTapeSymbols := by
    funext i
    simp [embed, Cfg.workTapeSymbols]
  cases hs : cfg.state with
  | none => simp [step, embed, hs]
  | some q =>
    simp only [step, embed, hs, extendTapes, Cfg.inputSymbol] at hwork ⊢
    rw [hwork]
    apply Cfg.ext <;> try rfl
    · funext j p
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        simp only [extend_apply]
      · simp [extend, hj]
    · funext j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        simp only [extend_apply]
      · simp [extend, hj]

/-- Extending the tape count does not change the execution time. -/
lemma runFrom_embed (n : ℕ) :
    (tm.extendTapes e).runFrom (embed e cfg extraTapes extraPos) n =
      embed e (tm.runFrom cfg n) extraTapes extraPos := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runFrom_succ_eq_step', ih, step_embed, runFrom_succ_eq_step']

/-- An injected tape visits exactly the native tape's positions. -/
lemma spaceUsedByTape_embed (n : ℕ) (i : Fin k) :
    (tm.extendTapes e).spaceUsedByTape (embed e cfg extraTapes extraPos) n (e i) =
      tm.spaceUsedByTape cfg n i := by
  simp only [spaceUsedByTape, visitedByTapeHead, runFrom_embed]
  simp only [embed, extend_apply]

/-- An unused tape visits just its initial cell. -/
lemma spaceUsedByTape_extra (n : ℕ) (j : Fin k') (hj : j ∉ Set.range e) :
    (tm.extendTapes e).spaceUsedByTape (embed e cfg extraTapes extraPos) n j = 1 := by
  simp only [spaceUsedByTape, visitedByTapeHead, runFrom_embed]
  simp [embed, extend, hj, Finset.image_const]

/-- The extra space is exactly one visited cell for each unused tape. -/
lemma spaceUsed_embed (n : ℕ) :
    (tm.extendTapes e).spaceUsed (embed e cfg extraTapes extraPos) n =
      tm.spaceUsed cfg n + (k' - k) := by
  unfold spaceUsed
  rw [← Finset.sum_add_sum_compl (Finset.univ.map e)]
  congr 1
  · simp [Finset.sum_map, spaceUsedByTape_embed]
  · calc
      _ = ∑ j ∈ (Finset.univ.map e)ᶜ, 1 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact spaceUsedByTape_extra tm e cfg extraTapes extraPos n j (by simpa using hj)
      _ = k' - k := by simp [Finset.card_compl]

end ExtendTapes

/-- The extended machine starts on blank tapes, with the unused ones blank as well. -/
lemma initCfg_extendTapes (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (input : List Symbol) :
    (tm.extendTapes e).initCfg input =
      ExtendTapes.embed e (tm.initCfg input) (fun _ _ => none) (fun _ => 0) := by
  ext i p <;> simp [ExtendTapes.embed, ExtendTapes.extend, extendTapes]

/-- Starting with blank work tapes commutes with tape extension. -/
lemma runFrom_extendTapes (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (input : List Symbol) (n : ℕ) :
    (tm.extendTapes e).runFrom ((tm.extendTapes e).initCfg input) n =
      ExtendTapes.embed e (tm.runFrom (tm.initCfg input) n) (fun _ _ => none) (fun _ => 0) := by
  rw [initCfg_extendTapes, ExtendTapes.runFrom_embed]

/-- Tape extension costs exactly one visited cell for each unused tape. -/
lemma spaceUsed_extendTapes (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (input : List Symbol) (n : ℕ) :
    (tm.extendTapes e).spaceUsed ((tm.extendTapes e).initCfg input) n =
      tm.spaceUsed (tm.initCfg input) n + (k' - k) := by
  rw [initCfg_extendTapes, ExtendTapes.spaceUsed_embed]

end Turing.MultiTapeTM
