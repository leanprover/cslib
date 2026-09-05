/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Data.Fintype.Card

/-!
# Extending and reindexing work tapes

`extendTapes` embeds a machine's work tapes along an injection. The extra tapes are idle, and each
native step still takes exactly one step. The configuration embedding permits arbitrary contents
and head positions on the extra tapes, so the transformation also applies to intermediate runs.
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

/-- Embed a native configuration while retaining arbitrary data on the unused tapes. -/
def embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    Cfg k' Symbol State input where
  state := cfg.state
  inputPos := cfg.inputPos
  workTapes := extend e cfg.workTapes extraTapes
  workTapePos := extend e cfg.workTapePos extraPos
  output := cfg.output

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

/-- Starting with blank work tapes commutes with tape extension. -/
lemma runFrom_extendTapes (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (input : List Symbol) (n : ℕ) :
    (tm.extendTapes e).runFrom ((tm.extendTapes e).initCfg input) n =
      ExtendTapes.embed e (tm.runFrom (tm.initCfg input) n) (fun _ _ => none) (fun _ => 0) := by
  have hinit : (tm.extendTapes e).initCfg input =
      ExtendTapes.embed e (tm.initCfg input) (fun _ _ => none) (fun _ => 0) := by
    ext i p <;> simp [ExtendTapes.embed, ExtendTapes.extend, extendTapes]
  rw [hinit, ExtendTapes.runFrom_embed]

end Turing.MultiTapeTM
