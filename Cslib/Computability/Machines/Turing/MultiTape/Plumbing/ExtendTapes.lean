/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Inv
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.StepLemmas
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Reindexing a machine's work tapes along an embedding

`extendTapes tm e`, for an embedding `e : Fin k ↪ Fin k'`, runs `tm` inside a machine with `k'`
work tapes, using the tapes selected by `e`: work tape `e j` plays the role of `tm`'s tape `j`,
and every tape outside the range of `e` is never written and never moves.

The construction is a step-semiconjugation. The configuration map `embed e cfg extraTapes extraPos`
places `cfg` on the tapes in the range of `e` and fills the others with fixed contents `extraTapes`
and head positions `extraPos`; `step` commutes with it unconditionally, so the reindexed run
mirrors the original by `Turing.MultiTapeTM.runFrom_comm_of_step` — no induction. Since the extra
tapes never move, the reindexed run uses the same space on the embedded tapes as `tm` does, plus at
most one cell for each of the remaining tapes.

Both the machine and the configuration map route each target tape `l` through the computable
partial inverse `partialInv e l : Option (Fin k)`, which is `some j` exactly when `e j = l`. Since
they share this scrutinee, the semiconjugation splits tape by tape into a source tape (`some j`) or
an untouched extra tape (`none`).
-/

namespace Turing.MultiTapeTM

variable {k k' : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The computable partial inverse of the embedding `e`: `partialInv e l = some j` when `e j = l`
(such `j` is unique by injectivity), and `none` when `l` lies outside the range of `e`. -/
@[expose] public def partialInv (e : Fin k ↪ Fin k') (l : Fin k') : Option (Fin k) :=
  if h : ∃ j, e j = l then
    some (Fintype.choose (fun j => e j = l)
      (existsUnique_of_exists_of_unique h fun _ _ ha hb => e.injective (ha.trans hb.symm)))
  else none

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

variable {tm : MultiTapeTM k Symbol State} {e : Fin k ↪ Fin k'}
  {cfg : Cfg k Symbol State input} {extraTapes : Fin k' → ℤ → Option Symbol} {extraPos : Fin k' → ℤ}

/-- The partial inverse recovers the source tape of an embedded tape. -/
@[simp]
public lemma partialInv_embed (e : Fin k ↪ Fin k') (j : Fin k) : partialInv e (e j) = some j := by
  have hex : ∃ j', e j' = e j := ⟨j, rfl⟩
  have hpi : partialInv e (e j) = some (Fintype.choose (fun j' => e j' = e j)
      (existsUnique_of_exists_of_unique hex fun _ _ ha hb => e.injective (ha.trans hb.symm))) :=
    dite_eq_left hex
  rw [hpi]
  congr 1
  exact e.injective (Fintype.choose_spec (fun j' => e j' = e j) _)

/-- Outside the range of `e`, the partial inverse is undefined. -/
public lemma partialInv_eq_none (e : Fin k ↪ Fin k') {l : Fin k'} (hl : ¬ ∃ j, e j = l) :
    partialInv e l = none :=
  dite_eq_right hl

/-- If the partial inverse is `some j`, then `e j = l`. -/
public lemma partialInv_eq_some (e : Fin k ↪ Fin k') {l : Fin k'} {j : Fin k}
    (h : partialInv e l = some j) : e j = l := by
  unfold partialInv at h
  by_cases hl : ∃ j, e j = l
  · rw [dite_eq_left hl] at h
    have hspec := Fintype.choose_spec (fun j' => e j' = l)
      (existsUnique_of_exists_of_unique hl fun _ _ ha hb => e.injective (ha.trans hb.symm))
    rw [Option.some_inj] at h
    rw [← h]; exact hspec
  · rw [dite_eq_right hl] at h; exact absurd h (by simp)

@[simp]
public lemma embed_workTapes_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapes (e j) = cfg.workTapes j := by
  simp only [embed, partialInv_embed]

@[simp]
public lemma embed_workTapePos_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapePos (e j) = cfg.workTapePos j := by
  simp only [embed, partialInv_embed]

@[simp]
public lemma embed_workTapeSymbols_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapeSymbols (e j) = cfg.workTapeSymbols j := by
  simp only [Cfg.workTapeSymbols, embed_workTapes_embed, embed_workTapePos_embed]

/-- Reindexing is a step-semiconjugation: the reindexed machine acts on the embedded tapes exactly
as `tm` does, and never touches the extra tapes. -/
public lemma step_embed (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) :
    (tm.extendTapes e).step (embed e cfg extraTapes extraPos)
      = embed e (tm.step cfg) extraTapes extraPos := by
  cases hq : cfg.state with
  | none =>
    have h1 : (embed e cfg extraTapes extraPos).state = none := hq
    rw [step_of_halt h1, step_of_halt hq]
  | some q =>
    have h1 : (embed e cfg extraTapes extraPos).state = some q := hq
    have hin : (embed e cfg extraTapes extraPos).inputSymbol = cfg.inputSymbol := rfl
    have hargs : (fun j : Fin k => (embed e cfg extraTapes extraPos).workTapeSymbols (e j))
        = cfg.workTapeSymbols :=
      funext fun j => embed_workTapeSymbols_embed e cfg extraTapes extraPos j
    rw [step_apply_of_state h1, step_apply_of_state hq]
    simp only [extendTapes, hin, hargs]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext l z
      simp only [Action.apply, embed]
      cases partialInv e l <;> rfl
    · funext l
      simp only [Action.apply, embed]
      cases partialInv e l <;> simp

/-- The reindexed run mirrors the original, with the extra tapes held fixed throughout. -/
public lemma runFrom_embed (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) :
    (tm.extendTapes e).runFrom (embed e cfg extraTapes extraPos) n
      = embed e (tm.runFrom cfg n) extraTapes extraPos :=
  runFrom_comm_of_step (fun c => embed e c extraTapes extraPos)
    (fun c => step_embed tm e c extraTapes extraPos) cfg n

section Space

/-- On an embedded tape `e j`, the reindexed run's head visits exactly the cells `tm`'s head of
tape `j` visits. -/
public lemma visitedByTapeHead_embed_embed (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) (j : Fin k) :
    (tm.extendTapes e).visitedByTapeHead (embed e cfg extraTapes extraPos) n (e j)
      = tm.visitedByTapeHead cfg n j := by
  refine Finset.image_congr fun m _ => ?_
  rw [runFrom_embed, embed_workTapePos_embed]

/-- The head of a tape outside `range e` never leaves its starting position. -/
public lemma workTapePos_embed_of_not_range (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) {l : Fin k'} (hl : ¬ ∃ j, e j = l) :
    ((tm.extendTapes e).runFrom (embed e cfg extraTapes extraPos) n).workTapePos l
      = extraPos l := by
  rw [runFrom_embed]
  simp only [embed, partialInv_eq_none e hl]

/-- **Space bound for a reindexed run.** The embedded tapes use exactly the space `tm` uses; each
of the remaining `k' - k` tapes never moves, so it contributes at most one cell. -/
public lemma spaceUsed_embed_le (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) :
    (tm.extendTapes e).spaceUsed (embed e cfg extraTapes extraPos) n
      ≤ tm.spaceUsed cfg n + (k' - k) := by
  classical
  -- an embedded tape `e j` uses exactly the space of `tm`'s tape `j`
  have key : ∀ j : Fin k,
      (tm.extendTapes e).spaceUsedByTape (embed e cfg extraTapes extraPos) n (e j)
        = tm.spaceUsedByTape cfg n j :=
    fun j => congrArg Finset.card (visitedByTapeHead_embed_embed tm e cfg extraTapes extraPos n j)
  -- a tape outside `range e` never moves, so it uses at most one cell
  have bound1 : ∀ l, ¬ (∃ j, e j = l) →
      (tm.extendTapes e).spaceUsedByTape (embed e cfg extraTapes extraPos) n l ≤ 1 := by
    intro l hl
    refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_singleton (extraPos l)))
    intro z hz
    obtain ⟨m, _, rfl⟩ := mem_visitedByTapeHead.mp hz
    rw [workTapePos_embed_of_not_range tm e cfg extraTapes extraPos m hl]
    exact Finset.mem_singleton_self _
  calc (tm.extendTapes e).spaceUsed (embed e cfg extraTapes extraPos) n
      = (∑ l ∈ Finset.univ \ Finset.univ.image e,
            (tm.extendTapes e).spaceUsedByTape (embed e cfg extraTapes extraPos) n l)
          + ∑ l ∈ Finset.univ.image e,
            (tm.extendTapes e).spaceUsedByTape (embed e cfg extraTapes extraPos) n l :=
        (Finset.sum_sdiff (Finset.subset_univ _)).symm
    _ ≤ (k' - k) + tm.spaceUsed cfg n := by
        refine Nat.add_le_add ?_ (le_of_eq ?_)
        · calc (∑ l ∈ Finset.univ \ Finset.univ.image e,
                  (tm.extendTapes e).spaceUsedByTape (embed e cfg extraTapes extraPos) n l)
              ≤ ∑ _l ∈ Finset.univ \ Finset.univ.image e, 1 := by
                refine Finset.sum_le_sum fun l hl => bound1 l ?_
                rw [Finset.mem_sdiff] at hl
                rintro ⟨j, rfl⟩
                exact hl.2 (Finset.mem_image_of_mem e (Finset.mem_univ j))
            _ = k' - k := by
                rw [Finset.sum_const, smul_eq_mul, mul_one,
                  Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
                  Fintype.card_fin, Finset.card_image_of_injective _ e.injective, Finset.card_univ,
                  Fintype.card_fin]
        · rw [Finset.sum_image fun x _ y _ h => e.injective h]
          simp only [spaceUsed]
          exact Finset.sum_congr rfl fun j _ => key j
    _ = tm.spaceUsed cfg n + (k' - k) := Nat.add_comm _ _

end Space

end Turing.MultiTapeTM
