/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Composition.Rewind

import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas
import Mathlib.Algebra.BigOperators.Fin

/-!
# Correctness and resource bounds for multi-tape composition

`comp_haltsWithOutput` gives operational correctness. `comp_computesInTimeAndSpace` composes
individual computations, charging the rewind and extra tape to the actual intermediate output
length. The function-level interface is in `MultiTape.Combinators.Comp`.

The first machine takes one composite step per native step; the second takes two. The bounds
include the intermediate tape and both blank boundary cells. They permit padded halting times.
As in `MultiTapeTM`, these results do not require finite alphabets or state types.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Composition

variable {k₀ k₁ : ℕ}
variable {Symbol State₀ State₁ : Type*}

variable (tm₀ : MultiTapeTM k₀ Symbol State₀) (tm₁ : MultiTapeTM k₁ Symbol State₁)

/--
After both component machines halt, the composite machine halts with the output of the second
machine.

If the first machine halts on `input` at exactly time `u` having produced `out₀`, and the second
machine has halted on input `out₀` by time `v` having produced `out₁`, then after
`u + (out₀.length + 3) + 2 * v` steps — the first machine's run, a rewind of the intermediate
output, and a two-steps-per-step simulation of the second machine — the composite machine on
`input` has halted with output exactly `out₁`.
-/
theorem comp_haltsWithOutput
    {input out₀ out₁ : List Symbol} {u v : ℕ}
    (hhalt₀ : (tm₀.runFrom (tm₀.initCfg input) u).state = none)
    (hactive₀ : ∀ m < u, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none)
    (hout₀ : (tm₀.runFrom (tm₀.initCfg input) u).output = out₀)
    (hhalt₁ : (tm₁.runFrom (tm₁.initCfg out₀) v).state = none)
    (hout₁ : (tm₁.runFrom (tm₁.initCfg out₀) v).output = out₁) :
    ((comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input)
        (u + (out₀.length + 3) + 2 * v)).state = none ∧
      ((comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input)
          (u + (out₀.length + 3) + 2 * v)).output = out₁ := by
  subst out₀
  subst out₁
  have hfinal := runFrom_secondPhase tm₀ tm₁
    (tm₀.runFrom (tm₀.initCfg input) u)
    (tm₁.initCfg (tm₀.runFrom (tm₀.initCfg input) u).output) v
  rw [← runFrom_to_secondInit tm₀ tm₁ input u hhalt₀ hactive₀, ← runFrom_add] at hfinal
  rw [hfinal]
  simp only [embedSecond, hhalt₁, and_self]

/-- Final first-component configuration used throughout the resource analysis. -/
@[simp] private abbrev firstFinalCfg
    (tm₀ : MultiTapeTM k₀ Symbol State₀) (input : List Symbol) (u : ℕ) :
    Cfg k₀ Symbol State₀ input :=
  tm₀.runFrom (tm₀.initCfg input) u

/-- Initial second-component configuration for the output of the first component. -/
private abbrev secondInitCfg
    (tm₀ : MultiTapeTM k₀ Symbol State₀)
    (tm₁ : MultiTapeTM k₁ Symbol State₁)
    (input : List Symbol) (u : ℕ) :
    Cfg k₁ Symbol State₁ (firstFinalCfg tm₀ input u).output :=
  tm₁.initCfg (firstFinalCfg tm₀ input u).output

/-- Second-component configuration after `m` simulated steps. -/
private abbrev secondCfgAt
    (tm₀ : MultiTapeTM k₀ Symbol State₀)
    (tm₁ : MultiTapeTM k₁ Symbol State₁)
    (input : List Symbol) (u m : ℕ) :
    Cfg k₁ Symbol State₁ (firstFinalCfg tm₀ input u).output :=
  tm₁.runFrom (secondInitCfg tm₀ tm₁ input u) m

/-- Duration used to simulate component runs of lengths `u` and `v`. -/
private abbrev compositionTotalTime
    (tm₀ : MultiTapeTM k₀ Symbol State₀) (input : List Symbol) (u v : ℕ) : ℕ :=
  u + ((firstFinalCfg tm₀ input u).output.length + 3) + 2 * v

/-- The first component must switch phases at its earliest halting time. -/
private structure CompositionRunSpec
    (tm₀ : MultiTapeTM k₀ Symbol State₀)
    (input : List Symbol) (u : ℕ) : Prop where
  firstHalted : (firstFinalCfg tm₀ input u).state = none
  firstActive : ∀ m < u, (tm₀.runFrom (tm₀.initCfg input) m).state ≠ none

/-- A named phase witness for a configuration occurring in a complete composite run. -/
private inductive CompositionCfgPhase
    (tm₀ : MultiTapeTM k₀ Symbol State₀)
    (tm₁ : MultiTapeTM k₁ Symbol State₁)
    (input : List Symbol) (u v : ℕ)
    (cfg : Cfg (compositionTapeCount k₀ k₁) Symbol
      (CompositionState State₀ State₁) input) : Prop
  | first (m : ℕ) (hm : m ≤ u)
      (hcfg : cfg = embedFirst tm₀ tm₁
        (tm₀.runFrom (tm₀.initCfg input) m))
  | rewind (s : ℕ)
      (hs : s ≤ (firstFinalCfg tm₀ input u).output.length)
      (hcfg : cfg = intermediateCfg tm₀ tm₁
          (firstFinalCfg tm₀ input u)
          (.inr (.inl .scan))
          (((firstFinalCfg tm₀ input u).output.length : ℤ) - 1 - s))
  | initialClassify
      (hcfg : cfg = intermediateCfg tm₀ tm₁
          (firstFinalCfg tm₀ input u)
          (.inr (.inr (.classify tm₁.q₀ .right))) 0)
  | second (m : ℕ) (hm : m ≤ v)
      (hcfg : cfg = embedSecond tm₀ tm₁
          (firstFinalCfg tm₀ input u)
          (secondCfgAt tm₀ tm₁ input u m))
  | secondClassify (m : ℕ) (hm : m < v) (boundary : InputBoundary)
      (hcfg : cfg = classifyCfg tm₀ tm₁
          (firstFinalCfg tm₀ input u)
          (secondCfgAt tm₀ tm₁ input u (m + 1))
          boundary)

/--
Every prefix of a complete composite run is in one of the configurations described by
the first simulation, the rewind, the initial classifier, or an even or odd second-phase step.
-/
private lemma runFrom_composition_cases
    (input : List Symbol) (u v r : ℕ)
    (hrun : CompositionRunSpec tm₀ input u)
    (hr : r ≤ compositionTotalTime tm₀ input u v) :
    CompositionCfgPhase tm₀ tm₁ input u v
      ((comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input) r) := by
  by_cases hfirst : r ≤ u
  · exact .first r hfirst (runFrom_firstPhase tm₀ tm₁ input r
      (fun m hm => hrun.firstActive m (lt_of_lt_of_le hm hfirst)))
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le (by omega : u ≤ r)
  have hprefix := runFrom_firstPhase tm₀ tm₁ input u hrun.firstActive
  by_cases hrewind : offset ≤ (firstFinalCfg tm₀ input u).output.length + 1
  · refine .rewind (offset - 1) (by omega) ?_
    rw [runFrom_add, hprefix]
    convert runFrom_firstHalt_rewind tm₀ tm₁
      (firstFinalCfg tm₀ input u) hrun.firstHalted (offset - 1) (by omega) using 1
    congr 1
    omega
  by_cases hclassify : offset = (firstFinalCfg tm₀ input u).output.length + 2
  · refine .initialClassify ?_
    rw [runFrom_add, hprefix, hclassify]
    exact runFrom_firstHalt_classify tm₀ tm₁ _ hrun.firstHalted
  obtain ⟨secondSteps, hoffset⟩ := Nat.exists_eq_add_of_le
    (by omega : (firstFinalCfg tm₀ input u).output.length + 3 ≤ offset)
  have hsecondSteps : secondSteps ≤ 2 * v := by
    dsimp only [compositionTotalTime] at hr
    omega
  have hsecond :
      (comp tm₀ tm₁).runFrom ((comp tm₀ tm₁).initCfg input) (u + offset) =
        (comp tm₀ tm₁).runFrom
          (embedSecond tm₀ tm₁ (firstFinalCfg tm₀ input u)
            (secondInitCfg tm₀ tm₁ input u)) secondSteps := by
    rw [hoffset, ← Nat.add_assoc, runFrom_add,
      runFrom_to_secondInit tm₀ tm₁ input u hrun.firstHalted hrun.firstActive]
  rcases Nat.even_or_odd' secondSteps with ⟨m, heven | hodd⟩
  · refine .second m (by omega) ?_
    rw [hsecond, heven]
    exact runFrom_secondPhase tm₀ tm₁ _ _ m
  · obtain ⟨boundary, hboundary⟩ := runFrom_secondPhase_odd tm₀ tm₁
      (firstFinalCfg tm₀ input u) (secondInitCfg tm₀ tm₁ input u) m
    exact .secondClassify m (by omega) boundary (by rw [hsecond, hodd, hboundary])

/-!
## Resource bounds and function-level correctness
-/


/-- Decompose composite space usage into the first, intermediate, and second tape blocks. -/
private lemma compositionSpaceUsed_eq
    {input : List Symbol}
    (cfg : Cfg (compositionTapeCount k₀ k₁) Symbol
      (CompositionState State₀ State₁) input)
    (t : ℕ) :
    (comp tm₀ tm₁).spaceUsed cfg t =
      (∑ i : Fin k₀, (comp tm₀ tm₁).spaceUsedByTape cfg t
        (compositionFirstTapeIdx k₁ i)) +
      (comp tm₀ tm₁).spaceUsedByTape cfg t
        (compositionIntermediateTapeIdx k₀ k₁) +
      ∑ i : Fin k₁, (comp tm₀ tm₁).spaceUsedByTape cfg t
        (compositionSecondTapeIdx k₀ k₁ i) := by
  unfold spaceUsed
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
  congr 1

/-- Every first-component tape position in a complete composite run occurs in the first run. -/
private lemma exists_firstComponent_tapePos_eq
    (input : List Symbol) (u v r : ℕ)
    (hrun : CompositionRunSpec tm₀ input u)
    (hr : r ≤ compositionTotalTime tm₀ input u v)
    (i : Fin k₀) :
    ∃ m ≤ u,
      ((comp tm₀ tm₁).runFrom
        ((comp tm₀ tm₁).initCfg input) r).workTapePos
          (compositionFirstTapeIdx k₁ i) =
        (tm₀.runFrom (tm₀.initCfg input) m).workTapePos i := by
  have hphase := runFrom_composition_cases tm₀ tm₁ input u v r hrun hr
  have hidx_ne : i.val ≠ k₀ := by omega
  cases hphase with
  | first m hm hcfg =>
    refine ⟨m, hm, ?_⟩
    rw [hcfg]
    simp [embedFirst, compositionFirstTapeIdx]
  | rewind _ _ hcfg | initialClassify hcfg =>
    refine ⟨u, le_rfl, ?_⟩
    rw [hcfg]
    simp [intermediateCfg, embedFirst, compositionFirstTapeIdx, hidx_ne]
  | second _ _ hcfg | secondClassify _ _ _ hcfg =>
    refine ⟨u, le_rfl, ?_⟩
    rw [hcfg]
    simp [classifyCfg, embedSecond, compositionFirstTapeIdx]

/-- Every second-component tape position in a complete composite run occurs in the second run. -/
private lemma exists_secondComponent_tapePos_eq
    (input : List Symbol) (u v r : ℕ)
    (hrun : CompositionRunSpec tm₀ input u)
    (hr : r ≤ compositionTotalTime tm₀ input u v)
    (i : Fin k₁) :
    ∃ m ≤ v,
      ((comp tm₀ tm₁).runFrom
        ((comp tm₀ tm₁).initCfg input) r).workTapePos
          (compositionSecondTapeIdx k₀ k₁ i) =
        (secondCfgAt tm₀ tm₁ input u m).workTapePos i := by
  have hphase := runFrom_composition_cases tm₀ tm₁ input u v r hrun hr
  have hidx_not_lt : ¬ k₀ + 1 + i.val < k₀ := by omega
  have hidx_ne : k₀ + 1 + i.val ≠ k₀ := by omega
  cases hphase with
  | first _ _ hcfg =>
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [hcfg]
    simp [embedFirst, compositionSecondTapeIdx, secondCfgAt, secondInitCfg, runFrom,
      hidx_not_lt, hidx_ne]
  | rewind _ _ hcfg | initialClassify hcfg =>
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [hcfg]
    simp [intermediateCfg, embedFirst, compositionSecondTapeIdx,
      secondCfgAt, secondInitCfg, runFrom, hidx_not_lt, hidx_ne]
  | second m hm hcfg =>
    refine ⟨m, hm, ?_⟩
    rw [hcfg]
    simp [embedSecond, compositionSecondTapeIdx, hidx_not_lt, hidx_ne]
  | secondClassify m hm _ hcfg =>
    refine ⟨m + 1, by omega, ?_⟩
    rw [hcfg]
    simp [classifyCfg, embedSecond, compositionSecondTapeIdx,
      hidx_not_lt, hidx_ne]

/-- Throughout a complete composite run, the intermediate head stays between the two blank cells
immediately outside the first component's output. -/
private lemma compositionIntermediateTapePos_mem_Icc
    (input : List Symbol) (u v r : ℕ)
    (hrun : CompositionRunSpec tm₀ input u)
    (hr : r ≤ compositionTotalTime tm₀ input u v) :
    ((comp tm₀ tm₁).runFrom
      ((comp tm₀ tm₁).initCfg input) r).workTapePos
        (compositionIntermediateTapeIdx k₀ k₁) ∈
      Finset.Icc (-1) ((firstFinalCfg tm₀ input u).output.length : ℤ) := by
  have hphase := runFrom_composition_cases tm₀ tm₁ input u v r hrun hr
  cases hphase with
  | first m hm hcfg =>
    have hmoutput := tm₀.runFrom_output_length_mono (tm₀.initCfg input) hm
    dsimp only at hmoutput
    rw [hcfg]
    simp only [tapes, firstFinalCfg, embedFirst, compositionIntermediateTapeIdx_val,
      lt_self_iff_false, ↓reduceDIte, Finset.mem_Icc]
    constructor <;> omega
  | rewind s hs hcfg =>
    rw [hcfg]
    simp only [firstFinalCfg, intermediateCfg, compositionIntermediateTapeIdx_val,
      ↓reduceIte, Finset.mem_Icc] at hs ⊢
    constructor <;> omega
  | initialClassify hcfg =>
    rw [hcfg]
    simp [intermediateCfg]
  | second m _ hcfg =>
    have hp := (secondCfgAt tm₀ tm₁ input u m).inputPos.isLt
    simp only [secondCfgAt, secondInitCfg, firstFinalCfg] at hp
    rw [hcfg]
    simp only [tapes, firstFinalCfg, embedSecond, compositionIntermediateTapeIdx_val,
      lt_self_iff_false, ↓reduceDIte, Finset.mem_Icc]
    unfold InputFromWorkTape.virtualInputPos
    constructor <;> omega
  | secondClassify m _ _ hcfg =>
    have hp := (secondCfgAt tm₀ tm₁ input u (m + 1)).inputPos.isLt
    simp only [secondCfgAt, secondInitCfg, firstFinalCfg] at hp
    rw [hcfg]
    simp only [tapes, firstFinalCfg, classifyCfg, embedSecond,
      compositionIntermediateTapeIdx_val, lt_self_iff_false, ↓reduceDIte,
      Finset.mem_Icc]
    unfold InputFromWorkTape.virtualInputPos
    constructor <;> omega

/-- The intermediate tape visits at most `output.length + 2` cells in a complete run. -/
private lemma compositionIntermediateSpace_le
    (input : List Symbol) (u v : ℕ)
    (hrun : CompositionRunSpec tm₀ input u) :
    (comp tm₀ tm₁).spaceUsedByTape
        ((comp tm₀ tm₁).initCfg input)
        (compositionTotalTime tm₀ input u v)
        (compositionIntermediateTapeIdx k₀ k₁) ≤
      (firstFinalCfg tm₀ input u).output.length + 2 := by
  calc
    _ ≤ (Finset.Icc (-1) ((firstFinalCfg tm₀ input u).output.length : ℤ)).card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨r, hr, rfl⟩ := (comp tm₀ tm₁).mem_visitedByTapeHead.mp hp
      exact compositionIntermediateTapePos_mem_Icc tm₀ tm₁ input u v r hrun (by omega)
    _ = _ := by rw [Int.card_Icc]; omega

/-- Component tape blocks retain their native space bounds; only the intermediate tape is new. -/
private lemma CompositionRunSpec.spaceUsed_le
    {input : List Symbol} {u v : ℕ} (hrun : CompositionRunSpec tm₀ input u) :
    (comp tm₀ tm₁).spaceUsed ((comp tm₀ tm₁).initCfg input)
        (compositionTotalTime tm₀ input u v) ≤
      tm₀.spaceUsed (tm₀.initCfg input) u +
        ((firstFinalCfg tm₀ input u).output.length + 2) +
        tm₁.spaceUsed (secondInitCfg tm₀ tm₁ input u) v := by
  rw [compositionSpaceUsed_eq]
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · apply Finset.sum_le_sum
      intro i _
      exact spaceUsedByTape_le_of_positions _ _ _ _ _ _ _ _
        (fun r hr => exists_firstComponent_tapePos_eq tm₀ tm₁ input u v r hrun hr i)
    · exact compositionIntermediateSpace_le tm₀ tm₁ input u v hrun
  · apply Finset.sum_le_sum
    intro i _
    exact spaceUsedByTape_le_of_positions _ _ _ _ _ _ _ _
      (fun r hr => exists_secondComponent_tapePos_eq tm₀ tm₁ input u v r hrun hr i)

/-- Compose two bounded computations, charging the intermediate tape and rewind to the actual
intermediate output length. Component halting times may be padded. -/
theorem comp_computesInTimeAndSpace
    {input middle output : List Symbol} {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : ComputesInTimeAndSpace tm₀ input middle t₀ s₀)
    (h₁ : ComputesInTimeAndSpace tm₁ middle output t₁ s₁) :
    ∃ t ≤ t₀ + (middle.length + 3) + 2 * t₁,
      ∃ s ≤ s₀ + (middle.length + 2) + s₁,
        ComputesInTimeAndSpace (comp tm₀ tm₁) input output t s := by
  obtain ⟨u, hu, hhaltu, hactiveu⟩ :=
    exists_minimal_halting_time tm₀ (tm₀.initCfg input) t₀ h₀.1
  have houtu : (firstFinalCfg tm₀ input u).output = middle :=
    (tm₀.runFrom_output_eq_of_halt _ hu hhaltu).symm.trans h₀.2.1
  have hrun : CompositionRunSpec tm₀ input u := ⟨hhaltu, hactiveu⟩
  have hspace := hrun.spaceUsed_le tm₀ tm₁ (v := t₁)
  have hspace₀ := tm₀.spaceUsed_mono (tm₀.initCfg input) hu
  dsimp only [compositionTotalTime, secondInitCfg] at hspace
  rw [houtu, h₁.2.2] at hspace
  dsimp only at hspace₀
  rw [h₀.2.2] at hspace₀
  refine ⟨u + (middle.length + 3) + 2 * t₁, by omega,
    (comp tm₀ tm₁).spaceUsed ((comp tm₀ tm₁).initCfg input)
      (u + (middle.length + 3) + 2 * t₁), by omega, ?_⟩
  have hcomp := comp_haltsWithOutput tm₀ tm₁ hhaltu hactiveu houtu h₁.1 h₁.2.1
  exact ⟨hcomp.1, hcomp.2, rfl⟩

end Turing.MultiTapeTM
