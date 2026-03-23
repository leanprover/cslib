/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic

@[expose] public section

/-!
# Finite executions of LTS
-/

namespace Cslib

variable {State Label : Type*} {lts : LTS State Label}

/-- LTS.Execution extends LTS.MTr by providing the intermediate states of a multistep transition. -/
@[scoped grind =]
def LTS.Execution (lts : LTS State Label) (s1 : State) (μs : List Label) (s2 : State)
    (ss : List State) : Prop :=
  ∃ _ : ss.length = μs.length + 1, ss[0] = s1 ∧ ss[ss.length - 1] = s2 ∧
  ∀ k, {_ : k < μs.length} → lts.Tr ss[k] μs[k] ss[k + 1]

/-- Every execution has at least one intermediate state. -/
@[scoped grind →]
theorem LTS.Execution.nonEmpty_states (h : lts.Execution s1 μs s2 ss) :
    ss ≠ [] := by grind

/-- Every state has an execution of zero steps terminating in itself. -/
@[scoped grind ⇒]
theorem LTS.Execution.refl (lts : LTS State Label) (s : State) : lts.Execution s [] s [s] := by
  grind

/-- Equivalent of `MTr.stepL` for executions. -/
theorem LTS.Execution.stepL {lts : LTS State Label} (htr : lts.Tr s1 μ s2)
    (hexec : lts.Execution s2 μs s3 ss) : lts.Execution s1 (μ :: μs) s3 (s1 :: ss) := by grind

/-- Deconstruction of executions with `List.cons`. -/
theorem LTS.Execution.cons_invert (h : lts.Execution s1 (μ :: μs) s2 (s1 :: ss)) :
    lts.Execution (ss[0]'(by grind)) μs s2 ss := by
  obtain ⟨_, _, _, h4⟩ := h
  exists (by grind)
  constructorm* _∧_
  · rfl
  · grind
  · intro k valid
    specialize h4 k <;> grind

/-- A multistep transition implies the existence of an execution. -/
@[scoped grind →]
theorem LTS.Execution.of_mTr {lts : LTS State Label}
    {s1 : State} {μs : List Label} {s2 : State}
    (h : lts.MTr s1 μs s2) : ∃ ss : List State, lts.Execution s1 μs s2 ss := by
  induction h
  case refl t =>
    use [t]
    grind
  case stepL t1 μ t2 μs t3 htr hmtr ih =>
    obtain ⟨ss', _⟩ := ih
    use t1 :: ss'
    grind

/-- Converts an execution into a multistep transition. -/
@[scoped grind →]
theorem LTS.Execution.to_mTr (hexec : lts.Execution s1 μs s2 ss) :
    lts.MTr s1 μs s2 := by
  induction ss generalizing s1 μs
  case nil => grind
  case cons s1' ss ih =>
    let ⟨hlen, hstart, hfinal, hexec'⟩ := hexec
    have : s1' = s1 := by grind
    rw [this] at hexec' hexec
    cases μs
    · grind
    case cons μ μs =>
      specialize ih (s1 := ss[0]'(by grind)) (μs := μs)
      apply LTS.Execution.cons_invert at hexec
      apply LTS.MTr.stepL
      · have : lts.Tr s1 μ (ss[0]'(by grind)) := by grind
        apply this
      · grind

open scoped LTS.Execution
/-- Correspondence of multistep transitions and executions. -/
@[scoped grind =]
theorem LTS.mTr_iff_execution :
    lts.MTr s1 μs s2 ↔ ∃ ss : List State, lts.Execution s1 μs s2 ss := by
  grind

private lemma LTS.Execution.comp_helper
    {lts : LTS State Label} {s r t : State} {μs1 μs2 : List Label} {ss1 ss2 : List State}
    (h1 : lts.Execution s μs1 r ss1) (h2 : lts.Execution r μs2 t ss2)
    (k : ℕ) (h_k : k < ss2.length) :
    (ss1 ++ ss2.tail)[μs1.length + k]'(by grind) = ss2[k] := by
  by_cases h : k = 0
  · simp (disch := grind) only [h, List.getElem_append_left]
    grind
  · simp (disch := grind) only [List.getElem_append_right, List.getElem_tail]
    have : μs1.length + k - ss1.length + 1 = k := by grind
    grind

/-- The composition of two executions is an execution. -/
theorem LTS.Execution.comp
    {lts : LTS State Label} {s r t : State} {μs1 μs2 : List Label} {ss1 ss2 : List State}
    (h1 : lts.Execution s μs1 r ss1) (h2 : lts.Execution r μs2 t ss2) :
    lts.Execution s (μs1 ++ μs2) t (ss1 ++ ss2.tail) := by
  have h0 : (ss1 ++ ss2.tail).length = (μs1 ++ μs2).length + 1 := by grind
  use h0
  split_ands
  · grind
  · have := LTS.Execution.comp_helper h1 h2 μs2.length
    grind only [Execution, = List.length_append]
  · intro k h_k
    by_cases k < μs1.length
    · grind only [Execution, = List.getElem_append]
    · have := LTS.Execution.comp_helper h1 h2 (k - μs1.length)
      have := LTS.Execution.comp_helper h1 h2 (k - μs1.length + 1)
      grind

/-- An execution can be split at any intermediate state into two executions. -/
theorem LTS.Execution.split
    {lts : LTS State Label} {s t : State} {μs : List Label} {ss : List State}
    (he : lts.Execution s μs t ss) (n : ℕ) (hn : n ≤ μs.length) :
    lts.Execution s (μs.take n) (ss[n]'(by grind)) (ss.take (n + 1)) ∧
    lts.Execution (ss[n]'(by grind)) (μs.drop n) t (ss.drop n) := by
  have : n + (ss.length - n - 1) = ss.length - 1 := by grind
  simp [Execution]
  grind

/-- A multistep transition over a concatenation can be split into two multistep transitions. -/
theorem LTS.MTr.split {lts : LTS State Label} {s0 : State} {μs1 μs2 : List Label} {s2 : State}
    (h : lts.MTr s0 (μs1 ++ μs2) s2) : ∃ s1, lts.MTr s0 μs1 s1 ∧ lts.MTr s1 μs2 s2 := by
  obtain ⟨ss, h_ss⟩ := LTS.Execution.of_mTr h
  have := LTS.Execution.split h_ss μs1.length
  grind

end Cslib
