/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Data.List.IsChainFromTo

/-!
# Finite executions of LTS

This is a *draft PR* demonstrating an inductive approach to LTS executions.
-/

@[expose] public section

namespace Cslib.LTS

variable {State Label : Type*} {lts : LTS State Label}

/-- `Execution` extends `MTr` by providing the intermediate states of a multistep transition. -/
@[mk_iff]
inductive Execution (lts : LTS State Label) : State → List Label → State → List State → Prop where
  /-- Every state has an execution of zero steps terminating in itself. -/
  | refl (s : State) : lts.Execution s [] s [s]
  /-- Equivalent of `MTr.stepL` for executions. -/
  | stepL {s₁ s₂ s₃ : State} {μ : Label} {μs : List Label} {ss : List State}
      (htr : lts.Tr s₁ μ s₂) (hexec : lts.Execution s₂ μs s₃ ss) :
      lts.Execution s₁ (μ :: μs) s₃ (s₁ :: ss)

namespace Execution

theorem of_tr (h : lts.Tr s₁ μ s₂) : lts.Execution s₁ [μ] s₂ [s₁, s₂] :=
  .stepL h (.refl s₂)

@[scoped grind →]
theorem length (h : lts.Execution s₁ μs s₂ ss) : ss.length = μs.length + 1 := by
  induction h <;> simp_all

@[scoped grind .]
theorem length_ss_pos (h : lts.Execution s₁ μs s₂ ss) : 0 < ss.length :=
  h.length ▸ Nat.zero_lt_succ μs.length

/-- Every execution has at least one intermediate state. -/
@[scoped grind .]
theorem ss_ne_nil (h : lts.Execution s₁ μs s₂ ss) : ss ≠ [] :=
  ss.ne_nil_iff_length_pos.mpr h.length_ss_pos

@[deprecated (since := "2026-10-01")] alias nonEmpty_states := ss_ne_nil

@[scoped grind →]
theorem start (h : lts.Execution s₁ μs s₂ ss) : ss[0]'h.length_ss_pos = s₁ := by
  cases h <;> rfl

theorem head (h : lts.Execution s₁ μs s₂ ss) : ss.head h.ss_ne_nil = s₁ := by
  cases h <;> rfl

@[scoped grind .]
theorem getLast (h : lts.Execution s₁ μs s₂ ss) :
    ss.getLast h.ss_ne_nil = s₂ := by
  induction h with
  | refl => rfl
  | stepL htr he ih => rw [List.getLast_cons he.ss_ne_nil, ih]

@[scoped grind →]
theorem last (h : lts.Execution s₁ μs s₂ ss) :
    ss[ss.length - 1]'(by lia [h.length_ss_pos]) = s₂ := by
  simp_rw [← h.getLast]
  apply List.getElem_length_sub_one_eq_getLast

@[scoped grind →]
theorem trans (h : lts.Execution s₁ μs s₂ ss) (k : ℕ) (hk : k < μs.length) :
    lts.Tr (ss[k]'(by lia [h.length])) μs[k] (ss[k + 1]'(by lia [h.length])) := by
  induction h generalizing k with
  | refl => grind
  | @stepL s₁ s₂ s₃ μ μs ss htr he ih =>
    obtain (rfl | ⟨k, hk, rfl⟩) : k = 0 ∨ ∃ k' < μs.length, k = k' + 1 := by
      rcases k with (_ | k)
      · exact Or.inl rfl
      · exact Or.inr ⟨k, k.succ_lt_succ_iff.mp hk, rfl⟩
    · convert! htr
      exact he.start
    · exact ih k (by lia)

protected theorem mk {s₁ s₂ : State} {μs : List Label} {ss : List State}
    (length : ss.length = μs.length + 1) (start : ss[0] = s₁)
    (last : ss[ss.length - 1] = s₂)
    (trans : ∀ k (hk : k < μs.length), lts.Tr ss[k] μs[k] ss[k + 1]) :
    lts.Execution s₁ μs s₂ ss := by
  cases ss with
  | nil => simp at length
  | cons s ss =>
    obtain rfl : s = s₁ := start
    induction ss generalizing s μs with
    | nil => grind [Execution.refl]
    | cons s' ss ih =>
      simp_rw [List.length_cons, Nat.add_right_cancel_iff] at length
      obtain ⟨μ, μs, rfl⟩ : ∃ μ μs', μs = (μ :: μs') := μs.length_pos_iff_exists_cons.mp (by lia)
      have htr : lts.Tr s μ s' := trans 0 (by simp)
      refine (ih s' length (by simpa using last) ?_).stepL htr
      intro k hk
      apply trans (k + 1)
      simpa

/-- Deconstruction of executions with `List.cons`. -/
theorem cons_invert (h : lts.Execution s₁ (μ :: μs) s₂ (s₁ :: ss)) :
    lts.Execution (ss[0]'(by grind)) μs s₂ ss := by
  rcases h with (_ | ⟨_, he⟩)
  rwa [he.start]

theorem cons_cons_invert (h : lts.Execution s₁ (μ :: μs) s₂ (s₁' :: s :: ss)) :
    lts.Execution s μs s₂ (s :: ss) := by
  rcases h with (_ | ⟨_, he⟩)
  convert he using 1
  exact he.start

theorem tail_of_length_pos (he : lts.Execution s₁ μs s₂ ss) (hlen : 0 < μs.length) :
    lts.Execution (ss[1]'(by grind)) μs.tail s₂ ss.tail := by
  rcases he with (_ | ⟨_, he⟩)
  · contradiction
  · convert! he
    simpa using he.start

/-- A multistep transition implies the existence of an execution. -/
@[scoped grind →]
theorem of_mTr {lts : LTS State Label}
    {s1 : State} {μs : List Label} {s2 : State}
    (h : lts.MTr s1 μs s2) : ∃ ss : List State, lts.Execution s1 μs s2 ss := by
  induction h
  case refl t =>
    use [t], .refl t
  case stepL t1 μ t2 μs t3 htr hmtr ih =>
    obtain ⟨ss', h⟩ := ih
    use t1 :: ss', h.stepL htr

/-- Converts an execution into a multistep transition. -/
@[scoped grind →]
theorem to_mTr (hexec : lts.Execution s1 μs s2 ss) :
    lts.MTr s1 μs s2 := by
  induction hexec with
  | refl => exact .refl
  | stepL htr he ih => exact ih.stepL htr

/-- The states visited by an execution form a chain from the initial to the final state
in the underlying unlabelled relation. -/
theorem isChainFromTo (hexec : lts.Execution s1 μs s2 ss) :
    ss.IsChainFromTo lts.UnlabelledTr s1 s2 := by
  induction hexec with
  | refl => exact List.isChainFromTo_singleton
  | stepL htr _ ih => exact ih.cons ⟨_, htr⟩

/-- The states visited by an execution form a chain in the underlying unlabelled relation. -/
theorem isChain (hexec : lts.Execution s1 μs s2 ss) :
    ss.IsChain lts.UnlabelledTr :=
  (Execution.isChainFromTo hexec).isChain

-- open scoped Execution
/-- Correspondence of multistep transitions and executions. -/
@[scoped grind =]
theorem mTr_iff_execution :
    lts.MTr s1 μs s2 ↔ ∃ ss : List State, lts.Execution s1 μs s2 ss := by
  grind

/-- The composition of two executions is an execution. -/
theorem comp
    {lts : LTS State Label} {s r t : State} {μs1 μs2 : List Label} {ss1 ss2 : List State}
    (h1 : lts.Execution s μs1 r ss1) (h2 : lts.Execution r μs2 t ss2) :
    lts.Execution s (μs1 ++ μs2) t (ss1 ++ ss2.tail) := by
  induction h1 with
  | refl =>
    convert! h2
    simp [← h2.head]
  | stepL htr he ih => exact (ih h2).stepL htr

-- theorem take (he : lts.Execution s μs t ss) (n : ℕ) (hn : n ≤ μs.length) :
--     lts.Execution s (μs.take n) (ss[n]'(by grind)) (ss.take (n + 1)) := by
--   apply Execution.mk
--   · simpa using he.start
--   · simp [he.length, Nat.min_eq_left hn]
--   · simp
--     grind [he.trans]

theorem take (he : lts.Execution s μs t ss) (n : ℕ) (hn : n ≤ μs.length) :
    lts.Execution s (μs.take n) (ss[n]'(by grind)) (ss.take (n + 1)) := by
  induction he generalizing n with
  | refl => simpa using .refl _
  | stepL htr he ih =>
    rcases n with (_ | n)
    · simpa using .refl _
    · simpa using (ih n (by grind)).stepL htr

theorem drop (he : lts.Execution s μs t ss) (n : ℕ) (hn : n ≤ μs.length) :
    lts.Execution (ss[n]'(by grind)) (μs.drop n) t (ss.drop n) := by
  induction he generalizing n with
  | refl =>
    obtain rfl : n = 0 := by simpa using hn
    simpa using .refl _
  | stepL htr he ih =>
    rcases n with (_ | n)
    · rw [← he.start] at htr
      exact .stepL htr (ih 0 <| Nat.zero_le _)
    · apply ih
      simpa using hn

/-- An execution can be split at any intermediate state into two executions. -/
theorem split
    {lts : LTS State Label} {s t : State} {μs : List Label} {ss : List State}
    (he : lts.Execution s μs t ss) (n : ℕ) (hn : n ≤ μs.length) :
    lts.Execution s (μs.take n) (ss[n]'(by grind)) (ss.take (n + 1)) ∧
    lts.Execution (ss[n]'(by grind)) (μs.drop n) t (ss.drop n) :=
  ⟨he.take n hn, he.drop n hn⟩

end Execution

end Cslib.LTS
