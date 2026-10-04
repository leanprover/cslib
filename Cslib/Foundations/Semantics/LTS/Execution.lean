/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Ching-Tsun Chou, Thomas Waring
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Data.List.IsChainFromTo

/-!
# Finite executions of LTS

A finite execution of `lts : LTS State Label`, a proposition `lts.Execution s μs t ss`, which says
that `lts` can transition from `s₁` to `s₂` through `ss` using the transition labels `μ`. That is,
the lists have the form `μs = [μ₁, μ₂, ..., μₙ]` and `ss = [s, s₂, s₃, ..., sₙ, t]`, and there are
transitions `lts.Tr s μ₁ s₂`, `lts.Tr s₂ μ₂ s₃`, ..., `lts.Tr sₙ μₙ t`.

We define `Cslib.LTS.Execution` as an inductive proposition, which is equivalent to the definition
in terms of indicies: see `Cslib.LTS.Execution.mk` and `Cslib.LTS.execution_iff_index`.
-/

@[expose] public section

namespace Cslib.LTS

variable {State Label : Type*} {lts : LTS State Label}

/-- `Execution` extends `MTr` by providing the intermediate states of a multistep transition:
`lts.Execution s₁ μs s₂ ss` means that `lts` can transition from `s₁` to `s₂` through `ss` using
the transition labels `μ`. This is equivalent to the proposition:
```lean
∃ _ : ss.length = μs.length + 1, ss[0] = s₁ ∧ ss[ss.length - 1] = s₂ ∧ ∀ k < μs.length, lts.Tr
ss[k] μ[k] ss[k + 1].
```
Access that formulation as a constructor using `Cslib.LTS.Execution.mk`, and its projections as
`Cslib.LTS.Execution.length`, `Cslib.LTS.Execution.start`, `Cslib.LTS.Execution.last` and
`Cslib.LTS.Execution.trans`.
-/
@[mk_iff]
inductive Execution (lts : LTS State Label) :
    (s₁ : State) → (μs : List Label) → (s₂ : State) → (ss : List State) → Prop where
  /-- Every state has an execution of zero steps terminating in itself. -/
  | refl (s : State) : lts.Execution s [] s [s]
  /-- Equivalent of `MTr.stepL` for executions. -/
  | stepL {s₁ s₂ s₃ : State} {μ : Label} {μs : List Label} {ss : List State}
      (htr : lts.Tr s₁ μ s₂) (hexec : lts.Execution s₂ μs s₃ ss) :
      lts.Execution s₁ (μ :: μs) s₃ (s₁ :: ss)

namespace Execution

theorem of_tr (h : lts.Tr s₁ μ s₂) : lts.Execution s₁ [μ] s₂ [s₁, s₂] :=
  .stepL h (.refl s₂)

/-- The lengths of `μs` and `ss` are constrained by the fact that each label `μ ∈ μs` represents
a transition between two states in `ss`. -/
@[scoped grind →]
theorem length (h : lts.Execution s₁ μs s₂ ss) : ss.length = μs.length + 1 := by
  induction h <;> simp_all

theorem length' (h : lts.Execution s₁ μs s₂ ss) :
  μs.length = ss.length - 1 := by simp [h.length]

/-- Transitions have positive length. -/
@[scoped grind .]
theorem length_ss_pos (h : lts.Execution s₁ μs s₂ ss) : 0 < ss.length :=
  h.length ▸ Nat.zero_lt_succ μs.length

/-- Every execution has at least one intermediate state. -/
@[scoped grind .]
theorem ss_ne_nil (h : lts.Execution s₁ μs s₂ ss) : ss ≠ [] :=
  ss.ne_nil_iff_length_pos.mpr h.length_ss_pos

@[deprecated (since := "2026-10-01")] alias nonEmpty_states := ss_ne_nil

/-- `s₁` is the first state of the execution. -/
theorem head (h : lts.Execution s₁ μs s₂ ss) : ss.head h.ss_ne_nil = s₁ := by
  cases h <;> rfl

/-- Alternative accessor for `Cslib.LTS.Execution.head`. -/
theorem start (h : lts.Execution s₁ μs s₂ ss) : ss[0]'h.length_ss_pos = s₁ := by
  rw [← ss.head_eq_getElem h.ss_ne_nil, h.head]

/-- `s₂` is the last state of the execution. -/
@[scoped grind .]
theorem getLast (h : lts.Execution s₁ μs s₂ ss) :
    ss.getLast h.ss_ne_nil = s₂ := by
  induction h with
  | refl => rfl
  | stepL htr he ih => rw [List.getLast_cons he.ss_ne_nil, ih]

/-- Alternative accessor for `Cslib.LTS.Execution.getLast`. -/
@[scoped grind →]
theorem last (h : lts.Execution s₁ μs s₂ ss) :
    ss[ss.length - 1]'(by lia [h.length_ss_pos]) = s₂ := by
  simp_rw [← h.getLast]
  apply List.getElem_length_sub_one_eq_getLast

/-- Alternative accessor for `Cslib.LTS.Execution.getLast`. -/
theorem last' (h : lts.Execution s₁ μs s₂ ss) :
  ss[μs.length]'(by grind) = s₂ := by simp [← h.last, h.length]

/-- `lts` transitions along the `k`th label in `μs` between the `k`th and `(k + 1)`th states in
`ss`. -/
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
    · rw [ss.getElem_cons_zero, μs.getElem_cons_zero, ss.getElem_cons_succ, he.start]
      exact htr
    · exact ih k (by lia)

/-- Alternative constructor for `Cslib.LTS.Execution`, in terms of the indexed collections of
  states and labels. -/
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
    | nil => convert! Execution.refl s <;> grind
    | cons s' ss ih =>
      simp_rw [List.length_cons, Nat.add_right_cancel_iff] at length
      obtain ⟨μ, μs, rfl⟩ : ∃ μ μs', μs = (μ :: μs') := μs.length_pos_iff_exists_cons.mp (by lia)
      refine (ih s' length (by simpa using last) ?_).stepL (trans 0 (by simp))
      intro k hk
      apply trans (k + 1)
      simpa

/-- The inductive definition of `Cslib.LTS.Execution` is equivalent to that in terms of indices. -/
theorem _root_.Cslib.LTS.execution_iff_index :
    lts.Execution s₁ μs s₂ ss ↔
      ∃ (_ : ss.length = μs.length + 1), ss[0] = s₁ ∧ ss[ss.length - 1] = s₂ ∧
      ∀ k (_ : k < μs.length), lts.Tr ss[k] μs[k] ss[k + 1] :=
  ⟨fun h ↦ ⟨h.length, h.start, h.last, h.trans⟩, fun ⟨hl, hs, ht, htr⟩ ↦ .mk hl hs ht htr⟩

/-- Deconstruction of executions with `List.cons`. -/
theorem cons_invert (h : lts.Execution s₁ (μ :: μs) s₂ (s₁ :: ss)) :
    lts.Execution (ss[0]'(by grind)) μs s₂ ss := by
  rcases h with (_ | ⟨_, he⟩)
  rwa [he.start]

/-- Deconstruct a positive-length execution, with a specific value for the second state in the
sequence. -/
theorem cons_cons_invert (h : lts.Execution s₁ (μ :: μs) s₂ (s₁' :: s :: ss)) :
    lts.Execution s μs s₂ (s :: ss) := by
  rcases h with (_ | ⟨_, he⟩)
  rwa [← he.start] at he

/-- Trim the first state from a positive-length execution. -/
theorem tail_of_length_pos (he : lts.Execution s₁ μs s₂ ss) (hlen : 0 < μs.length) :
    lts.Execution (ss[1]'(by grind)) μs.tail s₂ ss.tail := by
  rcases he with (_ | ⟨_, he⟩)
  · contradiction
  · simpa [he.start] using he

/-- A multistep transition implies the existence of an execution. -/
@[scoped grind →]
theorem of_mTr {lts : LTS State Label}
    {s₁ : State} {μs : List Label} {s₂ : State}
    (h : lts.MTr s₁ μs s₂) : ∃ ss : List State, lts.Execution s₁ μs s₂ ss := by
  induction h
  case refl t =>
    use [t], .refl t
  case stepL t1 μ t2 μs t3 htr hmtr ih =>
    obtain ⟨ss', h⟩ := ih
    use t1 :: ss', h.stepL htr

/-- Converts an execution into a multistep transition. -/
@[scoped grind →]
theorem to_mTr (hexec : lts.Execution s₁ μs s₂ ss) :
    lts.MTr s₁ μs s₂ := by
  induction hexec with
  | refl => exact .refl
  | stepL htr he ih => exact ih.stepL htr

/-- The states visited by an execution form a chain from the initial to the final state
in the underlying unlabelled relation. -/
theorem isChainFromTo (hexec : lts.Execution s₁ μs s₂ ss) :
    ss.IsChainFromTo lts.UnlabelledTr s₁ s₂ := by
  induction hexec with
  | refl => exact List.isChainFromTo_singleton
  | stepL htr _ ih => exact ih.cons ⟨_, htr⟩

/-- The states visited by an execution form a chain in the underlying unlabelled relation. -/
theorem isChain (hexec : lts.Execution s₁ μs s₂ ss) :
    ss.IsChain lts.UnlabelledTr :=
  (Execution.isChainFromTo hexec).isChain

/-- Correspondence of multistep transitions and executions. -/
@[scoped grind =]
theorem _root_.Cslib.LTS.mTr_iff_execution :
    lts.MTr s₁ μs s₂ ↔ ∃ ss : List State, lts.Execution s₁ μs s₂ ss := by
  grind

/-- The composition of two executions is an execution. -/
theorem comp
    {lts : LTS State Label} {s r t : State} {μs₁ μs₂ : List Label} {ss₁ ss₂ : List State}
    (h₁ : lts.Execution s μs₁ r ss₁) (h₂ : lts.Execution r μs₂ t ss₂) :
    lts.Execution s (μs₁ ++ μs₂) t (ss₁ ++ ss₂.tail) := by
  induction h₁ with
  | refl => simpa [← h₂.head] using h₂
  | stepL htr he ih => exact (ih h₂).stepL htr

/-- The states up to `ss[n]` form an execution. -/
theorem take (he : lts.Execution s μs t ss) (n : ℕ) (hn : n < ss.length) :
    lts.Execution s (μs.take n) ss[n] (ss.take (n + 1)) := by
  induction he generalizing n with
  | refl => simpa using .refl _
  | stepL htr he ih =>
    rcases n with (_ | n)
    · simpa using .refl _
    · simpa using (ih n (by grind)).stepL htr

/-- The states from `ss[n]` onward form an execution. -/
theorem drop (he : lts.Execution s μs t ss) (n : ℕ) (hn : n < ss.length) :
    lts.Execution ss[n] (μs.drop n) t (ss.drop n) := by
  induction he generalizing n with
  | refl =>
    obtain rfl : n = 0 := by simpa using hn
    simpa using .refl _
  | stepL htr he ih =>
    rcases n with (_ | n)
    · rw [← he.start] at htr
      exact .stepL htr (ih 0 he.length_ss_pos)
    · apply ih

/-- Split an execution at an intermediate state `ss[n]`. -/
theorem split' (he : lts.Execution s μs t ss) {n : ℕ} (hn : n < ss.length) :
    lts.Execution s (μs.take n) ss[n] (ss.take (n + 1)) ∧
      lts.Execution ss[n] (μs.drop n) t (ss.drop n) := ⟨he.take n hn, he.drop n hn⟩

/-- An execution can be split at any intermediate state into two executions. -/
theorem split (he : lts.Execution s μs t ss) (n : ℕ) (hn : n ≤ μs.length) :
    lts.Execution s (μs.take n) (ss[n]'(by grind)) (ss.take (n + 1)) ∧
      lts.Execution (ss[n]'(by grind)) (μs.drop n) t (ss.drop n) := he.split' (by grind)

end Execution

end Cslib.LTS
