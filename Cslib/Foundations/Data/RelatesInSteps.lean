/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Cslib.Init
public import Cslib.Foundations.Data.List.IsChainFromTo
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Relation

/-! # Relations Across Steps

This file defines `Relation.RelatesInSteps` (and `Relation.RelatesWithinSteps`).
These are inductively defined propositions that communicate whether a relation forms a
chain of length `n` (or at most `n`) between two elements.

The lemma `RelatesInSteps.exists_isChainFromTo` allows to obtain a chain
(`List.IsChainFromTo`) of related elements that witness the reachability, and
`List.IsChainFromTo.relatesInSteps` is the converse direction.
`Relation.relatesInSteps_iff_exists_isChainFromTo` combines both.

Another result is `Relation.ReflTransGen.relatesInSteps_lt_encard`, which states that any element
reachable from `a` is reachable in fewer steps than there are elements reachable from `a`.
-/

@[expose] public section

variable {α : Type*} {r : α → α → Prop} {a b c : α} {n m : ℕ}

namespace Relation

/--
A relation `r` relates two elements of `α` in `n` steps
if there is a chain of `n` pairs `(t_i, t_{i+1})` such that `r t_i t_{i+1}` for each `i`,
starting from the first element and ending at the second.
-/
inductive RelatesInSteps (r : α → α → Prop) : α → α → ℕ → Prop
  | refl (a : α) : RelatesInSteps r a a 0
  | tail (t t' t'' : α) (n : ℕ) (h₁ : RelatesInSteps r t t' n) (h₂ : r t' t'') :
      RelatesInSteps r t t'' (n + 1)

theorem RelatesInSteps.reflTransGen (h : RelatesInSteps r a b n) : ReflTransGen r a b := by
  induction h with
  | refl => rfl
  | tail _ _ _ _ h ih => exact .tail ih h

/-- If `b` is reachable from `a` via `r`, then they relate to each other for some number
of steps. -/
theorem ReflTransGen.relatesInSteps (h : ReflTransGen r a b) : ∃ n, RelatesInSteps r a b n := by
  induction h with
  | refl => exact ⟨0, .refl a⟩
  | tail _ _ ih =>
    obtain ⟨n, _⟩ := ih
    exact ⟨n + 1, by grind [RelatesInSteps]⟩

lemma RelatesInSteps.single {a b : α} (h : r a b) : RelatesInSteps r a b 1 :=
  tail a a b 0 (refl a) h

theorem RelatesInSteps.head (t t' t'' : α) (n : ℕ) (h₁ : r t t')
    (h₂ : RelatesInSteps r t' t'' n) : RelatesInSteps r t t'' (n+1) := by
  induction h₂ with
  | refl =>
    exact single h₁
  | tail _ _ n _ hcd hac =>
    exact tail _ _ _ (n + 1) hac hcd

@[elab_as_elim]
theorem RelatesInSteps.head_induction_on {motive : ∀ (a : α) (n : ℕ), RelatesInSteps r a b n → Prop}
    {a : α} {n : ℕ} (h : RelatesInSteps r a b n) (hrefl : motive b 0 (.refl b))
    (hhead : ∀ {a c n} (h' : r a c) (h : RelatesInSteps r c b n),
      motive c n h → motive a (n + 1) (h.head a c b n h')) :
    motive a n h := by
  induction h with
  | refl => exact hrefl
  | tail t' b' m hstep hrt'b' hstep_ih =>
    apply hstep_ih
    · exact hhead hrt'b' _ hrefl
    · exact fun h1 h2 ↦ hhead h1 (.tail _ t' b' _ h2 hrt'b')

lemma RelatesInSteps.zero {a b : α} (h : RelatesInSteps r a b 0) : a = b := by
  cases h
  rfl

@[simp]
lemma RelatesInSteps.zero_iff {a b : α} : RelatesInSteps r a b 0 ↔ a = b := by
  constructor
  · exact RelatesInSteps.zero
  · intro rfl
    exact RelatesInSteps.refl a

lemma RelatesInSteps.trans {a b c : α} {n m : ℕ}
    (h₁ : RelatesInSteps r a b n) (h₂ : RelatesInSteps r b c m) :
    RelatesInSteps r a c (n + m) := by
  induction h₂ generalizing a n with
  | refl => simp [h₁]
  | tail t' t'' k hsteps hstep ih =>
    rw [← Nat.add_assoc]
    exact .tail _ t' t'' (n + k) (ih h₁) hstep

lemma RelatesInSteps.succ {n : ℕ} (h : RelatesInSteps r a b (n + 1)) :
    ∃ t', RelatesInSteps r a t' n ∧ r t' b := by
  cases h with
  | tail t' _ _ hsteps hstep => exact ⟨t', hsteps, hstep⟩

lemma RelatesInSteps.succ_iff {a b : α} {n : ℕ} :
    RelatesInSteps r a b (n + 1) ↔ ∃ t', RelatesInSteps r a t' n ∧ r t' b := by
  constructor
  · exact RelatesInSteps.succ
  · rintro ⟨t', h_steps, h_red⟩
    exact .tail _ t' b n h_steps h_red

lemma RelatesInSteps.succ' {a b : α} {n : ℕ} (h : RelatesInSteps r a b (n + 1)) :
    ∃ t', r a t' ∧ RelatesInSteps r t' b n := by
  obtain ⟨t', hsteps, hstep⟩ := succ h
  cases n with
  | zero =>
    rw [zero_iff] at hsteps
    subst hsteps
    exact ⟨b, hstep, .refl _⟩
  | succ k' =>
    obtain ⟨t''', h_red''', h_steps'''⟩ := succ' hsteps
    exact ⟨t''', h_red''', .tail _ _ b k' h_steps''' hstep⟩

lemma RelatesInSteps.succ'_iff {a b : α} {n : ℕ} :
    RelatesInSteps r a b (n + 1) ↔ ∃ t', r a t' ∧ RelatesInSteps r t' b n := by
  constructor
  · exact succ'
  · rintro ⟨t', h_red, h_steps⟩
    exact h_steps.head a t' b n h_red

/--
If `h : α → ℕ` increases by at most 1 on each step of `r`,
then the value of `h` at the output is at most `h` at the input plus the number of steps.
-/
lemma RelatesInSteps.apply_le_apply_add {a b : α} {m : ℕ} (hevals : RelatesInSteps r a b m)
    (h : α → ℕ) (h_step : ∀ a b, r a b → h b ≤ h a + 1) :
    h b ≤ h a + m := by
  induction hevals with
  | refl => simp
  | tail t' t'' k _ hstep ih =>
    have h_step' := h_step t' t'' hstep
    lia

/--
If `g` is a homomorphism from `r` to `r'` (i.e., it preserves the reduction relation),
then `RelatesInSteps` is preserved under `g`.
-/
lemma RelatesInSteps.map {α α' : Type*}
    {r : α → α → Prop} {r' : α' → α' → Prop}
    (g : α → α') (hg : ∀ a b, r a b → r' (g a) (g b))
    {a b : α} {n : ℕ} (h : RelatesInSteps r a b n) :
    RelatesInSteps r' (g a) (g b) n := by
  induction h with
  | refl => exact RelatesInSteps.refl (g _)
  | tail t' t'' m _ hstep ih =>
    exact .tail (g _) (g t') (g t'') m ih (hg t' t'' hstep)

/-! ## Translating between `RelatesInSteps` and chains (`List.IsChainFromTo`) -/

/-- If `b` is related to `a` via `r` in `n` steps, then there is an `r`-chain of `n + 1` elements
starting at `a` and ending at `b`.
This is similar to `List.exists_isChain_ne_nil_of_relationReflTransGen`, but also provides
a length guarantee. -/
lemma RelatesInSteps.exists_isChainFromTo {a b : α} {n : ℕ} (h : RelatesInSteps r a b n) :
    ∃ chain : List α, chain.IsChainFromTo r a b ∧ chain.length = n + 1 := by
  induction h using RelatesInSteps.head_induction_on with
  | hrefl => exact ⟨[b], List.isChainFromTo_singleton, rfl⟩
  | @hhead a c n h' h ih =>
    obtain ⟨l, hchain, hlen⟩ := ih
    use a :: l, hchain.cons h'
    simpa

/-- Any two elements along an `r`-chain are related in as many steps as their distance in the
chain. -/
lemma _root_.List.IsChain.relatesInSteps_getElem {chain : List α} (hc : chain.IsChain r)
    (i k : ℕ) (hik : i + k < chain.length) :
    RelatesInSteps r chain[i] chain[i + k] k := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    apply RelatesInSteps.tail _ (chain[i + k]) _ k (ih (by lia))
    apply List.IsChain.getElem hc

/-- If there is an `r`-chain of `n + 1` elements from `a` to `b`, then `a` and `b` are related
to each other in `n` steps. -/
lemma _root_.List.IsChainFromTo.relatesInSteps {chain : List α} {n : ℕ}
    (hc : chain.IsChainFromTo r a b) (hlen : chain.length = n + 1) :
    RelatesInSteps r a b n := by
  have hrel := _root_.List.IsChain.relatesInSteps_getElem hc.isChain 0 n (by lia)
  have hlast : chain[n]'(by lia) = b := by simpa [hlen] using hc.getElem_length_sub_one
  simpa [hc.getElem_zero, hlast] using hrel

/-- `a` and `b` are related in `n` steps exactly when there is an `r`-chain of `n + 1` elements
from `a` to `b`. -/
lemma relatesInSteps_iff_exists_isChainFromTo :
    RelatesInSteps r a b n ↔ ∃ chain : List α, chain.IsChainFromTo r a b ∧ chain.length = n + 1 :=
  ⟨RelatesInSteps.exists_isChainFromTo, fun ⟨_, hc, hlen⟩ => hc.relatesInSteps hlen⟩

/-! ## RelatesWithinSteps - only requires an upper bound on the number of steps -/

/--
`RelatesWithinSteps` is a variant of `RelatesInSteps` that allows for a loose bound.
It states that `a` relates to `b` in *at most* `n` steps.
-/
def RelatesWithinSteps (r : α → α → Prop) (a b : α) (n : ℕ) : Prop :=
  ∃ m ≤ n, RelatesInSteps r a b m

/-- `RelatesInSteps` implies `RelatesWithinSteps` with the same bound. -/
lemma RelatesWithinSteps.of_relatesInSteps {a b : α} {n : ℕ} (h : RelatesInSteps r a b n) :
    RelatesWithinSteps r a b n :=
  ⟨n, Nat.le_refl n, h⟩

lemma RelatesWithinSteps.refl (a : α) : RelatesWithinSteps r a a 0 :=
  RelatesWithinSteps.of_relatesInSteps (RelatesInSteps.refl a)

lemma RelatesWithinSteps.single {a b : α} (h : r a b) : RelatesWithinSteps r a b 1 :=
  RelatesWithinSteps.of_relatesInSteps (RelatesInSteps.single h)

lemma RelatesWithinSteps.zero {a b : α} (h : RelatesWithinSteps r a b 0) : a = b := by
  obtain ⟨_, hm, hevals⟩ := h
  simp_all

@[simp]
lemma RelatesWithinSteps.zero_iff {a b : α} : RelatesWithinSteps r a b 0 ↔ a = b := by
  constructor
  · exact RelatesWithinSteps.zero
  · rintro rfl
    exact RelatesWithinSteps.refl a

/-- Transitivity of `RelatesWithinSteps` in the sum of the step bounds. -/
@[trans]
lemma RelatesWithinSteps.trans {a b c : α} {n₁ n₂ : ℕ}
    (h₁ : RelatesWithinSteps r a b n₁) (h₂ : RelatesWithinSteps r b c n₂) :
    RelatesWithinSteps r a c (n₁ + n₂) := by
  obtain ⟨m₁, hm₁, hevals₁⟩ := h₁
  obtain ⟨m₂, hm₂, hevals₂⟩ := h₂
  exact ⟨m₁ + m₂, by lia, hevals₁.trans hevals₂⟩

/-- If two elements `a` and `b` are related in at most `n₁` steps in the relation `r` and
`n₁ ≤ n₂`, then they are also related in at most `n₂` steps. -/
lemma RelatesWithinSteps.mono {a b : α} : Monotone (RelatesWithinSteps r a b ·) := by
  intro n₁ n₂ hn ⟨m, hm, hevals⟩
  exact ⟨m, Nat.le_trans hm hn, hevals⟩

/-- If `h : α → ℕ` increases by at most 1 on each step of `r`,
then the value of `h` at the output is at most `h` at the input plus the step bound. -/
lemma RelatesWithinSteps.apply_le_apply_add {a b : α} {m : ℕ}
    (hevals : RelatesWithinSteps r a b m)
    (h : α → ℕ)
    (h_step : ∀ a b, r a b → h b ≤ h a + 1) :
    h b ≤ h a + m := by
  obtain ⟨m, hm, hevals_m⟩ := hevals
  have := RelatesInSteps.apply_le_apply_add hevals_m h h_step
  lia

/--
If `g` is a homomorphism from `r` to `r'` (i.e., it preserves the reduction relation),
then `RelatesWithinSteps` is preserved under `g`.
-/
lemma RelatesWithinSteps.map {α α' : Type*} {r : α → α → Prop} {r' : α' → α' → Prop}
    (g : α → α') (hg : ∀ a b, r a b → r' (g a) (g b))
    {a b : α} {n : ℕ} (h : RelatesWithinSteps r a b n) :
    RelatesWithinSteps r' (g a) (g b) n := by
  obtain ⟨m, hm, hevals⟩ := h
  exact ⟨m, hm, RelatesInSteps.map g hg hevals⟩

/-! ## Reachability under a bound on the number of reachable elements -/

/-- A more precise version of `ReflTransGen.relatesInSteps`: if `b` is reachable from `a`, then it
is related to `a` in fewer steps than there are elements reachable from `a`.
Note that this cardinality is an `ℕ∞`, and if it is infinite, no bound on the number of steps
is stated. -/
theorem ReflTransGen.relatesInSteps_lt_encard {b : α} (h : ReflTransGen r a b) :
    ∃ n, RelatesInSteps r a b n ∧ (n : ℕ∞) < {x | ReflTransGen r a x}.encard := by
  classical
  -- Take any chain from `a` to `b` and remove its duplicates.
  obtain ⟨n₀, hn₀⟩ := h.relatesInSteps
  obtain ⟨chain₀, hc₀, -⟩ := hn₀.exists_isChainFromTo
  obtain ⟨chain, hc, h_nodup⟩ := hc₀.exists_nodup
  obtain ⟨n, hlen⟩ : ∃ n, chain.length = n + 1 := ⟨chain.length - 1, by have := hc.length_pos; lia⟩
  refine ⟨n, hc.relatesInSteps hlen, ?_⟩
  -- All elements of the chain are reachable from `a`, and they are pairwise distinct,
  -- so the chain has at most as many elements as there are reachable elements.
  have hsub : {x | x ∈ chain} ⊆ {x | ReflTransGen r a x} := fun _ hx => hc.reflTransGen_of_mem hx
  have h_le : (chain.length : ℕ∞) ≤ {x | ReflTransGen r a x}.encard := by
    rw [← List.coe_toFinset] at hsub
    have := Set.encard_le_encard hsub
    rwa [Set.encard_coe_eq_coe_finsetCard, List.toFinset_card_of_nodup h_nodup] at this
  -- The chain has one more element than the number of steps.
  exact lt_of_lt_of_le (by rw [hlen]; exact_mod_cast Nat.lt_succ_self n) h_le

end Relation
