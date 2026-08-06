/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Cslib.Init
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Relation

/-! # Relations Across Steps

This file defines `Relation.RelatesInSteps` (and `Relation.RelatesWithinSteps`).
These are inductively defines propositions that communicate whether a relation forms a
chain of length `n` (or at most `n`) between two elements.

The theorem `RelatesInSteps.exists_isPath` allows to obtain a path along the relation of
transitively related elements and `IsPath.relatesInSteps` is the converse direction.

Another result is `Relation.reflTransGen_iff_relatesWithinSteps_of_finite`, which states that if
only `n` elements are reachable from `a`, then any element reachable from `a` is reachable in at
most `n - 1` steps.
-/

@[expose] public section

variable {α : Type*} {r : α → α → Prop} {a b c : α}

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

lemma RelatesInSteps.succ' {a b : α} : ∀ {n : ℕ}, RelatesInSteps r a b (n + 1) →
    ∃ t', r a t' ∧ RelatesInSteps r t' b n := by
  intro n h
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

/-! ## Definition of and results about paths along a relation -/

/--
`IsPath r f n` means that the first `n` steps of the sequence `f : ℕ → α` form a path along `r`,
i.e. `r (f i) (f (i + 1))` holds for every `i < n`. The values of `f` beyond index `n` are
irrelevant.
-/
def IsPath (r : α → α → Prop) (f : ℕ → α) (n : ℕ) : Prop := ∀ i < n, r (f i) (f (i + 1))

/-- A path of length `n` is in particular a path of any smaller length. -/
lemma IsPath.mono {f : ℕ → α} : Antitone (IsPath r f) := by
  intro m n hle h_path i hi
  exact h_path i (by omega)

/-- If `a` and `b` are related in `n` steps, then there is a path of length `n` from `a` to `b`. -/
theorem RelatesInSteps.exists_isPath {a b : α} {n : ℕ} (h : RelatesInSteps r a b n) :
    ∃ f : ℕ → α, f 0 = a ∧ f n = b ∧ IsPath r f n := by
  induction h with
  | refl => exact ⟨fun _ => a, rfl, rfl, by simp [IsPath]⟩
  | tail t' t'' m _ hstep ih =>
    obtain ⟨f, hf0, hfm, hfstep⟩ := ih
    refine ⟨fun i => if i ≤ m then f i else t'', by simpa using hf0, by simp, fun i hi => ?_⟩
    rcases Nat.lt_or_ge i m with h' | h'
    · simpa [h'.le, h'] using hfstep i h'
    · have : i = m := by lia
      subst this
      simpa [hfm] using hstep

/-- Any two positions along a path are related in as many steps as their distance. -/
theorem IsPath.relatesInSteps {f : ℕ → α} {n : ℕ} (hf : IsPath r f n) (p k : ℕ) (hpk : p + k ≤ n) :
    RelatesInSteps r (f p) (f (p + k)) k := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    refine .tail _ (f (p + k)) _ k (ih (by lia)) ?_
    have := hf (p + k) (by lia)
    rwa [← Nat.add_assoc]

/-- A path that visits the same element at two different positions can be shortened by splicing
out the loop in between. -/
theorem IsPath.relatesInSteps_of_eq {f : ℕ → α} {n i j : ℕ}
    (hf : IsPath r f n)
    (hij : i < j)
    (hjn : j ≤ n)
    (heq : f i = f j) :
    RelatesInSteps r (f 0) (f n) (i + (n - j)) := by
  have h₁ : RelatesInSteps r (f 0) (f j) i := by grind [hf.relatesInSteps 0 i (by lia)]
  have h₂ : RelatesInSteps r (f j) (f n) (n - j) := by grind [hf.relatesInSteps j (n - j) (by lia)]
  exact h₁.trans h₂

/-- Every element visited by a path is reachable from its starting point. -/
theorem IsPath.reflTransGen {f : ℕ → α} {n : ℕ} (hf : IsPath r f n) {i : ℕ} (hi : i ≤ n) :
    ReflTransGen r (f 0) (f i) := by
  have := (hf.relatesInSteps 0 i (by lia)).reflTransGen
  rwa [Nat.zero_add] at this

/-- A path visiting more positions than there are elements reachable from its starting point must
visit some element twice. -/
theorem IsPath.exists_eq_of_ncard_le {f : ℕ → α} {n : ℕ}
    (hf : IsPath r f n)
    (hfin : Set.Finite (ReflTransGen r (f 0)))
    (hn : Set.ncard (ReflTransGen r (f 0)) ≤ n) :
    ∃ i j, i < j ∧ j ≤ n ∧ f i = f j := by
  have hmaps : ∀ i ∈ Finset.range (n + 1), f i ∈ hfin.toFinset := fun i hi =>
    hfin.mem_toFinset.mpr (hf.reflTransGen (by simpa [Nat.lt_succ_iff] using hi))
  have hcard : hfin.toFinset.card < (Finset.range (n + 1)).card := by
    grind [Set.ncard_eq_toFinset_card _ hfin]
  obtain ⟨i, hi, j, hj, hij, hfij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi hj
  rcases Nat.lt_or_ge i j with hlt | hge
  · exact ⟨i, j, hlt, hj, hfij⟩
  · exact ⟨j, i, by lia, hi, hfij.symm⟩

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
  obtain ⟨m, hm, hevals⟩ := h
  have : m = 0 := Nat.le_zero.mp hm
  subst this
  exact RelatesInSteps.zero hevals

@[simp]
lemma RelatesWithinSteps.zero_iff {a b : α} : RelatesWithinSteps r a b 0 ↔ a = b := by
  constructor
  · exact RelatesWithinSteps.zero
  · intro h
    subst h
    exact RelatesWithinSteps.refl a

/-- Transitivity of `RelatesWithinSteps` in the sum of the step bounds. -/
@[trans]
lemma RelatesWithinSteps.trans {a b c : α} {n₁ n₂ : ℕ}
    (h₁ : RelatesWithinSteps r a b n₁) (h₂ : RelatesWithinSteps r b c n₂) :
    RelatesWithinSteps r a c (n₁ + n₂) := by
  obtain ⟨m₁, hm₁, hevals₁⟩ := h₁
  obtain ⟨m₂, hm₂, hevals₂⟩ := h₂
  use m₁ + m₂
  constructor
  · lia
  · exact RelatesInSteps.trans hevals₁ hevals₂

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

/-! ### Reachability under a bound on the number of reachable elements -/

/-- An `r`-chain from `a` to `b` visiting at least as many positions as there are elements
(transitively) related to `a` must visit some element twice, and can therefore be shortened. -/
theorem RelatesInSteps.exists_lt_of_ncard_le {b : α} {n : ℕ}
    (hfin : Set.Finite (ReflTransGen r a))
    (h : RelatesInSteps r a b n)
    (hn : Set.ncard (ReflTransGen r a) ≤ n) :
    ∃ m < n, RelatesInSteps r a b m := by
  obtain ⟨f, rfl, rfl, hpath⟩ := h.exists_isPath
  obtain ⟨i, j, hij, hjn, heq⟩ := hpath.exists_eq_of_ncard_le hfin hn
  exact ⟨i + (n - j), by lia, hpath.relatesInSteps_of_eq hij hjn heq⟩

/-- If only a finite number of elements are (transitively) related to `a`, then any such element
is related to `a` in at most `k - 1` steps, where `k` is the cardinality of that set. -/
theorem reflTransGen_iff_relatesWithinSteps_of_finite {b : α}
    (hfin : Set.Finite (ReflTransGen r a)) :
    ReflTransGen r a b ↔ RelatesWithinSteps r a b (Set.ncard (ReflTransGen r a) - 1) := by
  classical
  simp only [RelatesWithinSteps]
  constructor
  · intro h_reach
    have hex : ∃ n, RelatesInSteps r a b n := ReflTransGen.relatesInSteps h_reach
    -- A chain of minimal length cannot be shortened, so it is short enough.
    have hmin : ∀ m < Nat.find hex, ¬ RelatesInSteps r a b m := fun m hm => Nat.find_min hex hm
    grind [RelatesInSteps.exists_lt_of_ncard_le]
  · grind [RelatesInSteps.reflTransGen]

end Relation
