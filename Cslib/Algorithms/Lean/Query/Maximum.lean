/-
Copyright (c) 2026 geopi1. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: geopi1
-/
module

public import Cslib.Algorithms.Lean.Query.Bounds
public import Cslib.Algorithms.Lean.Query.Sort.LEQuery
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.Fintype.EquivFin

/-! # Finding the maximum with comparison queries

Finding the maximum of `n` elements with comparisons needs exactly `n - 1` comparisons.

* `maximum` is the linear scan as a `FreeM (LEQuery α)` program. `maximum_isMaxFinder` proves it
  correct and `countQueries_maximum` proves it makes exactly `n - 1` queries for every oracle.
* `IsMaxFinder.length_sub_one_le_countQueries` proves that *every* correct comparison-based
  maximum-finding program makes at least `n - 1` queries on *every* list of `n` distinct elements,
  under *every* total order. `IsMaxFinder.lowerBound` restates this as a `Query.LowerBound`.

The lower bound is the classical adversary argument: every element other than the reported
maximum must lose some comparison, since otherwise moving it to the top of the order does not
change any answer (so the program reports the same, now wrong, maximum). Every comparison has a
single loser.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, C. Stein, *Introduction to Algorithms*][Cormen2009],
  Section 9.1.
-/

open Cslib Cslib.Query

public section

namespace Cslib.Query

variable {α : Type}

/-! ## Specification -/

/-- `find` is a correct comparison-based maximum finder: on a nonempty list it returns some
element of the list, and when the oracle implements a total preorder `r` that element is an
`r`-maximum of the list. -/
structure IsMaxFinder (find : List α → FreeM (LEQuery α) (Option α)) : Prop where
  /-- On a nonempty input, the program returns some element. -/
  isSome : ∀ (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι),
    xs ≠ [] → ((find xs).eval oracle).isSome
  /-- The returned element belongs to the input, for any oracle. -/
  mem : ∀ (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι) (m : α),
    (find xs).eval oracle = some m → m ∈ xs
  /-- The returned element is a maximum, when the oracle implements a total preorder. -/
  le_of_mem : ∀ (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (_ : ∀ a b, oracle (.le a b) = decide (r a b)) (m : α),
    (find xs).eval oracle = some m → ∀ y ∈ xs, r y m

/-! ## The linear scan -/

/-- Scan `ys` keeping the current candidate `m`, replacing it by `y` whenever `m ≤ y`. -/
def maximumAux (m : α) : List α → FreeM (LEQuery α) α
  | [] => pure m
  | y :: ys => do
    if ← LEQuery.ask m y then maximumAux y ys else maximumAux m ys

/-- The maximum of a list via a linear scan, or `none` for the empty list. -/
def maximum : List α → FreeM (LEQuery α) (Option α)
  | [] => pure none
  | x :: xs => some <$> maximumAux x xs

@[simp] theorem eval_maximumAux (oracle : {ι : Type} → LEQuery α ι → ι) (m : α) (ys : List α) :
    (maximumAux m ys).eval oracle =
      ys.foldl (fun m y => if oracle (.le m y) then y else m) m := by
  induction ys generalizing m with
  | nil => rfl
  | cons y ys ih => by_cases h : oracle (.le m y) <;> simp [maximumAux, h, ih]

@[simp] theorem countQueries_maximumAux (oracle : {ι : Type} → LEQuery α ι → ι) (m : α)
    (ys : List α) : (maximumAux m ys).countQueries oracle = ys.length := by
  induction ys generalizing m with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : oracle (.le m y) <;> simp [maximumAux, h, ih] <;> omega

@[simp] theorem eval_maximum_nil (oracle : {ι : Type} → LEQuery α ι → ι) :
    (maximum ([] : List α)).eval oracle = none := by
  simp [maximum]

@[simp] theorem eval_maximum_cons (oracle : {ι : Type} → LEQuery α ι → ι) (x : α)
    (xs : List α) :
    (maximum (x :: xs)).eval oracle =
      some (xs.foldl (fun m y => if oracle (.le m y) then y else m) x) := by
  simp [maximum]

/-- The linear scan makes exactly `n - 1` queries, whatever the oracle. -/
@[simp] theorem countQueries_maximum (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (maximum xs).countQueries oracle = xs.length - 1 := by
  cases xs <;> simp [maximum]

private theorem foldl_mem (f : α → α → Bool) (m : α) (ys : List α) :
    ys.foldl (fun m y => if f m y then y else m) m ∈ m :: ys := by
  induction ys generalizing m with
  | nil => simp
  | cons y ys ih =>
    by_cases h : f m y <;> simp only [List.foldl_cons, h, ↓reduceIte, Bool.false_eq_true]
    · exact List.mem_cons_of_mem _ (ih y)
    · rcases List.mem_cons.mp (ih m) with h' | h'
      · simp [h']
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')

private theorem le_foldl (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (m : α) (ys : List α) :
    ∀ y ∈ m :: ys, r y (ys.foldl (fun m y => if decide (r m y) then y else m) m) := by
  induction ys generalizing m with
  | nil => simpa using refl_of r m
  | cons y ys ih =>
    by_cases h : r m y
    · simp only [List.foldl_cons, h, decide_true, ↓reduceIte]
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact _root_.trans h (ih y y List.mem_cons_self)
      · exact ih y z hz
    · have hym : r y m := (total_of r m y).resolve_left h
      simp only [List.foldl_cons, h, decide_false, Bool.false_eq_true, ↓reduceIte]
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ih z z List.mem_cons_self
      rcases List.mem_cons.mp hz with rfl | hz
      · exact _root_.trans hym (ih m m List.mem_cons_self)
      · exact ih m z (List.mem_cons_of_mem _ hz)

theorem maximum_isMaxFinder : IsMaxFinder (maximum (α := α)) where
  isSome xs oracle h := by
    cases xs with
    | nil => exact absurd rfl h
    | cons x xs => simp
  mem xs oracle m h := by
    cases xs with
    | nil => simp at h
    | cons x xs =>
      simp only [eval_maximum_cons, Option.some.injEq] at h
      exact h ▸ foldl_mem _ x xs
  le_of_mem xs oracle r _ _ _ horacle m h := by
    cases xs with
    | nil => simp at h
    | cons x xs =>
      simp only [eval_maximum_cons, horacle, Option.some.injEq] at h
      exact h ▸ le_foldl r x xs

/-- The linear scan uses at most `n - 1` queries on inputs of length `n`. -/
theorem maximum_upperBound : UpperBound (maximum (α := α)) List.length (· - 1) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.sub_le_sub_right h 1) fun oracle xs =>
    (countQueries_maximum oracle xs).le

/-! ## The comparisons asked along a run -/

/-- The comparisons `(a, b)` asked by `p` along the path determined by `oracle`, in order. -/
def comparisons {β : Type} (oracle : {ι : Type} → LEQuery α ι → ι) :
    FreeM (LEQuery α) β → List (α × α)
  | .pure _ => []
  | .liftBind (.le a b) cont => (a, b) :: comparisons oracle (cont (oracle (.le a b)))

@[simp] theorem length_comparisons {β : Type} (oracle : {ι : Type} → LEQuery α ι → ι)
    (p : FreeM (LEQuery α) β) : (comparisons oracle p).length = p.countQueries oracle := by
  induction p with
  | pure => rfl
  | lift_bind op cont ih =>
    cases op with
    | le a b =>
      change (comparisons oracle (cont (oracle (.le a b)))).length + 1 =
        1 + (cont (oracle (.le a b))).countQueries oracle
      rw [ih, Nat.add_comm]

/-- A run only depends on the answers to the comparisons it actually asks: two oracles that
agree on them lead to the same result. -/
theorem eval_eq_of_comparisons {β : Type} (o₁ o₂ : {ι : Type} → LEQuery α ι → ι)
    (p : FreeM (LEQuery α) β)
    (h : ∀ q ∈ comparisons o₁ p, o₁ (.le q.1 q.2) = o₂ (.le q.1 q.2)) :
    p.eval o₁ = p.eval o₂ := by
  induction p with
  | pure => rfl
  | lift_bind op cont ih =>
    cases op with
    | le a b =>
      have hab : o₁ (.le a b) = o₂ (.le a b) := h (a, b) List.mem_cons_self
      change (cont (o₁ (.le a b))).eval o₁ = (cont (o₂ (.le a b))).eval o₂
      rw [← hab]
      exact ih _ fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- The loser of the comparison `(a, b)`: `a` if the oracle answers `a ≤ b`, and `b` otherwise. -/
def loser (oracle : {ι : Type} → LEQuery α ι → ι) (q : α × α) : α :=
  if oracle (.le q.1 q.2) then q.1 else q.2

/-! ## The adversary lower bound -/

/-- `r` modified so that `y` is above every element. -/
private def raise (r : α → α → Prop) (y : α) (a b : α) : Prop :=
  b = y ∨ (a ≠ y ∧ r a b)

private instance (r : α → α → Prop) [Std.Total r] (y : α) : Std.Total (raise r y) where
  total a b := by
    by_cases ha : a = y
    · exact Or.inr (Or.inl ha)
    by_cases hb : b = y
    · exact Or.inl (Or.inl hb)
    rcases total_of r a b with h | h
    · exact Or.inl (Or.inr ⟨ha, h⟩)
    · exact Or.inr (Or.inr ⟨hb, h⟩)

private instance (r : α → α → Prop) [IsTrans α r] (y : α) : IsTrans α (raise r y) where
  trans a b c hab hbc := by
    rcases hbc with hc | ⟨hb, hbc⟩
    · exact Or.inl hc
    rcases hab with rfl | ⟨ha, hab⟩
    · exact absurd rfl hb
    · exact Or.inr ⟨ha, _root_.trans hab hbc⟩

/-- In a run of a correct maximum finder under a total preorder, every element of the input other
than the reported maximum loses at least one comparison. -/
theorem IsMaxFinder.exists_loser {find : List α → FreeM (LEQuery α) (Option α)}
    (hfind : IsMaxFinder find) (xs : List α) (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) {m : α}
    (hm : (find xs).eval oracle = some m) {y : α} (hy : y ∈ xs) (hym : y ≠ m) :
    ∃ q ∈ comparisons oracle (find xs), loser oracle q = y := by
  classical
  by_contra! hlose
  -- The oracle for `r` with `y` raised to the top agrees with `oracle` on every comparison asked.
  let oracle' : {ι : Type} → LEQuery α ι → ι := LEQuery.oracleOf fun a b => decide (raise r y a b)
  have hagree : ∀ q ∈ comparisons oracle (find xs),
      oracle (.le q.1 q.2) = oracle' (.le q.1 q.2) := by
    rintro ⟨a, b⟩ hq
    have hl := hlose (a, b) hq
    simp only [loser, horacle] at hl
    simp only [horacle, oracle', LEQuery.oracleOf_le, raise]
    by_cases hb : b = y
    · subst hb
      by_cases hab : r a b
      · simp [hab]
      · simp [hab] at hl
    · by_cases ha : a = y
      · subst ha
        by_cases hab : r a b
        · simp [hab] at hl
        · simp [hab, hb]
      · simp [ha, hb]
  have hm' : (find xs).eval oracle' = some m := by
    rw [← eval_eq_of_comparisons _ _ _ hagree, hm]
  have := hfind.le_of_mem xs oracle' (raise r y) (fun _ _ => rfl) m hm' y hy
  rcases this with h | ⟨h, _⟩
  · exact hym h.symm
  · exact h rfl

/-- **Lower bound for finding the maximum.** Any correct comparison-based maximum finder makes at
least `n - 1` comparisons on any list of `n` distinct elements, under any total preorder. -/
theorem IsMaxFinder.length_sub_one_le_countQueries
    {find : List α → FreeM (LEQuery α) (Option α)} (hfind : IsMaxFinder find)
    (xs : List α) (hxs : xs.Nodup) (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) :
    xs.length - 1 ≤ (find xs).countQueries oracle := by
  classical
  by_cases hne : xs = []
  · simp [hne]
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (hfind.isSome xs oracle hne)
  have hsub : xs.toFinset.erase m ⊆
      ((comparisons oracle (find xs)).map (loser oracle)).toFinset := by
    intro y hy
    obtain ⟨hym, hy⟩ := Finset.mem_erase.mp hy
    obtain ⟨q, hq, hl⟩ :=
      hfind.exists_loser xs oracle r horacle hm (List.mem_toFinset.mp hy) hym
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, hq, hl⟩)
  calc xs.length - 1
      = xs.toFinset.card - 1 := by rw [List.toFinset_card_of_nodup hxs]
    _ ≤ (xs.toFinset.erase m).card := Finset.pred_card_le_card_erase
    _ ≤ ((comparisons oracle (find xs)).map (loser oracle)).toFinset.card :=
        Finset.card_le_card hsub
    _ ≤ ((comparisons oracle (find xs)).map (loser oracle)).length := List.toFinset_card_le _
    _ = (find xs).countQueries oracle := by simp

/-- Any correct maximum finder on an infinite linearly ordered type has query complexity at least
`n - 1` on inputs of size `n`. -/
theorem IsMaxFinder.lowerBound [LinearOrder α] [Infinite α]
    {find : List α → FreeM (LEQuery α) (Option α)} (hfind : IsMaxFinder find) :
    LowerBound find List.length (· - 1) := by
  intro n
  let xs := (List.range n).map (Infinite.natEmbedding α)
  have hxs : xs.Nodup := (List.nodup_range).map (Infinite.natEmbedding α).injective
  let oracle : {ι : Type} → LEQuery α ι → ι := LEQuery.oracleOf fun a b => decide (a ≤ b)
  refine ⟨xs, by simp [xs], oracle, ?_⟩
  have := hfind.length_sub_one_le_countQueries xs hxs oracle (· ≤ ·) fun _ _ => rfl
  simpa [xs] using this

/-- The linear scan is optimal: it makes exactly `n - 1` queries on every input of length `n`,
and no correct maximum finder can do better on lists of distinct elements. -/
theorem maximum_optimal {find : List α → FreeM (LEQuery α) (Option α)} (hfind : IsMaxFinder find)
    (xs : List α) (hxs : xs.Nodup) (oracle : {ι : Type} → LEQuery α ι → ι)
    (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) :
    (maximum xs).countQueries oracle ≤ (find xs).countQueries oracle := by
  rw [countQueries_maximum]
  exact hfind.length_sub_one_le_countQueries xs hxs oracle r horacle

end Cslib.Query
