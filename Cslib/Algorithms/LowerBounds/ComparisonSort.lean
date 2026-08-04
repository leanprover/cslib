/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Foundations.Control.Monad.Free
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Log

/-!
# The comparison sort lower bound

This file proves the `Ω(n log n)` worst-case lower bound on comparison sorting.

A program `P : FreeM (SortOps α) β` is a binary decision tree: `pure b` is a leaf, and
`(FreeM.lift (SortOps.cmpLE x y)).bind cont` is a node with children `cont true` and
`cont false`. `run P le` and `cost P le` give the result and the number of comparisons
of `P` under a comparator `le`; they are the two projections of the canonical
interpretation (`FreeM.liftM`) of `P` into `TimeM ℕ`, and so satisfy `run_bind` and
`cost_bind`. `worstTime P` is the worst case of `cost` over the orders `permLE σ`
induced by permutations `σ` of `Fin n`.

By structural induction on `P`, `card_image_run_le_two_pow` bounds the number of
distinct results over any finite family of comparators by `2 ^ c`, where `c` is the
worst-case number of comparisons over that family. A program that sorts under every
`permLE σ` has `n !` distinct outputs, so `n ! ≤ 2 ^ worstTime P`.

## Main results

- `card_image_run_le_two_pow`: a program attains at most `2 ^ c` distinct results over a
  finite comparator family with worst-case cost `c`.
- `factorial_le_two_pow_worstTime`: a program sorting all hidden orders on `Fin n`
  satisfies `n ! ≤ 2 ^ worstTime P`.
- `log_factorial_le_worstTime`: `Nat.log 2 (n !) ≤ worstTime P`.
- `cmpSort_lower_bound`: `n / 2 * Nat.log 2 (n / 2) ≤ worstTime P`.

## Tags

sorting, lower bound, decision tree, query complexity, free monad
-/

@[expose] public section

namespace Cslib.Algorithms

open scoped Nat

/--
A query type for comparison-based sorting, with a single query that compares two elements.
-/
inductive SortOps.{u} (α : Type u) : Type → Type _ where
  /-- `cmpLE x y` is intended to return `true` if `x ≤ y` and `false` otherwise.
  The specific order relation depends on the comparator the program is run against. -/
  | cmpLE (x : α) (y : α) : SortOps α Bool

variable {α : Type u} {β γ : Type}

open Cslib.Algorithms.Lean in
/-- Interpret the comparison query into `TimeM ℕ`: answer with `le x y`, at cost `1`. -/
def sortHandler (le : α → α → Bool) : {ι : Type} → SortOps α ι → TimeM ℕ ι
  | _, .cmpLE x y => ⟨le x y, 1⟩

/-- The result of running a comparison program against a comparator. -/
def run (P : FreeM (SortOps α) β) (le : α → α → Bool) : β :=
  (P.liftM (sortHandler le)).ret

/-- The number of comparisons a program performs against a comparator. -/
def cost (P : FreeM (SortOps α) β) (le : α → α → Bool) : ℕ :=
  (P.liftM (sortHandler le)).time

@[simp, grind =]
lemma run_pure (b : β) (le : α → α → Bool) : run (pure b) le = b := rfl

@[simp, grind =]
lemma run_lift (x y : α) (le : α → α → Bool) :
    run (FreeM.lift (SortOps.cmpLE x y)) le = le x y := rfl

@[simp, grind =]
lemma run_lift_bind (x y : α) (cont : Bool → FreeM (SortOps α) β) (le : α → α → Bool) :
    run ((FreeM.lift (SortOps.cmpLE x y)).bind cont) le = run (cont (le x y)) le := rfl

@[simp, grind =]
lemma run_bind (P : FreeM (SortOps α) β) (f : β → FreeM (SortOps α) γ)
    (le : α → α → Bool) :
    run (P >>= f) le = run (f (run P le)) le := by
  simp [run, FreeM.liftM_bind]

@[simp, grind =]
lemma cost_pure (b : β) (le : α → α → Bool) :
    cost (pure b : FreeM (SortOps α) β) le = 0 := rfl

@[simp, grind =]
lemma cost_lift (x y : α) (le : α → α → Bool) :
    cost (FreeM.lift (SortOps.cmpLE x y)) le = 1 := rfl

@[simp, grind =]
lemma cost_lift_bind (x y : α) (cont : Bool → FreeM (SortOps α) β) (le : α → α → Bool) :
    cost ((FreeM.lift (SortOps.cmpLE x y)).bind cont) le = 1 + cost (cont (le x y)) le := rfl

@[simp, grind =]
lemma cost_bind (P : FreeM (SortOps α) β) (f : β → FreeM (SortOps α) γ)
    (le : α → α → Bool) :
    cost (P >>= f) le = cost P le + cost (f (run P le)) le := by
  simp [run, cost, FreeM.liftM_bind]

/--
A comparison program making at most `t` comparisons against every comparator in a finite
family `S` attains at most `2 ^ t` distinct results over `S`: a binary decision tree of
depth `t` has at most `2 ^ t` leaves.
-/
theorem card_image_run_le_two_pow_of_cost_le [DecidableEq β]
    {P : FreeM (SortOps α) β} {S : Finset (α → α → Bool)} {t : ℕ}
    (ht : ∀ le ∈ S, cost P le ≤ t) :
    (S.image fun le => run P le).card ≤ 2 ^ t := by
  classical
  induction P generalizing S t with
  | pure b =>
    exact (Finset.card_le_card (Finset.image_subset_iff.2 fun le _ =>
      Finset.mem_singleton_self b)).trans (by simpa using Nat.one_le_two_pow)
  | lift_bind op cont ih =>
    cases op with
    | cmpLE x y =>
      rcases S.eq_empty_or_nonempty with rfl | ⟨le₁, hle₁⟩
      · simp
      obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by grind [ht le₁ hle₁]⟩
      set St := S.filter (fun le => le x y = true) with hSt
      set Sf := S.filter (fun le => ¬le x y = true) with hSf
      -- Split the image along the answer to the root comparison.
      have himage : (S.image fun le => run ((FreeM.lift (SortOps.cmpLE x y)).bind cont) le) =
          (St.image fun le => run (cont true) le) ∪
          (Sf.image fun le => run (cont false) le) := by
        rw [← Finset.filter_union_filter_not_eq (p := fun le => le x y = true) S,
          Finset.image_union, hSt, hSf]
        congr 1
        · exact Finset.image_congr fun le hle => by grind
        · exact Finset.image_congr fun le hle => by grind
      -- Each branch has cost at most `t` over its part of the family.
      have h₁ : (St.image fun le => run (cont true) le).card ≤ 2 ^ t :=
        ih true fun le hle => by grind [ht le]
      have h₂ : (Sf.image fun le => run (cont false) le).card ≤ 2 ^ t :=
        ih false fun le hle => by grind [ht le]
      calc (S.image fun le => run ((FreeM.lift (SortOps.cmpLE x y)).bind cont) le).card
          ≤ (St.image fun le => run (cont true) le).card +
            (Sf.image fun le => run (cont false) le).card :=
            himage ▸ Finset.card_union_le _ _
        _ ≤ 2 ^ t + 2 ^ t := Nat.add_le_add h₁ h₂
        _ = 2 ^ (t + 1) := by grind

/--
Over a finite family `S` of comparators, a comparison program attains at most `2 ^ c`
distinct results, where `c` is its worst-case number of comparisons over `S`.
-/
theorem card_image_run_le_two_pow [DecidableEq β]
    (P : FreeM (SortOps α) β) (S : Finset (α → α → Bool)) :
    (S.image fun le => run P le).card ≤ 2 ^ S.sup fun le => cost P le :=
  card_image_run_le_two_pow_of_cost_le fun _ hle => Finset.le_sup hle

section Sorting

variable {n : ℕ}

/-- The order on `Fin n` induced by a hidden permutation `σ`. -/
def permLE (σ : Equiv.Perm (Fin n)) : Fin n → Fin n → Bool :=
  fun i j => decide (σ i ≤ σ j)

/-- The sorted output for the hidden order `permLE σ`. -/
def permOutput (σ : Equiv.Perm (Fin n)) : List (Fin n) :=
  List.ofFn σ.symm

lemma permOutput_injective : Function.Injective (permOutput (n := n)) := fun _ _ h => by
  simpa using congrArg Equiv.symm (Equiv.coe_fn_injective (List.ofFn_injective h))

/-- Worst-case number of comparisons of `P` over all hidden permutation orders. -/
def worstTime (P : FreeM (SortOps (Fin n)) (List (Fin n))) : ℕ :=
  Finset.univ.sup fun σ : Equiv.Perm (Fin n) => cost P (permLE σ)

/-- A program that sorts under every hidden permutation order distinguishes all `n !` of
them. -/
theorem factorial_le_two_pow_worstTime
    (P : FreeM (SortOps (Fin n)) (List (Fin n)))
    (hP : ∀ σ : Equiv.Perm (Fin n), run P (permLE σ) = permOutput σ) :
    n ! ≤ 2 ^ worstTime P := by
  classical
  have h := card_image_run_le_two_pow P (Finset.univ.image permLE)
  rw [Finset.sup_image, Finset.image_image] at h
  rw [Function.comp_def, Function.comp_def,
    Finset.image_congr (g := permOutput) fun σ _ => hP σ,
    Finset.card_image_of_injective _ permOutput_injective, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin] at h
  exact h

/-- Sorting under every hidden permutation order on `Fin n` takes at least `log₂ (n !)`
comparisons in the worst case. -/
theorem log_factorial_le_worstTime
    (P : FreeM (SortOps (Fin n)) (List (Fin n)))
    (hP : ∀ σ : Equiv.Perm (Fin n), run P (permLE σ) = permOutput σ) :
    Nat.log 2 (n !) ≤ worstTime P :=
  (Nat.log_mono_right (factorial_le_two_pow_worstTime P hP)).trans_eq
    (Nat.log_pow Nat.one_lt_two _)

/-- Explicit lower estimate for `log₂ (n !)`. -/
lemma div_two_mul_log_le_log_factorial (n : ℕ) :
    n / 2 * Nat.log 2 (n / 2) ≤ Nat.log 2 (n !) := by
  set k := n / 2 with hk
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hkPow_le_factorial : k ^ k ≤ n ! :=
      calc k ^ k ≤ k ^ (n - k) := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hk0) (by omega)
        _ ≤ k ! * k ^ (n - k) := Nat.le_mul_of_pos_left _ (Nat.factorial_pos k)
        _ ≤ n ! := Nat.factorial_mul_pow_sub_le_factorial (hk ▸ Nat.div_le_self n 2)
    refine le_trans (Nat.le_log_of_pow_le Nat.one_lt_two ?_)
      (Nat.log_mono_right hkPow_le_factorial)
    calc 2 ^ (k * Nat.log 2 k) = (2 ^ Nat.log 2 k) ^ k := by rw [Nat.mul_comm, Nat.pow_mul]
      _ ≤ k ^ k := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hk0) k

/-- The comparison sort lower bound in explicit `Ω(n log n)` form. -/
theorem cmpSort_lower_bound
    (P : FreeM (SortOps (Fin n)) (List (Fin n)))
    (hP : ∀ σ : Equiv.Perm (Fin n), run P (permLE σ) = permOutput σ) :
    n / 2 * Nat.log 2 (n / 2) ≤ worstTime P :=
  (div_two_mul_log_le_log_factorial n).trans (log_factorial_le_worstTime P hP)

end Sorting

end Cslib.Algorithms
