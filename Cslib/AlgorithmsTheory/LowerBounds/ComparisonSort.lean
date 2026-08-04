/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.Models.ListComparisonSort
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Nat.Log
import all Init.Data.List.Sort.Basic

/-!
# The Comparison Sort Lower Bound

This file proves the comparison sort lower bound.

-/
@[expose] public section

namespace Cslib

namespace Algorithms

open Prog

/--
Arithmetic lower bound used to derive an `Ω(n log n)` comparison lower bound
from `Nat.log 2 (n!)`.
-/
lemma hFactorialLog (n : ℕ) :
    (n / 2) * Nat.log 2 (n / 2) ≤ Nat.log 2 (Nat.factorial n) := by
  let k := n / 2
  change k * Nat.log 2 k ≤ Nat.log 2 (Nat.factorial n)
  by_cases hk : k = 0
  · simp [hk]
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    have hk_le_n : k ≤ n := by
      simpa [k] using Nat.div_le_self n 2
    have h2k_le_n : k + k ≤ n := by
      simpa [k, two_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_div_le n 2
    have hk_le_sub : k ≤ n - k := (Nat.le_sub_iff_add_le hk_le_n).2 h2k_le_n
    have hPowLe : k ^ k ≤ k ^ (n - k) :=
      Nat.pow_le_pow_right hk_pos hk_le_sub
    have hFactorialPow : Nat.factorial k * k ^ (n - k) ≤ Nat.factorial n :=
      Nat.factorial_mul_pow_sub_le_factorial hk_le_n
    have hkPow_le_factorial : k ^ k ≤ Nat.factorial n := by
      calc
        k ^ k ≤ k ^ (n - k) := hPowLe
        _ ≤ Nat.factorial k * k ^ (n - k) := Nat.le_mul_of_pos_left _ (Nat.factorial_pos k)
        _ ≤ Nat.factorial n := hFactorialPow
    have hLogPow : k * Nat.log 2 k ≤ Nat.log 2 (k ^ k) := by
      have hPow : 2 ^ (k * Nat.log 2 k) ≤ k ^ k := by
        calc
          2 ^ (k * Nat.log 2 k) = (2 ^ Nat.log 2 k) ^ k := by
            rw [Nat.mul_comm, Nat.pow_mul]
          _ ≤ k ^ k := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hk) k
      exact Nat.le_log_of_pow_le (by decide : 1 < 2) hPow
    have hLogMono : Nat.log 2 (k ^ k) ≤ Nat.log 2 (Nat.factorial n) :=
      Nat.log_mono_right hkPow_le_factorial
    exact le_trans hLogPow hLogMono

/-- Convert a decision-tree counting inequality into the `Ω(n log n)` bound. -/
lemma lowerBound_of_factorial_le_pow
    (n t : ℕ) (hDecision : Nat.factorial n ≤ 2 ^ t) :
    (n / 2) * Nat.log 2 (n / 2) ≤ t := by
  have hLog : Nat.log 2 (Nat.factorial n) ≤ Nat.log 2 (2 ^ t) :=
    Nat.log_mono_right hDecision
  have hTime : Nat.log 2 (Nat.factorial n) ≤ t := by
    simpa [Nat.log_pow (b := 2) (x := t) (by decide : 1 < 2)] using hLog
  exact le_trans (hFactorialLog n) hTime

/-- The order on `Fin n` induced by a hidden permutation `σ`. -/
def permLE {n : ℕ} (σ : Equiv.Perm (Fin n)) : Fin n → Fin n → Bool :=
  fun x y => decide (σ x ≤ σ y)

/-- Canonical sorted output for the hidden order induced by `σ`. -/
def permOutput {n : ℕ} (σ : Equiv.Perm (Fin n)) : List (Fin n) :=
  List.ofFn σ.symm

lemma permOutput_pairwise {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permOutput σ).Pairwise (fun x y => permLE σ x y = true) := by
  rw [permOutput, List.pairwise_ofFn]
  intro i j hij
  simpa [permLE, decide_eq_true_eq] using (le_of_lt hij)

lemma permOutput_injective {n : ℕ} :
    Function.Injective (permOutput (n := n)) := by
  intro σ τ h
  have hsymm : (fun i => σ.symm i) = fun i => τ.symm i := List.ofFn_injective h
  ext x
  have hAt : σ.symm (τ x) = τ.symm (τ x) := by
    simpa using congrArg (fun f => f (τ x)) hsymm
  have hσ := congrArg σ hAt
  simpa using (congrArg Fin.val hσ).symm

/--
A program `P : Prog (SortOps α) β` is a binary decision tree: `.pure` is a leaf and a
`cmpLE` query branches on the comparator's answer. Over any finite family `S` of
comparators, `P` attains at most `2 ^ t` distinct results if it makes at most `t`
comparisons against every member of `S`: a binary tree of depth `t` has at most `2 ^ t`
leaves. The family splits at the root comparison into the comparators answering `true`
and those answering `false`, and each part is governed by the corresponding subtree.
-/
theorem card_image_eval_le_two_pow [DecidableEq β]
    (P : Prog (SortOps α) β) (S : Finset (α → α → Bool)) (t : ℕ)
    (ht : ∀ le ∈ S, Prog.time P (sortModelNat le) ≤ t) :
    (S.image fun le => Prog.eval P (sortModelNat le)).card ≤ 2 ^ t := by
  classical
  induction P generalizing S t with
  | pure b =>
    exact (Finset.card_le_card (Finset.image_subset_iff.2 fun le _ =>
      Finset.mem_singleton_self b)).trans (by simpa using Nat.one_le_two_pow)
  | liftBind op cont ih =>
    cases op with
    | cmpLE x y =>
      rcases S.eq_empty_or_nonempty with rfl | ⟨le₁, hle₁⟩
      · simp
      obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := by
        have h₁ := ht le₁ hle₁
        simp only [Prog.time_liftBind, sortModelNat_cost] at h₁
        exact ⟨t - 1, by omega⟩
      set St := S.filter (fun le => le x y = true) with hSt
      set Sf := S.filter (fun le => ¬le x y = true) with hSf
      -- Split the image along the answer to the root comparison.
      have himage :
          (S.image fun le =>
            Prog.eval (FreeM.liftBind (SortOps.cmpLE x y) cont) (sortModelNat le)) =
          (St.image fun le => Prog.eval (cont true) (sortModelNat le)) ∪
          (Sf.image fun le => Prog.eval (cont false) (sortModelNat le)) := by
        rw [← Finset.filter_union_filter_not_eq (fun le => le x y = true) S,
          Finset.image_union, hSt, hSf]
        congr 1
        · exact Finset.image_congr fun le hle => by
            have hxy : le x y = true := (Finset.mem_filter.mp hle).2
            simp [hxy]
        · exact Finset.image_congr fun le hle => by
            have hxy : le x y = false := by simpa using (Finset.mem_filter.mp hle).2
            simp [hxy]
      -- Each branch has cost at most `t` over its part of the family.
      have h₁ : (St.image fun le => Prog.eval (cont true) (sortModelNat le)).card ≤ 2 ^ t :=
        ih true St t fun le hle => by
          have h := ht le (Finset.mem_filter.mp hle).1
          simp only [Prog.time_liftBind, sortModelNat_cost, sortModelNat_evalQuery_cmpLE,
            (Finset.mem_filter.mp hle).2] at h
          omega
      have h₂ : (Sf.image fun le => Prog.eval (cont false) (sortModelNat le)).card ≤ 2 ^ t :=
        ih false Sf t fun le hle => by
          have hxy : le x y = false := by simpa using (Finset.mem_filter.mp hle).2
          have h := ht le (Finset.mem_filter.mp hle).1
          simp only [Prog.time_liftBind, sortModelNat_cost, sortModelNat_evalQuery_cmpLE,
            hxy] at h
          omega
      calc (S.image fun le =>
              Prog.eval (FreeM.liftBind (SortOps.cmpLE x y) cont) (sortModelNat le)).card
          ≤ (St.image fun le => Prog.eval (cont true) (sortModelNat le)).card +
            (Sf.image fun le => Prog.eval (cont false) (sortModelNat le)).card :=
            himage ▸ Finset.card_union_le _ _
        _ ≤ 2 ^ t + 2 ^ t := Nat.add_le_add h₁ h₂
        _ = 2 ^ (t + 1) := by rw [pow_succ, Nat.mul_two]

/-- Worst-case comparisons over a finite hidden family of comparators. -/
def worstTimeComp {ι : Type*} [Fintype ι]
    (P : Prog (SortOps α) (List α)) (leF : ι → α → α → Bool) : ℕ :=
  (Finset.univ : Finset ι).sup (fun i => P.time (sortModelNat (leF i)))

/--
If a program computes an injective output across a finite hidden family of comparators,
then the family injects into the leaves of the program's decision tree, so its
cardinality is at most `2 ^ worstTimeComp`.
-/
theorem card_le_two_pow_worstTimeComp
    {ι : Type*} [Fintype ι]
    (P : Prog (SortOps α) (List α)) (leF : ι → α → α → Bool)
    (output : ι → List α)
    (hOutputInj : Function.Injective output)
    (hCorrect : ∀ i, P.eval (sortModelNat (leF i)) = output i) :
    Fintype.card ι ≤ 2 ^ worstTimeComp P leF := by
  classical
  have h := card_image_eval_le_two_pow P (Finset.univ.image leF) (worstTimeComp P leF)
    (fun le hle => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hle
      exact Finset.le_sup (f := fun j => Prog.time P (sortModelNat (leF j))) (Finset.mem_univ i))
  rw [Finset.image_image] at h
  have himg : (Finset.univ.image ((fun le => Prog.eval P (sortModelNat le)) ∘ leF)) =
      Finset.univ.image output :=
    Finset.image_congr fun i _ => hCorrect i
  rw [himg, Finset.card_image_of_injective _ hOutputInj, Finset.card_univ] at h
  exact h

/-- Worst-case number of comparisons over all hidden permutations of `Fin n`. -/
abbrev worstTime {n : ℕ} (P : Prog (SortOps (Fin n)) (List (Fin n))) : ℕ :=
  worstTimeComp P (fun σ => permLE σ)

/--
Decision-tree lower bound in the strong hidden-permutation model:
`n!` distinct hidden orders require at least `log₂(n!)` worst-case comparisons.
-/
lemma hDecisionTreeLower
    {n : ℕ} (P : Prog (SortOps (Fin n)) (List (Fin n)))
    (hCorrect : ∀ σ : Equiv.Perm (Fin n),
      P.eval (sortModelNat (permLE σ)) = permOutput σ) :
    Nat.factorial n ≤ 2 ^ worstTime P := by
  simpa [Fintype.card_perm] using
    card_le_two_pow_worstTimeComp P (fun σ => permLE σ) (permOutput (n := n))
      (permOutput_injective (n := n)) hCorrect

/--
Any comparison program that sorts under every hidden permutation order on `Fin n`
performs at least `n / 2 * log₂ (n / 2)` comparisons in the worst case.
-/
theorem cmpSort_lower_bound
    (n : ℕ) (P : Prog (SortOps (Fin n)) (List (Fin n)))
    (hCorrect : ∀ σ : Equiv.Perm (Fin n),
      P.eval (sortModelNat (permLE σ)) = permOutput σ) :
    worstTime P ≥ (n / 2) * Nat.log 2 (n / 2) := by
  have hDecision : Nat.factorial n ≤ 2 ^ worstTime P :=
    hDecisionTreeLower P hCorrect
  exact lowerBound_of_factorial_le_pow n (worstTime P) hDecision

section HiddenOrderEquiv

/-- Hidden order induced by a permutation after encoding elements with `e : β ≃ Fin n`. -/
def permLEEquiv {β : Type} {n : ℕ}
    (e : β ≃ Fin n) (σ : Equiv.Perm (Fin n)) : β → β → Bool :=
  fun x y => decide (σ (e x) ≤ σ (e y))

/-- Canonical sorted output induced by `σ`, transported through `e`. -/
def permOutputEquiv {β : Type} {n : ℕ}
    (e : β ≃ Fin n) (σ : Equiv.Perm (Fin n)) : List β :=
  List.ofFn (fun i => e.symm (σ.symm i))

lemma permOutputEquiv_injective {β : Type} {n : ℕ}
    (e : β ≃ Fin n) :
    Function.Injective (permOutputEquiv e) := by
  intro σ τ h
  have hsymm :
      (fun i => e.symm (σ.symm i)) = fun i => e.symm (τ.symm i) :=
    List.ofFn_injective h
  ext x
  have hAt : e.symm (σ.symm (τ x)) = e.symm (τ.symm (τ x)) := by
    simpa using congrArg (fun f => f (τ x)) hsymm
  have hAt' : σ.symm (τ x) = τ.symm (τ x) := by
    simpa using congrArg e hAt
  have hσ : τ x = σ x := by
    simpa using congrArg σ hAt'
  simpa [eq_comm] using congrArg Fin.val hσ

/-- Worst-case comparisons over hidden permutations, transported through `e`. -/
abbrev worstTimeEquiv {β : Type} {n : ℕ}
    (e : β ≃ Fin n) (P : Prog (SortOps β) (List β)) : ℕ :=
  worstTimeComp P (fun σ => permLEEquiv e σ)

lemma hDecisionTreeLowerEquiv
    {β : Type} {n : ℕ}
    (e : β ≃ Fin n) (P : Prog (SortOps β) (List β))
    (hCorrect : ∀ σ : Equiv.Perm (Fin n),
      Prog.eval P (sortModelNat (α := β) (permLEEquiv e σ)) = permOutputEquiv e σ) :
    Nat.factorial n ≤ 2 ^ worstTimeEquiv e P := by
  simpa [Fintype.card_perm] using
    card_le_two_pow_worstTimeComp P (fun σ => permLEEquiv e σ) (permOutputEquiv e)
      (permOutputEquiv_injective e) hCorrect

/-- `Ω(n log n)` lower bound on any type equivalent to `Fin n`. -/
theorem cmpSort_lower_bound_equiv
    {β : Type} {n : ℕ}
    (e : β ≃ Fin n) (P : Prog (SortOps β) (List β))
    (hCorrect : ∀ σ : Equiv.Perm (Fin n),
      Prog.eval P (sortModelNat (α := β) (permLEEquiv e σ)) = permOutputEquiv e σ) :
    worstTimeEquiv e P ≥ (n / 2) * Nat.log 2 (n / 2) := by
  have hDecision : Nat.factorial n ≤ 2 ^ worstTimeEquiv e P :=
    hDecisionTreeLowerEquiv e P hCorrect
  exact lowerBound_of_factorial_le_pow n (worstTimeEquiv e P) hDecision

/-- `Ω(n log n)` lower bound stated directly for a finite carrier type `α`. -/
theorem cmpSort_lower_bound_fintype
    (α : Type) [Fintype α]
    (P : Prog (SortOps α) (List α))
    (hCorrect : ∀ σ : Equiv.Perm (Fin (Fintype.card α)),
      Prog.eval P (sortModelNat (α := α) (permLEEquiv (Fintype.equivFin α) σ)) =
        permOutputEquiv (Fintype.equivFin α) σ) :
    worstTimeEquiv (Fintype.equivFin α) P ≥
      (Fintype.card α / 2) * Nat.log 2 (Fintype.card α / 2) := by
  simpa using cmpSort_lower_bound_equiv (e := Fintype.equivFin α) (P := P) hCorrect

/--
Lower bound specialized to a fixed nodup list `l`.
This is a corollary of the fintype statement with carrier `{x // x ∈ l}`.
-/
theorem cmpSort_lower_bound_infinite_types
    {α : Type} [DecidableEq α]
    (l : List α) (hNodup : l.Nodup)
    (P : Prog (SortOps {x // x ∈ l}) (List {x // x ∈ l}))
    (hCorrect : ∀ σ : Equiv.Perm (Fin l.length),
      Prog.eval P (sortModelNat (α := {x // x ∈ l})
        (permLEEquiv (List.Nodup.getEquiv l hNodup).symm σ)) =
        permOutputEquiv (List.Nodup.getEquiv l hNodup).symm σ) :
    worstTimeEquiv (List.Nodup.getEquiv l hNodup).symm P ≥
      (l.length / 2) * Nat.log 2 (l.length / 2) := by
  simpa using cmpSort_lower_bound_equiv (List.Nodup.getEquiv l hNodup).symm P hCorrect

end HiddenOrderEquiv

section HiddenModelFamily

/-!
## Hidden model family lower bounds

This section develops the decision-tree lower bound in a model-parametric style:
the hidden input is a finite family of `SortOps` models (or equivalently a finite
family of comparators) satisfying order laws and unit comparison cost.
-/

/-- Comparator extracted from an arbitrary `SortOps` model. -/
def modelLE (M : Model (SortOps α) ℕ) : α → α → Bool :=
  fun x y => M.evalQuery (SortOps.cmpLE x y)

@[simp]
lemma modelLE_sortModelNat {α : Type*} (le : α → α → Bool) :
    modelLE (sortModelNat le) = le := rfl

lemma eval_eq_eval_sortModelNat_modelLE
    (P : Prog (SortOps α) β) (M : Model (SortOps α) ℕ) :
    P.eval M = P.eval (sortModelNat (modelLE M)) := by
  induction P with
  | pure a =>
      simp
  | liftBind op cont ih =>
      cases op with
      | cmpLE x y =>
          simpa [Prog.eval_liftBind, modelLE] using ih (modelLE M x y)

lemma time_eq_time_sortModelNat_modelLE
    (P : Prog (SortOps α) β) (M : Model (SortOps α) ℕ)
    (hCost : ∀ x y, M.cost (SortOps.cmpLE x y) = 1) :
    P.time M = P.time (sortModelNat (modelLE M)) := by
  induction P with
  | pure a =>
      simp
  | liftBind op cont ih =>
      cases op with
      | cmpLE x y =>
          simpa [Prog.time_liftBind, modelLE, hCost x y] using
            ih (modelLE M x y)

/-- Worst-case comparisons over a finite hidden family of `SortOps` models. -/
def worstTimeModel {ι : Type*} [Fintype ι]
    (models : ι → Model (SortOps α) ℕ)
    (P : Prog (SortOps α) (List α)) : ℕ :=
  (Finset.univ : Finset ι).sup (fun i => P.time (models i))

/--
Decision-tree lower bound over an arbitrary finite hidden family of unit-cost
comparison models.
-/
lemma hDecisionTreeLowerModel
    {ι : Type*} [Fintype ι]
    (models : ι → Model (SortOps α) ℕ)
    (hCost : ∀ i x y, (models i).cost (SortOps.cmpLE x y) = 1)
    (P : Prog (SortOps α) (List α))
    (output : ι → List α)
    (hOutputInj : Function.Injective output)
    (hCorrect : ∀ i, P.eval (models i) = output i) :
    Fintype.card ι ≤ 2 ^ worstTimeModel models P := by
  have hworst : worstTimeModel models P = worstTimeComp P (fun i => modelLE (models i)) :=
    Finset.sup_congr rfl fun i _ =>
      time_eq_time_sortModelNat_modelLE P (models i) (hCost i)
  rw [hworst]
  exact card_le_two_pow_worstTimeComp P (fun i => modelLE (models i)) output hOutputInj
    fun i => (eval_eq_eval_sortModelNat_modelLE P (models i)).symm.trans (hCorrect i)

/--
We prove the cardinality assumption used in this lemma in
`factorial_le_card_of_orderEmbedding` below.

This formulation is model-parametric: the hidden instances are full `SortOps`
models, not only permutation-induced comparators.
-/
lemma cmpSort_lower_bound_model
    {ι : Type*} [Fintype ι]
    (n : ℕ)
    (models : ι → Model (SortOps α) ℕ)
    (hCost : ∀ i x y, (models i).cost (SortOps.cmpLE x y) = 1)
    (P : Prog (SortOps α) (List α))
    (output : ι → List α)
    (hOutputInj : Function.Injective output)
    (hCorrect : ∀ i, P.eval (models i) = output i)
    (hCard : Nat.factorial n ≤ Fintype.card ι) :
    worstTimeModel models P ≥ (n / 2) * Nat.log 2 (n / 2) := by
  have hDecisionFamily : Fintype.card ι ≤ 2 ^ worstTimeModel models P :=
    hDecisionTreeLowerModel models hCost P output hOutputInj hCorrect
  have hDecision : Nat.factorial n ≤ 2 ^ worstTimeModel models P :=
    le_trans hCard hDecisionFamily
  exact lowerBound_of_factorial_le_pow n (worstTimeModel models P) hDecision

lemma factorial_le_card_of_orderEmbedding
    {ι : Type*} [Fintype ι] (n : ℕ) (emb : Equiv.Perm (Fin n) ↪ ι) :
    Nat.factorial n ≤ Fintype.card ι := by
  have hCardPerm : Fintype.card (Equiv.Perm (Fin n)) ≤ Fintype.card ι :=
    Fintype.card_le_of_injective emb emb.injective
  simpa [Fintype.card_perm] using hCardPerm

/--
`Ω(n log n)` lower bound from any hidden comparator family: if a program's evaluations
distinguish all members of a family into which the permutations of `Fin n` embed, it
performs `Ω(n log n)` comparisons in the worst case.
-/
theorem cmpSort_lower_bound_le_family
    {ι : Type*} [Fintype ι]
    (n : ℕ)
    (le : ι → α → α → Bool)
    (P : Prog (SortOps α) (List α))
    (hEvalInj : Function.Injective (fun i => P.eval (sortModelNat (le i))))
    (emb : Equiv.Perm (Fin n) ↪ ι) :
    worstTimeModel (fun i => sortModelNat (le i)) P ≥
      (n / 2) * Nat.log 2 (n / 2) :=
  cmpSort_lower_bound_model n (fun i => sortModelNat (le i)) (fun _ _ _ => rfl) P
    (fun i => P.eval (sortModelNat (le i))) hEvalInj (fun _ => rfl)
    (factorial_le_card_of_orderEmbedding n emb)

end HiddenModelFamily

end Algorithms

end Cslib
