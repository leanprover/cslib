/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Cslib.AlgorithmsTheory.Models.ListComparisonSort
import all Init.Data.List.Sort.Basic

public import Mathlib

@[expose] public section

namespace Cslib

namespace Algorithms

open Prog

/--
Finite pigeonhole/cardinality step:
if we can inject `m` distinguishable inputs into Boolean transcripts of length `t`,
then `m ≤ 2^t`.
-/
lemma hDecisionTree
    (m t : ℕ)
    (traceCode : Fin m → (Fin t → Bool))
    (hTraceInj : Function.Injective traceCode) :
    m ≤ 2 ^ t := by
  simpa [Fintype.card_fun, Fintype.card_bool] using
    (Fintype.card_le_of_injective traceCode hTraceInj)

/--
Pigeonhole principle in existential form.
-/
lemma hDecisionTreeBound
    (m t : ℕ)
    (hTraceCode :
      ∃ traceCode : Fin m →
          (Fin t → Bool),
        Function.Injective traceCode) :
    m ≤ 2 ^ t := by
  rcases hTraceCode with ⟨traceCode, hTraceInj⟩
  exact hDecisionTree m t traceCode hTraceInj

/--
Finite pigeonhole/cardinality step over an arbitrary finite domain.
-/
lemma hDecisionTreeFintype
    (β : Type*) [Fintype β] (t : ℕ)
    (traceCode : β → (Fin t → Bool))
    (hTraceInj : Function.Injective traceCode) :
    Fintype.card β ≤ 2 ^ t := by
  simpa [Fintype.card_fun, Fintype.card_bool] using
    (Fintype.card_le_of_injective traceCode hTraceInj)

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
Boolean transcript produced by running a comparison program under comparator `le`.
-/
def traceSort : Prog (SortOps α) β → (α → α → Bool) → List Bool
  | .pure _, _ => []
  | .liftBind q cont, le =>
      match q with
      | .cmpLE x y =>
          let b := le x y
          b :: traceSort (cont b) le

@[simp] lemma traceSort_pure (x : β) (le : α → α → Bool) :
    traceSort (.pure x : Prog (SortOps α) β) le = [] := rfl

@[simp] lemma traceSort_liftBind (x y : α) (cont : Bool → Prog (SortOps α) β) (le : α → α → Bool) :
    traceSort (.liftBind (SortOps.cmpLE x y) cont) le =
      (le x y) :: traceSort (cont (le x y)) le := by
  simp [traceSort]

lemma traceSort_length_eq_time (P : Prog (SortOps α) β) (le : α → α → Bool) :
    (traceSort P le).length = P.time (sortModelNat le) := by
  induction P with
  | pure a =>
      simp [traceSort]
  | liftBind op cont ih =>
      cases op with
      | cmpLE x y =>
          simp [traceSort, ih, Nat.add_comm]

/--
If two runs of a program have the same comparison transcript, then they have the same output.
-/
lemma eval_eq_of_traceSort_eq
    (P : Prog (SortOps α) β) {le₁ le₂ : α → α → Bool}
    (h : traceSort P le₁ = traceSort P le₂) :
    P.eval (sortModelNat le₁) = P.eval (sortModelNat le₂) := by
  induction P generalizing le₁ le₂ with
  | pure a =>
      simp
  | liftBind op cont ih =>
      cases op with
      | cmpLE x y =>
          have hcons :
              (le₁ x y) :: traceSort (cont (le₁ x y)) le₁ =
              (le₂ x y) :: traceSort (cont (le₂ x y)) le₂ := by
            simpa [traceSort] using h
          injection hcons with hhead htail
          have htail' :
              traceSort (cont (le₁ x y)) le₁ =
              traceSort (cont (le₁ x y)) le₂ := by
            simpa [hhead] using htail
          simpa [Prog.eval_liftBind, hhead] using ih (le₁ x y) htail'

/--
For a fixed program, one transcript cannot be a strict prefix of another.
-/
lemma traceSort_prefix_eq
    (P : Prog (SortOps α) β) {le₁ le₂ : α → α → Bool}
    (h : traceSort P le₁ <+: traceSort P le₂) :
    traceSort P le₁ = traceSort P le₂ := by
  induction P generalizing le₁ le₂ with
  | pure a =>
      simp [traceSort]
  | liftBind op cont ih =>
      cases op with
      | cmpLE x y =>
          have hcons :
              (le₁ x y) :: traceSort (cont (le₁ x y)) le₁ <+:
              (le₂ x y) :: traceSort (cont (le₂ x y)) le₂ := by
            simpa [traceSort] using h
          rcases List.cons_prefix_cons.mp hcons with ⟨hhead, htail⟩
          have htail' :
              traceSort (cont (le₁ x y)) le₁ <+:
              traceSort (cont (le₁ x y)) le₂ := by
            simpa [hhead] using htail
          have hEqTail := ih (le₁ x y) htail'
          have hEqTail' :
              traceSort (cont (le₂ x y)) le₁ =
              traceSort (cont (le₂ x y)) le₂ := by
            simpa [hhead] using hEqTail
          simp [traceSort, hhead, hEqTail']

/-- Pad a transcript with `false` bits up to a fixed length `t`. -/
def padTrace (t : ℕ) (tr : List Bool) : Fin t → Bool :=
  fun i => (tr[i.1]?).getD false

lemma isPrefix_of_padTrace_eq
    {t : ℕ} {s₁ s₂ : List Bool}
    (hs₁ : s₁.length ≤ t) (hLen : s₁.length ≤ s₂.length)
    (hPad : padTrace t s₁ = padTrace t s₂) :
    s₁ <+: s₂ := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem?'
  intro i hi
  have hTakeLen : (s₂.take s₁.length).length = s₁.length := by
    simp [List.length_take, Nat.min_eq_left hLen]
  have hi₁ : i < s₁.length := by
    simpa [hTakeLen] using hi
  have hi₂ : i < s₂.length := lt_of_lt_of_le hi₁ hLen
  have hit : i < t := lt_of_lt_of_le hi₁ hs₁
  have hAt := congrArg (fun f => f ⟨i, hit⟩) hPad
  calc
    s₁[i]? = (s₁[i]?).getD false := by simp [hi₁]
    _ = (s₂[i]?).getD false := by simpa [padTrace] using hAt
    _ = s₂[i]? := by simp [hi₂]
    _ = (s₂.take s₁.length)[i]? := by
      simpa using (List.getElem?_take_of_lt (l := s₂) (i := i) (j := s₁.length) hi₁).symm

lemma traceSort_eq_of_padTrace_eq
    (P : Prog (SortOps α) β) {le₁ le₂ : α → α → Bool} {t : ℕ}
    (hLen₁ : (traceSort P le₁).length ≤ t)
    (hLen₂ : (traceSort P le₂).length ≤ t)
    (hPad : padTrace t (traceSort P le₁) = padTrace t (traceSort P le₂)) :
    traceSort P le₁ = traceSort P le₂ := by
  by_cases hcmp : (traceSort P le₁).length ≤ (traceSort P le₂).length
  · exact traceSort_prefix_eq P (isPrefix_of_padTrace_eq hLen₁ hcmp hPad)
  · have hcmp' : (traceSort P le₂).length ≤ (traceSort P le₁).length := Nat.le_of_not_ge hcmp
    have hEq21 : traceSort P le₂ = traceSort P le₁ := by
      exact traceSort_prefix_eq P (isPrefix_of_padTrace_eq hLen₂ hcmp' hPad.symm)
    exact hEq21.symm

/-- Worst-case number of comparisons over all hidden permutations of `Fin n`. -/
def worstTime {n : ℕ} (P : Prog (SortOps (Fin n)) (List (Fin n))) : ℕ :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).sup
    (fun σ => P.time (sortModelNat (permLE σ)))

/-- Fixed-length transcript code at depth `worstTime`. -/
def traceCode {n : ℕ} (P : Prog (SortOps (Fin n)) (List (Fin n))) :
    Equiv.Perm (Fin n) → (Fin (worstTime P) → Bool) :=
  fun σ => padTrace (worstTime P) (traceSort P (permLE σ))

lemma traceCode_injective
    {n : ℕ} (P : Prog (SortOps (Fin n)) (List (Fin n)))
    (hCorrect : ∀ σ : Equiv.Perm (Fin n),
      P.eval (sortModelNat (permLE σ)) = permOutput σ) :
    Function.Injective (traceCode P) := by
  intro σ τ hCode
  have hTimeσ :
      P.time (sortModelNat (permLE σ)) ≤
        (Finset.univ : Finset (Equiv.Perm (Fin n))).sup
          (fun ρ => P.time (sortModelNat (permLE ρ))) := by
    exact Finset.le_sup
      (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
      (f := fun ρ => P.time (sortModelNat (permLE ρ)))
      (Finset.mem_univ σ)
  have hTimeτ :
      P.time (sortModelNat (permLE τ)) ≤
        (Finset.univ : Finset (Equiv.Perm (Fin n))).sup
          (fun ρ => P.time (sortModelNat (permLE ρ))) := by
    exact Finset.le_sup
      (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
      (f := fun ρ => P.time (sortModelNat (permLE ρ)))
      (Finset.mem_univ τ)
  have hLenσ : (traceSort P (permLE σ)).length ≤ worstTime P := by
    simpa [worstTime, traceSort_length_eq_time] using hTimeσ
  have hLenτ : (traceSort P (permLE τ)).length ≤ worstTime P := by
    simpa [worstTime, traceSort_length_eq_time] using hTimeτ
  have hTrace :
      traceSort P (permLE σ) = traceSort P (permLE τ) := by
    exact traceSort_eq_of_padTrace_eq P hLenσ hLenτ hCode
  have hEval :
      P.eval (sortModelNat (permLE σ)) = P.eval (sortModelNat (permLE τ)) :=
    eval_eq_of_traceSort_eq P hTrace
  have hOut : permOutput σ = permOutput τ := by
    simpa [hCorrect σ, hCorrect τ] using hEval
  exact permOutput_injective hOut

/--
Decision-tree lower bound in the strong hidden-permutation model:
`n!` distinct hidden orders require at least `log₂(n!)` worst-case comparisons.
-/
lemma hDecisionTreeLower
    {n : ℕ} (P : Prog (SortOps (Fin n)) (List (Fin n)))
    (hCorrect : ∀ σ : Equiv.Perm (Fin n),
      P.eval (sortModelNat (permLE σ)) = permOutput σ) :
    Nat.factorial n ≤ 2 ^ worstTime P := by
  have hCard :
      Fintype.card (Equiv.Perm (Fin n)) ≤ 2 ^ worstTime P :=
    hDecisionTreeFintype (β := Equiv.Perm (Fin n)) (worstTime P) (traceCode P)
      (traceCode_injective P hCorrect)
  simpa [Fintype.card_perm] using hCard

lemma eval_pairwise_of_correct
    {n : ℕ} (P : Prog (SortOps (Fin n)) (List (Fin n)))
    (hCorrect : ∀ σ : Equiv.Perm (Fin n),
      P.eval (sortModelNat (permLE σ)) = permOutput σ)
    (σ : Equiv.Perm (Fin n)) :
    (P.eval (sortModelNat (permLE σ))).Pairwise (fun x y => permLE σ x y = true) := by
  simpa [hCorrect σ] using permOutput_pairwise σ

/--
GPT suggested to pick an abitrary hidden permutation of `Fin n` and generate a list from it
and then prove that for this, sorting takes `n /2 * (Nat.log 2 (n / 2))`
-/
theorem cmpSort_lower_bound
    (n : ℕ) (P : Prog (SortOps (Fin n)) (List (Fin n)))
    (hCorrect : ∀ σ : Equiv.Perm (Fin n),
      P.eval (sortModelNat (permLE σ)) = permOutput σ) :
    worstTime P ≥ (n / 2) * Nat.log 2 (n / 2) := by
  have hDecision : Nat.factorial n ≤ 2 ^ worstTime P :=
    hDecisionTreeLower P hCorrect
  have hLog :
      Nat.log 2 (Nat.factorial n) ≤ Nat.log 2 (2 ^ worstTime P) :=
    Nat.log_mono_right hDecision
  have hTime : Nat.log 2 (Nat.factorial n) ≤ worstTime P := by
    simpa [Nat.log_pow (b := 2) (x := worstTime P) (by decide : 1 < 2)] using hLog
  exact le_trans (hFactorialLog n) hTime



end Algorithms

end Cslib
