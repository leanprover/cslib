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
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Data.Nat.Log
import all Init.Data.List.Sort.Basic

@[expose] public section

namespace Cslib

namespace Algorithms

open Prog

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
          simpa [traceSort, Nat.add_comm] using ih (le x y)

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

/-- Worst-case comparisons over a finite hidden family of comparators. -/
def worstTimeComp {ι : Type*} [Fintype ι]
    (P : Prog (SortOps α) (List α)) (leF : ι → α → α → Bool) : ℕ :=
  (Finset.univ : Finset ι).sup (fun i => P.time (sortModelNat (leF i)))

/-- Fixed-length transcript code at depth `worstTimeComp`. -/
def traceCodeComp {ι : Type*} [Fintype ι]
    (P : Prog (SortOps α) (List α)) (leF : ι → α → α → Bool) :
    ι → (Fin (worstTimeComp P leF) → Bool) :=
  fun i => padTrace (worstTimeComp P leF) (traceSort P (leF i))

lemma traceCodeComp_injective
    {ι : Type*} [Fintype ι]
    (P : Prog (SortOps α) (List α)) (leF : ι → α → α → Bool)
    (output : ι → List α)
    (hOutputInj : Function.Injective output)
    (hCorrect : ∀ i, P.eval (sortModelNat (leF i)) = output i) :
    Function.Injective (traceCodeComp P leF) := by
  intro i j hCode
  have hLen (ρ : ι) :
      (traceSort P (leF ρ)).length ≤ worstTimeComp P leF := by
    simpa [worstTimeComp, traceSort_length_eq_time] using
      (Finset.le_sup
        (s := (Finset.univ : Finset ι))
        (f := fun k => P.time (sortModelNat (leF k)))
        (Finset.mem_univ ρ))
  have hTrace :
      traceSort P (leF i) = traceSort P (leF j) := by
    exact traceSort_eq_of_padTrace_eq P (hLen i) (hLen j) hCode
  exact hOutputInj <| by
    simpa [hCorrect i, hCorrect j] using eval_eq_of_traceSort_eq P hTrace

/-- Worst-case number of comparisons over all hidden permutations of `Fin n`. -/
abbrev worstTime {n : ℕ} (P : Prog (SortOps (Fin n)) (List (Fin n))) : ℕ :=
  worstTimeComp P (fun σ => permLE σ)

/-- Fixed-length transcript code at depth `worstTime`. -/
abbrev traceCode {n : ℕ} (P : Prog (SortOps (Fin n)) (List (Fin n))) :
    Equiv.Perm (Fin n) → (Fin (worstTime P) → Bool) :=
  traceCodeComp P (fun σ => permLE σ)

lemma traceCode_injective
    {n : ℕ} (P : Prog (SortOps (Fin n)) (List (Fin n)))
    (hCorrect : ∀ σ : Equiv.Perm (Fin n),
      P.eval (sortModelNat (permLE σ)) = permOutput σ) :
    Function.Injective (traceCode P) := by
  simpa [traceCode, worstTime] using
    (traceCodeComp_injective P (fun σ => permLE σ) (permOutput (n := n))
      (permOutput_injective (n := n)) hCorrect)

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
    (hDecisionTreeFintype (β := Equiv.Perm (Fin n)) (worstTime P) (traceCode P)
      (traceCode_injective P hCorrect))

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

/-- Fixed-length transcript code at depth `worstTimeEquiv`. -/
abbrev traceCodeEquiv {β : Type} {n : ℕ}
    (e : β ≃ Fin n) (P : Prog (SortOps β) (List β)) :
    Equiv.Perm (Fin n) → (Fin (worstTimeEquiv e P) → Bool) :=
  traceCodeComp P (fun σ => permLEEquiv e σ)

lemma traceCodeEquiv_injective
    {β : Type} {n : ℕ}
    (e : β ≃ Fin n) (P : Prog (SortOps β) (List β))
    (hCorrect : ∀ σ : Equiv.Perm (Fin n),
      Prog.eval P (sortModelNat (α := β) (permLEEquiv e σ)) = permOutputEquiv e σ) :
    Function.Injective (traceCodeEquiv e P) := by
  simpa [traceCodeEquiv, worstTimeEquiv] using
    (traceCodeComp_injective P (fun σ => permLEEquiv e σ) (permOutputEquiv e)
      (permOutputEquiv_injective e) hCorrect)

lemma hDecisionTreeLowerEquiv
    {β : Type} {n : ℕ}
    (e : β ≃ Fin n) (P : Prog (SortOps β) (List β))
    (hCorrect : ∀ σ : Equiv.Perm (Fin n),
      Prog.eval P (sortModelNat (α := β) (permLEEquiv e σ)) = permOutputEquiv e σ) :
    Nat.factorial n ≤ 2 ^ worstTimeEquiv e P := by
  simpa [Fintype.card_perm] using
    (hDecisionTreeFintype (β := Equiv.Perm (Fin n)) (worstTimeEquiv e P) (traceCodeEquiv e P)
      (traceCodeEquiv_injective e P hCorrect))

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

/-- Order laws for a finite family of Boolean comparators. -/
structure ComparatorLawsFamily {ι α : Type*} (le : ι → α → α → Bool) where
  total : ∀ i, Std.Total (fun x y => le i x y = true)
  trans : ∀ i, IsTrans α (fun x y => le i x y = true)

/-- Laws required for a finite hidden family of `SortOps` models. -/
structure ModelLawsFamily {ι α : Type*}
    (models : ι → Model (SortOps α) ℕ) where
  unitCost : ∀ i x y, (models i).cost (SortOps.cmpLE x y) = 1
  cmpLaws : ComparatorLawsFamily (fun i => modelLE (models i))

/--
sortModelNats obey the model family laws and can therefore be instantiated
to the modelLawsFamily structure.
-/
lemma modelLawsFamily_sortModelNat
    {ι α : Type*} {le : ι → α → α → Bool}
    (hLaws : ComparatorLawsFamily le) :
    ModelLawsFamily (fun i => sortModelNat (le i)) := by
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · intro i x y
        grind [sortModelNat]
      · intro i
        simpa [modelLE, sortModelNat] using hLaws.total i
      · intro i
        simpa [modelLE, sortModelNat] using hLaws.trans i

lemma eval_eq_eval_sortModelNat_modelLE
    (P : Prog (SortOps α) β) (M : Model (SortOps α) ℕ) :
    P.eval M = P.eval (sortModelNat (modelLE M)) := by
  induction P with
  | pure a =>
      simp
  | liftBind op cont ih =>
      cases op with
      | cmpLE x y =>
          simpa [Prog.eval_liftBind, modelLE, sortModelNat] using ih (modelLE M x y)

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
          simpa [Prog.time_liftBind, modelLE, sortModelNat, hCost x y] using
            ih (modelLE M x y)

lemma traceSort_length_eq_time_model
    (P : Prog (SortOps α) β) (M : Model (SortOps α) ℕ)
    (hCost : ∀ x y, M.cost (SortOps.cmpLE x y) = 1) :
    (traceSort P (modelLE M)).length = P.time M := by
  calc
    (traceSort P (modelLE M)).length = P.time (sortModelNat (modelLE M)) :=
      traceSort_length_eq_time P (modelLE M)
    _ = P.time M := (time_eq_time_sortModelNat_modelLE P M hCost).symm

/-- Worst-case comparisons over a finite hidden family of `SortOps` models. -/
def worstTimeModel {ι : Type*} [Fintype ι]
    (models : ι → Model (SortOps α) ℕ)
    (P : Prog (SortOps α) (List α)) : ℕ :=
  (Finset.univ : Finset ι).sup (fun i => P.time (models i))

/-- Fixed-length transcript code at depth `worstTimeModel`. -/
def traceCodeModel {ι : Type*} [Fintype ι]
    (models : ι → Model (SortOps α) ℕ)
    (P : Prog (SortOps α) (List α)) :
    ι → (Fin (worstTimeModel models P) → Bool) :=
  fun i => padTrace (worstTimeModel models P) (traceSort P (modelLE (models i)))

lemma traceCodeModel_injective
    {ι : Type*} [Fintype ι]
    (models : ι → Model (SortOps α) ℕ)
    (hCost : ∀ i x y, (models i).cost (SortOps.cmpLE x y) = 1)
    (P : Prog (SortOps α) (List α))
    (output : ι → List α)
    (hOutputInj : Function.Injective output)
    (hCorrect : ∀ i, P.eval (models i) = output i) :
    Function.Injective (traceCodeModel models P) := by
  intro i j hCode
  have hLen (ρ : ι) :
      (traceSort P (modelLE (models ρ))).length ≤ worstTimeModel models P := by
    have hTimeρ :
        P.time (models ρ) ≤
          (Finset.univ : Finset ι).sup (fun k => P.time (models k)) := by
      exact Finset.le_sup
        (s := (Finset.univ : Finset ι))
        (f := fun k => P.time (models k))
        (Finset.mem_univ ρ)
    grind [worstTimeModel, traceSort_length_eq_time_model, hCost ρ]
  have hTrace :
      traceSort P (modelLE (models i)) = traceSort P (modelLE (models j)) := by
    exact traceSort_eq_of_padTrace_eq P (hLen i) (hLen j) hCode
  have hEval :
      P.eval (models i) = P.eval (models j) := by
    calc
      P.eval (models i) = P.eval (sortModelNat (modelLE (models i))) :=
        eval_eq_eval_sortModelNat_modelLE P (models i)
      _ = P.eval (sortModelNat (modelLE (models j))) :=
        eval_eq_of_traceSort_eq P hTrace
      _ = P.eval (models j) :=
        (eval_eq_eval_sortModelNat_modelLE P (models j)).symm
  exact hOutputInj <| by
    aesop (add simp [hCorrect, hEval])

/--
Decision-tree lower bound over an arbitrary finite hidden family of unit-cost
comparison models.
-/
lemma hDecisionTreeLowerModel
    {ι : Type*} [Fintype ι]
    (models : ι → Model (SortOps α) ℕ)
    (hLaws : ModelLawsFamily models)
    (P : Prog (SortOps α) (List α))
    (output : ι → List α)
    (hOutputInj : Function.Injective output)
    (hCorrect : ∀ i, P.eval (models i) = output i) :
    Fintype.card ι ≤ 2 ^ worstTimeModel models P := by
  simpa using hDecisionTreeFintype (β := ι) (worstTimeModel models P) (traceCodeModel models P)
    (traceCodeModel_injective models hLaws.unitCost P output hOutputInj hCorrect)

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
    (hLaws : ModelLawsFamily models)
    (P : Prog (SortOps α) (List α))
    (output : ι → List α)
    (hOutputInj : Function.Injective output)
    (hCorrect : ∀ i, P.eval (models i) = output i)
    (hCard : Nat.factorial n ≤ Fintype.card ι) :
    worstTimeModel models P ≥ (n / 2) * Nat.log 2 (n / 2) := by
  have hDecisionFamily : Fintype.card ι ≤ 2 ^ worstTimeModel models P :=
    hDecisionTreeLowerModel models hLaws P output hOutputInj hCorrect
  have hDecision : Nat.factorial n ≤ 2 ^ worstTimeModel models P :=
    le_trans hCard hDecisionFamily
  exact lowerBound_of_factorial_le_pow n (worstTimeModel models P) hDecision

/--
If program evaluations are injective across hidden comparators, then any pointwise
equal output specification is injective as well.
-/
lemma output_injective_of_eval_injective
    {ι : Type*}
    (le : ι → α → α → Bool)
    (P : Prog (SortOps α) (List α))
    (output : ι → List α)
    (hCorrect : ∀ i, P.eval (sortModelNat (le i)) = output i)
    (hEvalInj : Function.Injective (fun i => P.eval (sortModelNat (le i)))) :
    Function.Injective output := by
  intro i j hEq
  apply hEvalInj
  grind

/-- Correctness witness for a hidden family of comparators used in the lower bound. -/
structure LeFamilyCorrectness {ι α : Type*}
    (n : ℕ) (evalF : ι → List α) where
  /-- The output list -/
  output : ι → List α
  correct : ∀ i : ι, evalF i = output i
  evalInj : Function.Injective evalF
  /-- The embedding of a permutation on n elements into ι -/
  orderEmbedding : Equiv.Perm (Fin n) ↪ ι

lemma factorial_le_card_of_orderEmbedding
    {ι : Type*} [Fintype ι] (n : ℕ) (emb : Equiv.Perm (Fin n) ↪ ι) :
    Nat.factorial n ≤ Fintype.card ι := by
  have hCardPerm : Fintype.card (Equiv.Perm (Fin n)) ≤ Fintype.card ι :=
    Fintype.card_le_of_injective emb emb.injective
  simpa [Fintype.card_perm] using hCardPerm

/--
`Ω(n log n)` lower bound from any hidden model family.
Comparator-family formulation: hidden instances are given directly as `le i`.
-/
theorem cmpSort_lower_bound_le_family
    {ι : Type*} [Fintype ι]
    (n : ℕ)
    (le : ι → α → α → Bool)
    (hLaws : ComparatorLawsFamily le)
    (P : Prog (SortOps α) (List α))
    (hSpec : LeFamilyCorrectness n (fun i => P.eval (sortModelNat (le i)))) :
    worstTimeModel (fun i => sortModelNat (le i)) P ≥
      (n / 2) * Nat.log 2 (n / 2) := by
  have hCard : Nat.factorial n ≤ Fintype.card ι :=
    factorial_le_card_of_orderEmbedding n hSpec.orderEmbedding
  have hOutputInj : Function.Injective hSpec.output := by
    exact output_injective_of_eval_injective le P hSpec.output hSpec.correct hSpec.evalInj
  refine cmpSort_lower_bound_model (n := n) (models := fun i => sortModelNat (le i))
      (hLaws := modelLawsFamily_sortModelNat hLaws)
      (P := P) (output := hSpec.output) hOutputInj hSpec.correct hCard

end HiddenModelFamily

end Algorithms

end Cslib
