/-
Copyright (c) 2026 zayn7lie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Wang, Maksym Radziwill
-/
module

public import Mathlib.Data.Nat.Basic
public import Cslib.Foundations.Syntax.HasSubstitution

/-!
# Untyped lambda calculus with de Bruijn indices

This file defines the syntax of untyped lambda terms using de Bruijn indices, together
with the basic operations on terms needed for β-reduction.  Using de Bruijn indices avoids
explicit reasoning about α-conversion and variable names.

## Main definitions

* `Lambda.Term`: the type of lambda terms.
* `Term.incre`: lifting (shifting) of free variables above a cutoff.
* `Term.subst`: raw substitution at a de Bruijn index.
* `Term.decre`: lowering of free variables above a cutoff.
* `Term.sub`: the substitution operation implementing β-contraction.

## Main lemmas

* `Term.incre_rfl`: shifting by `0` is the identity.
* `Term.decre_incre_elim`: lowering cancels a corresponding shift.
* `Term.var_sub_elim`, `Term.var_lt_sub`, `Term.var_gt_sub`: basic computations for
  substitution on variables.

## Notes

The definitions in this file are tailored to the later development of one-step β-reduction,
parallel reduction, and the Church–Rosser theorem.

## References

* <https://en.wikipedia.org/wiki/De_Bruijn_index>
-/


namespace Lambda

/-- using de Bruijn syntax avoiding α-conversion -/
public inductive Term : Type where
  | var : Nat → Term
  | abs : Term → Term
  | app : Term → Term → Term
deriving DecidableEq, Repr

open Term
namespace Term

notation:max "𝕧" str => Term.var str
notation:max "λ." t => Term.abs t
infixl:77 "·" => Term.app

/-- `incre i l t` increments `i` for all free vars `≥ l`. -/
@[expose] public def incre (i : Nat) (l : Nat) : Term → Term
  | var k   => if l ≤ k then var (k + i) else var k
  | abs t   => abs (incre i (l + 1) t)
  | app t u => app (incre i l t) (incre i l u)

/-- `subst j s t` substitutes `j` with term `s` in `t`. -/
@[expose] public def subst (j : Nat) (s : Term) : Term → Term
  | var k   => if k = j then s else var k
  | abs t   => abs (subst (j + 1) (incre 1 0 s) t)
  | app t u => app (subst j s t) (subst j s u)

/-- `decre i l t` decrements `i` for all free vars `≥ l + i`.
    the reason using `l + i` is that it is more explicit for
    free variable elimination. For example, after eliminating
    `var k` for Term `t` from the most outside, `decre 1 k t`
    will close the gap caused by `k` elimination. -/
@[expose] public def decre (i : Nat) (l : Nat) : Term → Term
  | var k   => if l + i ≤ k then var (k - i) else var k
  | abs t   => abs (decre i (l + 1) t)
  | app t u => app (decre i l t) (decre i l u)

/-- Substitute into the body of a lambda: `(λ.t) s` -/
@[expose] public def sub (t : Term) (n : Nat) (s : Term) := 
  decre 1 n (subst n (incre 1 n s) t)

/-- Notation typeclass for substitution, t[n := s] ≃ t.sub n s 
    which substitute nth variable in t with s. -/
@[expose] public instance : Cslib.HasSubstitution Term Nat Term 
  where subst := sub

/-- Increment of 0 is identity -/
@[simp] public theorem incre_rfl {l t} : incre 0 l t = t := by
  induction t generalizing l with
  | var k => simp_all only [incre, Nat.add_zero, ite_self]
  | abs t ih => simp_all only [incre]
  | app t u iht ihu => simp_all only [incre]

/-- Decrement of increment with same bound is the same.
Lemma for `var_sub` -/
@[simp] public theorem decre_incre_elim {l t} : 
    decre 1 l (incre 1 l t) = t := by
  induction t generalizing l with
  | var k =>
      unfold decre incre
      cases em (l ≤ k) with
      | inl h => simp_all only [↓reduceIte, 
          Nat.add_le_add_iff_right, Nat.add_one_sub_one]
      | inr h =>
          have : ¬(l + 1 ≤ k) := by omega
          simp only [if_neg h, if_neg this]
  | abs t ih => simp_all only [incre, decre]
  | app t u iht ihu => simp_all only [incre, decre]

/-- Substitution of var n. -/
@[simp] public theorem var_sub_elim {n s} : ((𝕧 n).sub) n s = s := by
  simp_all only [sub, subst, ↓reduceIte, decre_incre_elim]

/-- Vacuously Substitution of var k to var k. -/
@[simp] public theorem var_lt_sub {k n s} (hk : k < n) :
    ((𝕧 k).sub) n s = 𝕧 k := by
  have : ¬(n + 1 ≤ k) := by omega
  simp_all only [sub, subst, Nat.ne_of_lt hk, 
    ↓reduceIte, decre]

/-- Vacuously Substitution of var k to var k - 1. -/
@[simp] public theorem var_gt_sub {k n s} (hk : k > n) :
    ((𝕧 k).sub) n s = 𝕧 (k - 1) := by
  have : n + 1 ≤ k := by omega
  simp_all only [gt_iff_lt, sub, subst, 
    Nat.ne_of_gt hk, ↓reduceIte, decre]

/-- Increments elimination for same lower bound.
Special thanks to professor Radziwill @maksym-radziwill about
his idea of generalizing proper variable. -/
@[simp] public theorem incre_same_bound_elim {i j n t} :
    (incre i n (incre j n t)) = (incre (i + j) n t) := by
  induction t generalizing i n with
  | var k =>
      cases em (n ≤ k) with
      | inl h =>
          simp_all only [incre, ↓reduceIte, 
            le_trans h (Nat.le_add_right k j), var.injEq]
          simp_all only [Nat.add_comm, Nat.add_left_comm]
      | inr h => simp_all only [not_le, incre, if_neg h]
  | abs t' ih => simp_all only [incre]
  | app t₁ t₂ ih₁ ih₂ => simp_all only [incre]

/-- Communitivity of incre. -/
public theorem incre_comm {i j k l t} :
    (incre j (k + l + i) (incre i l t))=
      (incre i l (incre j (k + l) t)) := by
  induction t generalizing l with
  | var n =>
      cases em (k + l ≤ n) with
      | inl h =>
          have : l ≤ n := le_trans (Nat.le_add_left _ _) h
          simp_all only [incre, ↓reduceIte, 
            Nat.add_le_add_iff_right, 
            le_trans this (Nat.le_add_right _ _), var.injEq]
          simp only [Nat.add_comm, Nat.add_left_comm]
      | inr h =>
          simp only [incre, if_neg h]
          cases em (l ≤ n) with
          | inl h' =>
              simp_all only [not_le, ↓reduceIte, incre,
                Nat.add_le_add_iff_right, ite_eq_right_iff]
              intro hk
              have : n < n := Nat.lt_of_lt_of_le h hk
              exact (Nat.lt_irrefl n this).elim
          | inr h' =>
              simp_all only [not_le, if_neg h', incre,
                ite_eq_right_iff, var.injEq, Nat.add_eq_left]
              intro hk
              have hl : l ≤ n := by omega
              exact (Nat.lt_irrefl n
                (Nat.lt_of_lt_of_le h' hl)).elim
  | abs t' ih => 
      simp_all only [Nat.add_comm, incre, Nat.add_assoc]
  | app t₁ t₂ ih₁ ih₂ => simp_all only [incre]

public theorem incre_comm_zero {n s} :
    incre 1 (n + 1) (incre 1 0 s) =
      incre 1 0 (incre 1 n s) := by
  simpa only [Nat.add_zero] 
    using (incre_comm (i := 1) (l := 0) (j := 1) (k := n) (t := s))

@[simp] public theorem abs_sub_zero {t n s} :
    ((λ.t).sub n s) = λ.(t.sub (n + 1) (incre 1 0 s)) := by
  simp_all only [sub, subst, decre, incre_comm_zero]

private lemma incre_sub_var {i l n k s} :
    (incre i (l + n + 1) 𝕧 k).sub n (incre i (l + n) s) =
    incre i (l + n) ((𝕧 k).sub n s) := by
  cases em (k = n) with
  | inl h =>
      have : ¬ (l + n + 1 ≤ n) := by omega
      simp_all only [not_le, sub, incre, if_neg this, subst, 
        ↓reduceIte, decre_incre_elim]
  | inr h =>
      cases em (l + n + 1 ≤ k) with
      | inl h' =>
          have : ¬(k + i = n) := by omega
          have : n + 1 ≤ k + i := by omega
          have : n + 1 ≤ k := by omega
          have : l + n ≤ k - 1 := by omega
          have : k + i - 1 = k - 1 + i := by omega
          simp_all only [sub, incre, ↓reduceIte, 
            subst, decre]
      | inr h' =>
          simp_all only [not_le, sub, incre, if_neg h',
            subst, ↓reduceIte, decre]
          cases em (n < k) with
          | inl h'' =>
              have : (n + 1 ≤ k) := by omega
              simp_all only [↓reduceIte, incre, 
                right_eq_ite_iff, var.injEq, Nat.left_eq_add]
              intro h
              have : ¬(l + n ≤ k - 1) := by omega
              exact (this h).elim
          | inr h'' =>
              have : ¬(n + 1 ≤ k) := by omega
              simp_all only [not_lt, not_le, if_neg, incre, 
                right_eq_ite_iff, var.injEq, Nat.left_eq_add]
              intro h
              have : ¬(l + n ≤ k) := by omega
              exact (this h).elim

/-- The communitivity between sub and incre for free var. -/
@[simp] public theorem incre_sub {i l n t s} :
    ((incre i (l + n + 1) t).sub n (incre i (l + n) s)) =
    (incre i (l + n) (t.sub n s)) := by
  induction t generalizing l n s with
  | var k => exact incre_sub_var
  | abs t' ih =>
      simpa only [sub, ← incre_comm, incre, subst, 
        Nat.add_zero, ← incre_comm_zero, decre, abs.injEq] 
        using ih
  | app t₁ t₂ ih₁ ih₂ => simp_all only [sub, incre, subst, decre]

private lemma subst_zero_incre {n t u} :
    subst n t (incre 1 n u) = incre 1 n u := by
  induction u generalizing n t with
  | var k =>
      cases em (n ≤ k) with
      | inl h =>
          simp_all only [incre, ↓reduceIte, subst, ite_eq_right_iff]
          intro; omega
      | inr h =>
          simp_all only [not_le, incre, if_neg h,
            subst, ite_eq_right_iff]
          intro; omega
  | abs t ih => simp_all only [incre, subst]
  | app t v iht ihv => simp_all only [incre, subst]

private lemma sub_incre_same {u r m} :
    ((incre 1 m u).sub m r) = u := by
  simp_all only [sub, subst_zero_incre, decre_incre_elim]

@[simp] public theorem sub_lift_zero {i t n u} :
    ((incre 1 i t).sub (n + i + 1) (incre 1 i u)) =
      incre 1 i (t.sub (n + i) u) := by
  induction t generalizing n u i with
  | var k =>
      cases em (k = n + i) with
      | inl hk => 
          simp_all only [sub, incre, Nat.le_add_left, 
            ↓reduceIte, subst, decre_incre_elim]
      | inr hk =>
        cases em (k < n + i) with
          | inl hlt =>
              have hlt' : k + 1 < n + i + 1 := by omega
              have hnlt : ¬(n + i + 1 ≤ k) := by omega
              simp only [sub, incre, subst]
              cases em (i ≤ k) with
              | inl hlt' => 
                  simp_all only [Nat.add_lt_add_iff_right, 
                    not_le, ↓reduceIte, subst, 
                    Nat.add_right_cancel_iff, decre,
                    Nat.add_le_add_iff_right, 
                    Nat.add_one_sub_one, if_neg, incre]
              | inr hlt' =>
                  have h' : ¬(k = n + i + 1) := by omega
                  simp_all only [Nat.add_lt_add_iff_right, 
                    not_le, if_neg, subst, ↓reduceIte, 
                    decre, incre, ite_eq_right_iff, 
                    var.injEq]
                  intro h
                  have : ¬(n + i + 1 + 1 ≤ k) := by omega
                  exact (this h).elim
          | inr hlt =>
              have hle : i ≤ k := by omega
              have hgt : n + i + 1 ≤ k := by omega
              have hlt : i ≤ k - 1 := by omega
              simp_all only [not_lt, sub, incre, ↓reduceIte, 
                subst, Nat.add_right_cancel_iff, decre, 
                Nat.add_le_add_iff_right, 
                Nat.add_one_sub_one, var.injEq]
              exact by omega
  | abs t ih =>
      simpa only [sub, incre, subst, 
        ← incre_comm_zero, decre, abs.injEq] 
        using (ih (i := i + 1) (n := n) (u := incre 1 0 u))
  | app t₁ t₂ ih₁ ih₂ => simp_all only [sub, incre, subst, decre]

private lemma sub_comm_var {k n m u s} :
    (((𝕧 k).sub ((n + m) + 1) (incre 1 m u)).sub m (s.sub (n + m) u))
    = (((𝕧 k).sub m s).sub (n + m) u) := by
  cases em (k = n + m + 1) with
  | inl hk =>
      have : ¬(n + m + 1 = m) := by omega
      have : m + 1 ≤ n + m + 1 := by omega
      simp_all only [sub, subst, ↓reduceIte, 
        decre_incre_elim, subst_zero_incre, decre,
        Nat.add_one_sub_one]
  | inr hk =>
      cases em (k = m) with
      | inl hkm =>
          have : ¬(n + m + 1 + 1 ≤ m) := by omega
          simp_all only [sub, subst, ↓reduceIte, 
            decre, decre_incre_elim]
      | inr hkm =>
          have : ¬(k - 1 = n + m) := by omega
          cases em (n + m + 1 + 1 ≤ k) with
          | inl hlt =>
              have : ¬(k - 1 = m) := by omega
              have : m + 1 ≤ k := by omega
              have : m + 1 ≤ k - 1 := by omega
              simp_all only [sub, subst, ↓reduceIte, decre,
                left_eq_ite_iff, var.injEq]
              exact by omega
          | inr hlt =>
              cases em (m + 1 ≤ k) with
              | inl hlt =>
                  simp_all only [not_le, sub, subst, 
                    ↓reduceIte, decre, if_neg, 
                    right_eq_ite_iff, var.injEq]
                  intro h
                  have nh : ¬(n + m < k - 1) := by omega
                  exact (nh h).elim
              | inr hlt =>
                  have hneq : ¬(k = n + m) := by omega
                  have hnlt : ¬(m < k) := by omega
                  simp_all only [sub, subst, not_lt, subst,
                    ↓reduceIte, decre, right_eq_ite_iff, 
                    var.injEq]
                  intro h
                  have nh : ¬(n + m < k) := by omega
                  exact (nh h).elim

public theorem sub_comm {t : Term} {n m s u} :
    ((t.sub ((n + m) + 1) (incre 1 m u)).sub m (s.sub (n + m) u))
    = ((t.sub m s).sub (n + m) u) := by
  induction t generalizing n m s u with
  | var k => exact sub_comm_var
  | abs t' ih =>
      have : ∀ k, (incre 1 0 (decre 1 k (subst k (incre 1 k u) s))) =
          (decre 1 (k + 1) (subst (k + 1) (incre 1 (k + 1)
          (incre 1 0 u)) (incre 1 0 s))) := by
        intro k
        simpa only [sub, Nat.add_zero] 
          using (sub_lift_zero (t := s) (n := k) (u := u) 
                  (i := 0)).symm
      simpa only [sub, subst, ← incre_comm_zero, 
        decre, this, abs.injEq] 
        using (ih (n := n) 
          (m := m + 1) (u := incre 1 0 u) (s := incre 1 0 s))
  | app t₁ t₂ ih₁ ih₂ => simp_all only [sub, subst, decre]

public theorem sub_sub_incre {t : Term} {n k u s} :
    ((t.sub (n + 1) (incre (1 + k) 0 u)).sub 0 (s.sub n (incre k 0 u)))
    = ((t.sub 0 s).sub n (incre k 0 u)) := by
  have h' :
      ((t.sub (n + 1) (incre 1 0 (incre k 0 u))).sub 0
          ((s.sub n (incre k 0 u)))) =
        ((t.sub 0 s).sub n (incre k 0 u)) := by
    simpa only [sub, incre_same_bound_elim, Nat.add_zero] 
      using (sub_comm (t := t) (u := incre k 0 u) (s := s) 
        (n := n) (m := 0))
  simpa only [sub, incre_same_bound_elim] using h'


end Term
end Lambda
