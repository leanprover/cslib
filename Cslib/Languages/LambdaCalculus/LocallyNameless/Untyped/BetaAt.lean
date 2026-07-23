/-
Copyright (c) 2026 Maximiliano Onofre Martínez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maximiliano Onofre Martínez
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.CallByName

/-! # Redex Positions

This module defines β-reduction at a given redex position and proves its basic properties.

## Reference

* [M. Copes, *A machine-checked proof of the Standardization Theorem in λ-calculus*][Copes2018]

-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- The number of β-redexes occurring in a term. -/
@[grind]
def countRedexes : Term Var → Nat
| fvar _        => 0
| bvar _        => 0
| abs m         => countRedexes m
| app (abs m) n => countRedexes m + countRedexes n + 1
| app m n       => countRedexes m + countRedexes n

/-- `BetaAt i M N` reduces the redex at position `i` of `M` to obtain `N`;
    positions are counted from left to right. -/
inductive BetaAt : Nat → Term Var → Term Var → Prop
/-- The outermost redex sits at position `0`. -/
| outer : LC (abs M) → LC N → BetaAt 0 (app (abs M) N) (M ^ N)
/-- Reducing the operator advances the position by one when the operator is an abstraction. -/
| appL : BetaAt i M M' → BetaAt (i + if IsAbs M then 1 else 0) (app M N) (app M' N)
/-- Reducing the operand adds the operator's redex count, plus one when it is an abstraction. -/
| appR : BetaAt i M M' →
    BetaAt (i + countRedexes N + if IsAbs N then 1 else 0) (app N M) (app N M')
/-- Reducing under a binder keeps the position. -/
| abs (xs : Finset Var) :
    (∀ x ∉ xs, BetaAt i (M ^ fvar x) (M' ^ fvar x)) → BetaAt i (abs M) (abs M')

variable {L L' M M' N N' P : Term Var} {a b i m n : Nat}

/-- Reducing a non-abstraction operator keeps the position. -/
lemma BetaAt.appNoAbsL (h : BetaAt i M M') (hna : ¬IsAbs M) :
    BetaAt i (app M N) (app M' N) := by
  simpa [if_neg hna] using h.appL

/-- Reducing an abstraction operator advances the position by one. -/
lemma BetaAt.appAbsL (h : BetaAt i M M') (ha : IsAbs M) :
    BetaAt (i + 1) (app M N) (app M' N) := by
  simpa [if_pos ha] using h.appL

/-- Reducing the operand adds the redex count of a non-abstraction operator. -/
lemma BetaAt.appNoAbsR (h : BetaAt i M M') (hna : ¬IsAbs N) :
    BetaAt (i + countRedexes N) (app N M) (app N M') := by
  simpa [if_neg hna] using h.appR (N := N)

/-- Reducing the operand adds the redex count of an abstraction operator, plus one. -/
lemma BetaAt.appAbsR (h : BetaAt i M M') (ha : IsAbs N) :
    BetaAt (i + countRedexes N + 1) (app N M) (app N M') := by
  simpa [if_pos ha] using h.appR (N := N)

/-- Opening with a free variable preserves the number of redexes. -/
lemma countRedexes_openRec_fvar (M : Term Var) (k : Nat) (x : Var) :
    countRedexes (M⟦k ↝ fvar x⟧) = countRedexes M := by
  induction M generalizing k with
  | bvar j => simp only [openRec_bvar]; split <;> rfl
  | fvar => rfl
  | abs M ih => grind [openRec_abs]
  | app L R ihL ihR => cases L <;> grind [openRec_bvar, openRec_app, openRec_abs]

/-- Opening the outermost binder with a free variable preserves the number of redexes. -/
lemma countRedexes_open_fvar (M : Term Var) (x : Var) :
    countRedexes (M ^ fvar x) = countRedexes M :=
  countRedexes_openRec_fvar M 0 x

/-- An application has at least as many redexes as its operator and operand combined. -/
lemma countRedexes_app_le (M N : Term Var) :
    countRedexes M + countRedexes N ≤ countRedexes (app M N) := by
  cases M <;> grind

/-- An application with an abstraction operator has one more redex than its parts. -/
lemma countRedexes_app_abs {M : Term Var} (ha : IsAbs M) (N : Term Var) :
    countRedexes (app M N) = countRedexes M + countRedexes N + 1 := by
  cases ha
  grind

/-- Contracting a redex of an abstraction yields an abstraction. -/
lemma BetaAt.isAbs_r (h : BetaAt i M N) (ha : IsAbs M) : IsAbs N := by
  cases ha
  cases h
  exact .abs _

/-- The source of a Call-by-Name step is never an abstraction. -/
lemma cbn_not_isAbs (h : M ⭢ₙ N) : ¬IsAbs M := by
  intro ha
  cases ha
  trivial

/-- A single Call-by-Name step contracts the redex at position `0`. -/
lemma BetaAt.of_cbn_step (h : M ⭢ₙ N) : BetaAt 0 M N := by
  induction h with
  | base h_beta =>
    cases h_beta with
    | beta lc_M lc_N => exact .outer lc_M lc_N
  | app _ step_M ih => exact .appNoAbsL ih (cbn_not_isAbs step_M)

/-- Renaming a free variable preserves the number of redexes. -/
lemma countRedexes_subst_fvar [DecidableEq Var] (M : Term Var) (x y : Var) :
    countRedexes (M[x := fvar y]) = countRedexes M := by
  induction M with
  | fvar z => simp only [subst_fvar]; split <;> rfl
  | bvar => rfl
  | abs M ih => grind
  | app L R ihL ihR => cases L <;> grind

/-- Renaming a free variable preserves being an abstraction. -/
lemma isAbs_subst_fvar [DecidableEq Var] {x y : Var} : IsAbs (M[x := fvar y]) ↔ IsAbs M := by
  cases M <;> grind

/-- A `BetaAt` step is a full β-step. -/
lemma BetaAt.to_step [DecidableEq Var] (h : BetaAt i M N) (lc : LC M) : M ⭢βᶠ N := by
  induction h with
  | outer lc_M lc_N => exact .base (.beta lc_M lc_N)
  | appL _ ih =>
    cases lc with
    | app lc_L lc_R => exact .appR lc_R (ih lc_L)
  | appR _ ih =>
    cases lc with
    | app lc_L lc_R => exact .appL lc_L (ih lc_R)
  | abs xs _ ih =>
    cases lc with
    | abs ys _ h_body =>
      apply Xi.abs (xs ∪ ys)
      intro z hz
      exact ih z (by grind) (h_body z (by grind))

variable [HasFresh Var]

/-- The position of a contracted redex is at most the redex count of the result. -/
lemma BetaAt.le_countRedexes (h : BetaAt i M N) : i ≤ countRedexes N := by
  induction h with
  | outer => exact Nat.zero_le _
  | appL step =>
    split
    · rw [countRedexes_app_abs (step.isAbs_r (by assumption))]
      omega
    · exact le_trans (by omega) (countRedexes_app_le _ _)
  | appR =>
    split
    · rw [countRedexes_app_abs (by assumption)]
      omega
    · exact le_trans (by omega) (countRedexes_app_le _ _)
  | abs xs =>
    have := fresh_exists xs
    grind [countRedexes_open_fvar]

variable [DecidableEq Var]

/-- Renaming a free variable preserves the position of the contracted redex. -/
lemma BetaAt.rename (h : BetaAt i M M') (x y : Var) :
    BetaAt i (M[x := fvar y]) (M'[x := fvar y]) := by
  induction h with
  | outer lc_M lc_N =>
    rw [subst_open x (fvar y) _ _ (.fvar y)]
    exact .outer (subst_lc lc_M (.fvar y)) (subst_lc lc_N (.fvar y))
  | appL _ ih =>
    split
    · exact ih.appAbsL (isAbs_subst_fvar.mpr (by assumption))
    · exact ih.appNoAbsL (mt isAbs_subst_fvar.mp (by assumption))
  | appR _ ih =>
    rw [← countRedexes_subst_fvar _ x y]
    split
    · exact ih.appAbsR (isAbs_subst_fvar.mpr (by assumption))
    · exact ih.appNoAbsR (mt isAbs_subst_fvar.mp (by assumption))
  | abs =>
    apply BetaAt.abs <| free_union [fv] Var
    grind

/-- Contracting a redex preserves local closure. -/
lemma BetaAt.lc_r (h : BetaAt i M M') (lc : LC M) : LC M' := by
  induction h with
  | outer lc_M lc_N => exact beta_lc lc_M lc_N
  | appL _ ih =>
    cases lc with
    | app lc_L lc_R => exact .app (ih lc_L) lc_R
  | appR _ ih =>
    cases lc with
    | app lc_L lc_R => exact .app lc_L (ih lc_R)
  | abs xs _ ih =>
    cases lc with
    | abs ys _ h_body =>
      apply LC.abs (xs ∪ ys)
      intro z hz
      exact ih z (by grind) (h_body z (by grind))

/-- Closing a variable and abstracting preserves the position of the contracted redex. -/
lemma BetaAt.abs_close {x : Var} (h : BetaAt i M M') (lc : LC M) :
    BetaAt i (M⟦0 ↜ x⟧.abs) (M'⟦0 ↜ x⟧.abs) := by
  apply BetaAt.abs ∅
  intro z _
  have lc' := h.lc_r lc
  have hr : BetaAt i (M[x := fvar z]) (M'[x := fvar z]) := h.rename x z
  grind

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
