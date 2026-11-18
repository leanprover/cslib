/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CSLib Contributors
-/

import Cslib.Foundations.Relation.Preserves
import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.Safety
import Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.StrongNorm
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiSubst

/-! # Locally Nameless λ-Calculus and STLC Capture-Avoiding Substitution Tests

Test and specification suite for capture-avoiding substitution, variable opening/closing, binder
shadowing, full β-reduction, and simply typed λ-calculus (`Stlc`) typing and type preservation
using the locally nameless representation (CSLib Issue #711).

Covers classic capture-avoidance benchmarks from Pierce's *Types and Programming Languages*
(§5.3.4), Charguéraud's *The Locally Nameless Representation*, and Weirich's `lambda-n-ways`
benchmark suite.
-/

namespace CslibTests.LocallyNamelessStlc

open Cslib LambdaCalculus LocallyNameless Untyped Term Stlc Typing Relation
open scoped Term Stlc Context

/-! ## Concrete Variable Names and Binder Helper -/

/-- Concrete free variable `x` (`0`). -/
abbrev x : ℕ := 0

/-- Concrete free variable `y` (`1`). -/
abbrev y : ℕ := 1

/-- Concrete free variable `z` (`2`). -/
abbrev z : ℕ := 2

/-- Concrete free variable `w` (`3`). -/
abbrev w : ℕ := 3

/-- Concrete free variable `f` (`4`). -/
abbrev f : ℕ := 4

/-- Concrete free variable `nVar` (`5`). -/
abbrev nVar : ℕ := 5

/-- Concrete free variable `mVar` (`6`). -/
abbrev mVar : ℕ := 6

/-- Smart constructor `λv. body` in locally nameless form, closing `v` at index `0` before `abs`. -/
def lam {Var : Type*} [DecidableEq Var] (v : Var) (body : Term Var) : Term Var :=
  (body⟦0 ↜ v⟧).abs

/-! ## 1. Locally Nameless Representation & Opening/Closing Round-Trips -/

/-- Identity combinator `λx. x` constructed by closing `x`. -/
def idTerm : Term ℕ := ((fvar x)⟦0 ↜ x⟧).abs

/-- `λx. x` elaborates to the canonical de Bruijn representation `abs (bvar 0)`. -/
theorem idTerm_eq : idTerm = Term.abs (bvar 0) := rfl

/-- Canonical α-equivalence: `λx. x` and `λy. y` are syntactically identical in locally nameless
syntax. -/
theorem idTerm_alpha_eq : ((fvar x)⟦0 ↜ x⟧).abs = ((fvar y)⟦0 ↜ y⟧).abs := rfl

/-- Constant (`K`) combinator `λx. λy. x` constructed by closing `y` then `x`. -/
def kTerm : Term ℕ := (((fvar x)⟦0 ↜ y⟧).abs⟦0 ↜ x⟧).abs

/-- `λx. λy. x` elaborates to `abs (abs (bvar 1))`. -/
theorem kTerm_eq : kTerm = Term.abs (Term.abs (bvar 1)) := rfl

/-- `S` combinator `λx. λy. λz. x z (y z)` constructed via nested `closeRec` (`⟦0 ↜ ·⟧`). -/
def sTerm : Term ℕ :=
  ((((app (app (fvar x) (fvar z)) (app (fvar y) (fvar z)))⟦0 ↜ z⟧).abs⟦0 ↜ y⟧).abs⟦0 ↜ x⟧).abs

/-- `λx. λy. λz. x z (y z)` elaborates to the expected de Bruijn indices `2`, `1`, `0`. -/
theorem sTerm_eq :
    sTerm = Term.abs (Term.abs (Term.abs
      (app (app (bvar 2) (bvar 0)) (app (bvar 1) (bvar 0))))) := rfl

/-- Church numeral `0` (`λf. λx. x`). -/
def churchZero : Term ℕ := (((fvar x)⟦0 ↜ x⟧).abs⟦0 ↜ f⟧).abs

/-- `churchZero` elaborates to `abs (abs (bvar 0))`. -/
theorem churchZero_eq : churchZero = Term.abs (Term.abs (bvar 0)) := rfl

/-- Church numeral `1` (`λf. λx. f x`). -/
def churchOne : Term ℕ := (((app (fvar f) (fvar x))⟦0 ↜ x⟧).abs⟦0 ↜ f⟧).abs

/-- `churchOne` elaborates to `abs (abs (app (bvar 1) (bvar 0)))`. -/
theorem churchOne_eq : churchOne = Term.abs (Term.abs (app (bvar 1) (bvar 0))) := rfl

/-- Church numeral `2` (`λf. λx. f (f x)`). -/
def churchTwo : Term ℕ :=
  (((app (fvar f) (app (fvar f) (fvar x)))⟦0 ↜ x⟧).abs⟦0 ↜ f⟧).abs

/-- `churchTwo` elaborates to `abs (abs (app (bvar 1) (app (bvar 1) (bvar 0))))`. -/
theorem churchTwo_eq :
    churchTwo = Term.abs (Term.abs (app (bvar 1) (app (bvar 1) (bvar 0)))) := rfl

/-- Closing `x` replaces matching free occurrences with `bvar`s shifted by binder depth while
leaving distinct free variables (`y`) and existing bound variables (`bvar 0`) untouched. -/
theorem close_depth_and_distinct :
    (app (fvar x) (Term.abs (app (fvar x) (app (fvar y) (bvar 0)))))⟦0 ↜ x⟧ =
      app (bvar 0) (Term.abs (app (bvar 1) (app (fvar y) (bvar 0)))) := rfl

/-- Opening then closing with a fresh free variable recovers the original body (`open_close_var`).
-/
theorem open_then_close_roundtrip :
    (((app (fvar y) (bvar 0)) ^ fvar x) ^* x) = app (fvar y) (bvar 0) :=
  (open_close_var x (app (fvar y) (bvar 0)) (by decide)).symm

/-- Freshness in `open_close_var` is essential: opening then closing with `x` when `x` already
occurs free captures the pre-existing `fvar x` as `bvar 0`. -/
theorem open_then_close_clashing_ne :
    (((app (fvar x) (bvar 0)) ^ fvar x) ^* x) ≠ app (fvar x) (bvar 0) := by
  decide

/-- Closing then opening a locally closed term recovers the original term (`close_open`). -/
theorem close_then_open_roundtrip :
    let t : Term ℕ := app (fvar x) (Term.abs (app (fvar x) (bvar 0)))
    (t ^* x) ^ fvar x = t :=
  close_open x _ 0 (by rw [← lcAt_iff_LC]; decide)

/-- Well-formed closed combinators satisfy `LC`. -/
theorem lc_combinators : LC idTerm ∧ LC kTerm ∧ LC sTerm ∧ LC churchTwo := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [← lcAt_iff_LC]; decide)

/-- Open terms without dangling `bvar`s satisfy `LC`, including abstractions over free variables. -/
theorem lc_open_terms : LC (app (fvar x) idTerm) ∧ LC (Term.abs (fvar x)) := by
  refine ⟨?_, ?_⟩ <;> (rw [← lcAt_iff_LC]; decide)

/-- Dangling bound variable `bvar 0` is not locally closed. -/
theorem not_lc_bvar_zero : ¬ LC (bvar 0 : Term ℕ) := by
  rintro ⟨⟩

/-- `abs (bvar 1)` has a bound variable escaping its single binder and is not locally closed. -/
theorem not_lc_abs_bvar_one : ¬ LC (Term.abs (bvar 1) : Term ℕ) := by
  rw [← lcAt_iff_LC]
  decide

/-- Nested abstraction `abs (abs (app (bvar 0) (bvar 2)))` fails `LC` due to escaping `bvar 2`. -/
theorem not_lc_nested_escaping_bvar :
    ¬ LC (Term.abs (Term.abs (app (bvar 0) (bvar 2))) : Term ℕ) := by
  rw [← lcAt_iff_LC]
  decide

/-- An application containing a dangling `bvar 0` is not locally closed. -/
theorem not_lc_app_bvar_zero : ¬ LC (app (fvar x) (bvar 0)) := by
  rw [← lcAt_iff_LC]
  decide

/-! ## 2. Capture-Avoiding Substitution (`lambda-n-ways` & TAPL Corner Cases) -/

/-- A free variable is in normal form under single-step full β-reduction. -/
theorem not_step_fvar {Var : Type*} (v : Var) (u : Term Var) : ¬ ((fvar v) ⭢βᶠ u) := by
  suffices ∀ t, t ⭢βᶠ u → t ≠ fvar v from fun h => this (fvar v) h rfl
  rintro t (⟨⟨⟩⟩ | _ | _ | _) <;> rintro ⟨⟩

/-- Multi-step full β-reduction starting from `fvar v` can only reach `fvar v`. -/
theorem steps_fvar_eq {Var : Type*} {v : Var} {u : Term Var} (h : (fvar v) ↠βᶠ u) :
    u = fvar v := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact False.elim (not_step_fvar v _ (ih ▸ hstep))

/-- By confluence of full β-reduction, if `M ↠βᶠ fvar v₁` and `v₂ ≠ v₁`, then `M` cannot reduce to
`fvar v₂`. -/
theorem not_steps_fvar_of_steps_fvar {Var : Type*} [HasFresh Var]
    {M : Term Var} {v₁ v₂ : Var} (hred : M ↠βᶠ fvar v₁) (hne : v₂ ≠ v₁) :
    ¬ (M ↠βᶠ fvar v₂) := by
  classical
  intro hred₂
  obtain ⟨u, hu₁, hu₂⟩ := confluent_fullBeta hred hred₂
  have eq₁ : u = fvar v₁ := steps_fvar_eq hu₁
  have eq₂ : u = fvar v₂ := steps_fvar_eq hu₂
  rw [eq₁] at eq₂
  injection eq₂ with hvv
  exact hne hvv.symm

/-- `λy. x` is represented as `abs (fvar x)` when `y ≠ x`. -/
theorem lam_y_fvar_x_eq : lam y (fvar x) = Term.abs (fvar x) := rfl

/-- **No variable capture under binder**: `(λy. x)[x := y] = abs (fvar y)`, where `fvar y` remains
free rather than becoming bound `bvar 0`. -/
theorem subst_no_capture_under_binder :
    (Term.abs (fvar x))[x := fvar y] = Term.abs (fvar y) := rfl

/-- `y` remains in the free-variable set after `(λy. x)[x := y]`, unlike captured `abs (bvar 0)`. -/
theorem subst_no_capture_fv :
    ((Term.abs (fvar x))[x := fvar y]).fv = {y} ∧ (Term.abs (bvar 0) : Term ℕ).fv = ∅ :=
  ⟨rfl, rfl⟩

/-- Opening the body of `(λy. x)[x := y]` with `fvar v` yields `fvar y` for ALL `v` (both `v ≠ y`
and `v = y`), demonstrating that `fvar y` was not captured by `abs`. -/
theorem subst_no_capture_open_body (v : ℕ) :
    ((fvar x)[x := fvar y]) ^ fvar v = fvar y := rfl

/-- Opening the full term `((abs (fvar x))[x := fvar y]) ^ fvar v` leaves `abs (fvar y)` intact for
every `v` (including `v ≠ y` and `v = y`) because `abs (fvar y)` is locally closed. -/
theorem subst_no_capture_open_abs (v : ℕ) :
    ((Term.abs (fvar x))[x := fvar y]) ^ fvar v = Term.abs (fvar y) := rfl

/-- Applying `(λy. x)[x := y]` to `fvar v` reduces in one β-step to `fvar y` for EVERY `v`
(both when `v ≠ y`, such as `v = w`, and when `v = y`). -/
theorem subst_no_capture_beta_to_y (v : ℕ) :
    app ((Term.abs (fvar x))[x := fvar y]) (fvar v) ⭢βᶠ fvar y :=
  Xi.base (Beta.beta (LC.abs ∅ (fvar y) fun _ _ => LC.fvar y) (LC.fvar v))

/-- Contrast: naive variable capture `(λy. y) w` reduces to `w` instead of `y`. -/
theorem naive_capture_beta_to_w :
    app (lam y (fvar y)) (fvar w) ⭢βᶠ fvar w :=
  Xi.base (Beta.beta (LC.abs ∅ (bvar 0) fun u _ => LC.fvar u) (LC.fvar w))

/-- Parametric proof that for any `w' ≠ y'`, `(λy. x)[x := y'] w'` NEVER β-reduces (even in
multiple steps) to `w'`, ruling out variable capture semantically. -/
theorem subst_no_capture_not_steps_arg {Var : Type*} [HasFresh Var] [DecidableEq Var]
    (x' y' w' : Var) (hne : w' ≠ y') :
    ¬ (app ((Term.abs (fvar x'))[x' := fvar y']) (fvar w') ↠βᶠ fvar w') := by
  have hstep : app ((Term.abs (fvar x'))[x' := fvar y']) (fvar w') ⭢βᶠ fvar y' := by
    simp only [subst_abs, subst_fvar, ↓reduceIte]
    exact Xi.base (Beta.beta (LC.abs ∅ (fvar y') fun _ _ => LC.fvar y') (LC.fvar w'))
  exact not_steps_fvar_of_steps_fvar (ReflTransGen.single hstep) hne

/-- Concrete specialization: `((abs (fvar x))[x := fvar y]).app (fvar w)` does not reduce to `w`. -/
theorem subst_no_capture_not_steps_w :
    ¬ (app ((Term.abs (fvar x))[x := fvar y]) (fvar w) ↠βᶠ fvar w) :=
  subst_no_capture_not_steps_arg x y w (by decide)

/-- **TAPL §5.3.4 benchmark term** `λy. x y`, constructed by closing `y`. -/
def taplTerm : Term ℕ := ((app (fvar x) (fvar y))⟦0 ↜ y⟧).abs

/-- `taplTerm` elaborates to `abs (app (fvar x) (bvar 0))`. -/
theorem taplTerm_eq : taplTerm = Term.abs (app (fvar x) (bvar 0)) := rfl

/-- **TAPL §5.3.4 capture-avoidance test**: `(λy. x y)[x := y z]` keeps the substituted `y` free
(`fvar y`) while preserving the bound `y` (`bvar 0`), without needing binder α-renaming. -/
theorem tapl_5_3_4_subst :
    taplTerm[x := app (fvar y) (fvar z)] =
      Term.abs (app (app (fvar y) (fvar z)) (bvar 0)) := rfl

/-- Applying `(λy. x y)[x := y z]` to `w` β-reduces in one step to `(y z) w`. -/
theorem tapl_5_3_4_beta :
    app (taplTerm[x := app (fvar y) (fvar z)]) (fvar w) ⭢βᶠ
      app (app (fvar y) (fvar z)) (fvar w) := by
  have hlc_abs : LC (Term.abs (app (app (fvar y) (fvar z)) (bvar 0))) := by
    rw [← lcAt_iff_LC]
    decide
  exact Xi.base (Beta.beta hlc_abs (LC.fvar w))

/-- **Binder shadowing**: `(λx. x)[x := z] = λx. x`. -/
theorem subst_shadow_id :
    (((fvar x)⟦0 ↜ x⟧).abs)[x := fvar z] = Term.abs (bvar 0) := rfl

/-- Substitution replaces free outer `x` while leaving shadowed inner `λx. x` untouched. -/
theorem subst_outer_free_inner_shadowed :
    (app (fvar x) (((fvar x)⟦0 ↜ x⟧).abs))[x := fvar z] =
      app (fvar z) (Term.abs (bvar 0)) := rfl

/-- **Nested binder shadowing** `λx. x (λx. x)`: inner `x` binds to the inner `abs` (`bvar 0`) and
outer `x` binds to the outer `abs` (`bvar 0`). -/
def nestedShadow : Term ℕ :=
  ((app (fvar x) (((fvar x)⟦0 ↜ x⟧).abs))⟦0 ↜ x⟧).abs

/-- `nestedShadow` elaborates to `abs (app (bvar 0) (abs (bvar 0)))` and is invariant under
substituting `x`. -/
theorem nestedShadow_eq_and_subst :
    nestedShadow = Term.abs (app (bvar 0) (Term.abs (bvar 0))) ∧
      nestedShadow[x := fvar z] = nestedShadow := ⟨rfl, rfl⟩

/-- Applying `λx. x (λx. x)` to `y` substitutes `y` only for the outer `x`, leaving the inner
shadowed `λx. x` intact. -/
theorem nestedShadow_beta :
    app nestedShadow (fvar y) ⭢βᶠ app (fvar y) (Term.abs (bvar 0)) := by
  have hlc : LC nestedShadow := by
    rw [← lcAt_iff_LC]
    decide
  exact Xi.base (Beta.beta hlc (LC.fvar y))

/-- Multi-binder shadowing `λx. λy. λx. x y` binds the inner `x` to `bvar 0` and `y` to `bvar 1`,
leaving the outer `x` binder unused. -/
theorem nested_shadow_three_binders :
    lam x (lam y (lam x (app (fvar x) (fvar y)))) =
      Term.abs (Term.abs (Term.abs (app (bvar 0) (bvar 1)))) := rfl

/-- **Substitution commutation (`subst_comm`)**: when `x ≠ y` and `x ∉ u.fv`, substituting `s` for
`x` then `u` for `y` equals substituting `u` for `y` then `s[y := u]` for `x`. -/
theorem subst_comm {Var : Type*} [DecidableEq Var] (t s u : Term Var) (x' y' : Var)
    (hne : x' ≠ y') (hfresh : x' ∉ u.fv) :
    t[x' := s][y' := u] = t[y' := u][x' := s[y' := u]] := by
  induction t with
  | bvar _ => rfl
  | fvar v => grind [subst_fresh]
  | app _ _ ihl ihr => simp only [subst_app, ihl, ihr]
  | abs _ ihm => simp only [subst_abs, ihm]

/-- Concrete higher-order substitution commutation test where `s` contains free variable `y` and `t`
binds `z`. -/
theorem subst_comm_concrete :
    let t := lam z (app (fvar x) (app (fvar y) (fvar z)))
    let s := lam w (app (fvar y) (fvar w))
    let u := app (fvar z) (fvar w)
    t[x := s][y := u] = t[y := u][x := s[y := u]] ∧
      t[x := s][y := u] =
        Term.abs (app (Term.abs (app (app (fvar z) (fvar w)) (bvar 0)))
          (app (app (fvar z) (fvar w)) (bvar 0))) :=
  ⟨subst_comm _ _ _ x y (by decide) (by decide), rfl⟩

/-- Freshness side condition `x ∉ u.fv` in `subst_comm` is necessary: when `u = fvar x`, the two
substitution orders disagree on `t = fvar y`. -/
theorem subst_comm_counterexample_when_not_fresh :
    (fvar y)[x := fvar z][y := fvar x] ≠
      (fvar y)[y := fvar x][x := (fvar z)[y := fvar x]] := by
  decide

/-- **Sequential vs simultaneous substitution**: sequential `[x := y][y := z]` collapses both `x`
and `y` to `z`, whereas simultaneous substitution via a fresh intermediate variable `w` swaps `x`
and `y`. -/
theorem sequential_vs_swap_concrete :
    (app (fvar x) (fvar y))[x := fvar y][y := fvar z] = app (fvar z) (fvar z) ∧
      (app (fvar x) (lam z (app (fvar y) (fvar z))))[x := fvar w][y := fvar x][w := fvar y] =
        app (fvar y) (lam z (app (fvar x) (fvar z))) :=
  ⟨rfl, rfl⟩

/-- `multiSubst` applies environment substitutions right-to-left (`[⟨y, fvar z⟩, ⟨x, fvar y⟩]`
evaluates `M[x := fvar y][y := fvar z]`), whereas ordering `[⟨w, fvar y⟩, ⟨y, fvar x⟩, ⟨x, fvar w⟩]`
swaps `x` and `y`. -/
theorem multiSubst_order_test :
    multiSubst [⟨y, fvar z⟩, ⟨x, fvar y⟩] (app (fvar x) (fvar y)) = app (fvar z) (fvar z) ∧
      multiSubst [⟨w, fvar y⟩, ⟨y, fvar x⟩, ⟨x, fvar w⟩] (app (fvar x) (fvar y)) =
        app (fvar y) (fvar x) :=
  ⟨rfl, rfl⟩

/-- Swapping two free variables `x'` and `y'` in any term `t` using a fresh variable computed via
`HasFresh.fresh`. -/
def swapVars {Var : Type*} [DecidableEq Var] [HasFresh Var] (x' y' : Var) (t : Term Var) :
    Term Var :=
  let tmp := fresh (t.fv ∪ {x', y'})
  t[x' := fvar tmp][y' := fvar x'][tmp := fvar y']

/-- Auxiliary lemma characterizing three-step swap with any fresh variable `tmp`. -/
theorem swapAux_eq {Var : Type*} [DecidableEq Var] (x' y' tmp : Var) (t : Term Var)
    (hnt : tmp ∉ t.fv) (hnx : tmp ≠ x') (hny : tmp ≠ y') :
    (t[x' := fvar tmp][y' := fvar x'][tmp := fvar y']).fv ⊆ (t.fv ∪ {x', y'}) ∧
      (t[x' := fvar tmp][y' := fvar x'][tmp := fvar y'])[x' := fvar tmp][y' := fvar x'][tmp :=
        fvar y'] = t := by
  induction t with
  | bvar _ => grind
  | fvar _ => grind
  | app l r ihl ihr =>
    simp only [fv, Finset.mem_union, not_or] at hnt
    obtain ⟨hl_fv, hl_eq⟩ := ihl hnt.1
    obtain ⟨hr_fv, hr_eq⟩ := ihr hnt.2
    simp only [subst_app, fv, hl_eq, hr_eq, and_true]
    exact Finset.union_subset (hl_fv.trans (by grind)) (hr_fv.trans (by grind))
  | abs m ihm =>
    obtain ⟨hm_fv, hm_eq⟩ := ihm hnt
    simpa only [subst_abs, fv] using ⟨hm_fv, congrArg Term.abs hm_eq⟩

/-- Variable swapping via `HasFresh` is an involution on all locally nameless terms. -/
theorem swapVars_involutive {Var : Type*} [DecidableEq Var] [HasFresh Var]
    (x' y' : Var) (t : Term Var) :
    swapVars x' y' (swapVars x' y' t) = t := by
  unfold swapVars
  set s₁ := t.fv ∪ {x', y'}
  have hf₁ : fresh s₁ ∉ s₁ := fresh_notMem s₁
  have hnt₁ : fresh s₁ ∉ t.fv := by grind
  have hnx₁ : fresh s₁ ≠ x' := by grind
  have hny₁ : fresh s₁ ≠ y' := by grind
  set t' := t[x' := fvar (fresh s₁)][y' := fvar x'][fresh s₁ := fvar y']
  set s₂ := t'.fv ∪ {x', y'}
  have hf₂ : fresh s₂ ∉ s₂ := fresh_notMem s₂
  have hnt₂ : fresh s₂ ∉ t'.fv := by grind
  have hnx₂ : fresh s₂ ≠ x' := by grind
  have hny₂ : fresh s₂ ≠ y' := by grind
  have hsame : ∀ (a b : Var) (s : Term Var),
      a ∉ s.fv → a ≠ x' → a ≠ y' → b ∉ s.fv → b ≠ x' → b ≠ y' →
      s[x' := fvar a][y' := fvar x'][a := fvar y'] =
        s[x' := fvar b][y' := fvar x'][b := fvar y'] := by
    intro a b s ha hax hay hb hbx hby
    induction s with
    | bvar _ => rfl
    | fvar _ => grind
    | app l r ihl ihr =>
      simp only [fv, Finset.mem_union, not_or] at ha hb
      simp only [subst_app, ihl ha.1 hb.1, ihr ha.2 hb.2]
    | abs m ihm =>
      simp only [subst_abs, ihm ha hb]
  obtain ⟨ht'_fv, ht'_inv⟩ := swapAux_eq x' y' (fresh s₁) t hnt₁ hnx₁ hny₁
  have hnt₁_t' : fresh s₁ ∉ t'.fv := fun h => hf₁ (ht'_fv h)
  rw [hsame (fresh s₂) (fresh s₁) t' hnt₂ hnx₂ hny₂ hnt₁_t' hnx₁ hny₁]
  exact ht'_inv

/-! ## 3. Simply Typed λ-Calculus (`Stlc`) Typing, Substitution & Preservation -/

/-- Base type `ι` over `Base := Unit`. -/
abbrev ι : Ty Unit := Ty.base ()

/-- Church numeral type `(ι ⤳ ι) ⤳ (ι ⤳ ι)` in STLC. -/
abbrev NatTy : Ty Unit := (ι ⤳ ι) ⤳ ι ⤳ ι

/-- Church Boolean type `ι ⤳ ι ⤳ ι` in STLC. -/
abbrev BoolTy : Ty Unit := ι ⤳ ι ⤳ ι

/-- Identity combinator typing `[] ⊢ λx. x ∶ (σ ⤳ σ)` for any STLC type `σ`. -/
theorem typing_id (σ : Ty Unit) : ([] : Context ℕ (Ty Unit)) ⊢ idTerm ∶ (σ ⤳ σ) := by
  apply Typing.abs ∅
  intro x₁ _
  exact Typing.var (by simp [Context.haswellformed_def]) (by simp)

/-- Specialization of identity typing at base arrow type `ι ⤳ ι`. -/
theorem typing_id_base : ([] : Context ℕ (Ty Unit)) ⊢ idTerm ∶ (ι ⤳ ι) :=
  typing_id ι

/-- Constant (`K`) combinator typing `[] ⊢ λx. λy. x ∶ (σ ⤳ τ ⤳ σ)`. -/
theorem typing_k (σ τ : Ty Unit) : ([] : Context ℕ (Ty Unit)) ⊢ kTerm ∶ (σ ⤳ τ ⤳ σ) := by
  apply Typing.abs ∅
  intro x₁ _
  apply Typing.abs {x₁}
  intro x₂ hx₂
  have hwf : ([⟨x₂, τ⟩, ⟨x₁, σ⟩] : Context ℕ (Ty Unit))✓ := by
    simp only [Context.haswellformed_def, List.nodupKeys_cons, List.mem_keys]
    grind
  exact Typing.var hwf (by simp)

/-- Specialization of `K` combinator typing to `ι ⤳ τ ⤳ ι`. -/
theorem typing_k_base (τ : Ty Unit) : ([] : Context ℕ (Ty Unit)) ⊢ kTerm ∶ (ι ⤳ τ ⤳ ι) :=
  typing_k ι τ

/-- `S` combinator typing `[] ⊢ λx. λy. λz. x z (y z) ∶ ((σ₁ ⤳ σ₂ ⤳ τ) ⤳ (σ₁ ⤳ σ₂) ⤳ σ₁ ⤳ τ)`. -/
theorem typing_s (σ₁ σ₂ τ : Ty Unit) :
    ([] : Context ℕ (Ty Unit)) ⊢ sTerm ∶ ((σ₁ ⤳ σ₂ ⤳ τ) ⤳ (σ₁ ⤳ σ₂) ⤳ σ₁ ⤳ τ) := by
  apply Typing.abs ∅
  intro x₁ _
  apply Typing.abs {x₁}
  intro x₂ hx₂
  apply Typing.abs {x₁, x₂}
  intro x₃ hx₃
  have hwf : ([⟨x₃, σ₁⟩, ⟨x₂, σ₁ ⤳ σ₂⟩, ⟨x₁, σ₁ ⤳ σ₂ ⤳ τ⟩] : Context ℕ (Ty Unit))✓ := by
    simp only [Context.haswellformed_def, List.nodupKeys_cons, List.mem_keys]
    grind
  have hx₁ : [⟨x₃, σ₁⟩, ⟨x₂, σ₁ ⤳ σ₂⟩, ⟨x₁, σ₁ ⤳ σ₂ ⤳ τ⟩] ⊢ fvar x₁ ∶ (σ₁ ⤳ σ₂ ⤳ τ) :=
    Typing.var hwf (by simp)
  have hx₂ : [⟨x₃, σ₁⟩, ⟨x₂, σ₁ ⤳ σ₂⟩, ⟨x₁, σ₁ ⤳ σ₂ ⤳ τ⟩] ⊢ fvar x₂ ∶ (σ₁ ⤳ σ₂) :=
    Typing.var hwf (by simp)
  have hx₃ : [⟨x₃, σ₁⟩, ⟨x₂, σ₁ ⤳ σ₂⟩, ⟨x₁, σ₁ ⤳ σ₂ ⤳ τ⟩] ⊢ fvar x₃ ∶ σ₁ :=
    Typing.var hwf (by simp)
  exact Typing.app (Typing.app hx₁ hx₃) (Typing.app hx₂ hx₃)

/-- Church numeral `0` has type `NatTy`. -/
theorem typing_c0 : ([] : Context ℕ (Ty Unit)) ⊢ churchZero ∶ NatTy := by
  apply Typing.abs ∅
  intro f₁ _
  apply Typing.abs {f₁}
  intro x₁ hx₁
  have hwf : ([⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩] : Context ℕ (Ty Unit))✓ := by
    simp only [Context.haswellformed_def, List.nodupKeys_cons, List.mem_keys]
    grind
  exact Typing.var hwf (by simp)

/-- Church Boolean `true` (`λx. λy. x`) and `false` (`λx. λy. y`) both inhabit `BoolTy`. -/
theorem typing_church_booleans :
    ([] : Context ℕ (Ty Unit)) ⊢ kTerm ∶ BoolTy ∧
      ([] : Context ℕ (Ty Unit)) ⊢ churchZero ∶ BoolTy := by
  refine ⟨typing_k ι ι, ?_⟩
  apply Typing.abs ∅
  intro x₁ _
  apply Typing.abs {x₁}
  intro x₂ hx₂
  have hwf : ([⟨x₂, ι⟩, ⟨x₁, ι⟩] : Context ℕ (Ty Unit))✓ := by
    simp only [Context.haswellformed_def, List.nodupKeys_cons, List.mem_keys]
    grind
  exact Typing.var hwf (by simp)

/-- Church numeral `1` has type `NatTy`. -/
theorem typing_c1 : ([] : Context ℕ (Ty Unit)) ⊢ churchOne ∶ NatTy := by
  apply Typing.abs ∅
  intro f₁ _
  apply Typing.abs {f₁}
  intro x₁ hx₁
  have hwf : ([⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩] : Context ℕ (Ty Unit))✓ := by
    simp only [Context.haswellformed_def, List.nodupKeys_cons, List.mem_keys]
    grind
  have hf_ty : [⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩] ⊢ fvar f₁ ∶ (ι ⤳ ι) := Typing.var hwf (by simp)
  have hx_ty : [⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩] ⊢ fvar x₁ ∶ ι := Typing.var hwf (by simp)
  exact Typing.app hf_ty hx_ty

/-- Church numeral `2` has type `NatTy`. -/
theorem typing_c2 : ([] : Context ℕ (Ty Unit)) ⊢ churchTwo ∶ NatTy := by
  apply Typing.abs ∅
  intro f₁ _
  apply Typing.abs {f₁}
  intro x₁ hx₁
  have hwf : ([⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩] : Context ℕ (Ty Unit))✓ := by
    simp only [Context.haswellformed_def, List.nodupKeys_cons, List.mem_keys]
    grind
  have hf_ty : [⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩] ⊢ fvar f₁ ∶ (ι ⤳ ι) := Typing.var hwf (by simp)
  have hx_ty : [⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩] ⊢ fvar x₁ ∶ ι := Typing.var hwf (by simp)
  exact Typing.app hf_ty (Typing.app hf_ty hx_ty)

/-- Church successor `λn. λf. λx. f (n f x)` in locally nameless form. -/
def churchSucc : Term ℕ :=
  lam nVar (lam f (lam x (app (fvar f) (app (app (fvar nVar) (fvar f)) (fvar x)))))

/-- `churchSucc` elaborates to
`abs (abs (abs (app (bvar 1) (app (app (bvar 2) (bvar 1)) (bvar 0)))))`. -/
theorem churchSucc_eq :
    churchSucc =
      Term.abs (Term.abs (Term.abs (app (bvar 1) (app (app (bvar 2) (bvar 1)) (bvar 0))))) :=
  rfl

/-- Church successor has STLC type `NatTy ⤳ NatTy`. -/
theorem typing_succ : ([] : Context ℕ (Ty Unit)) ⊢ churchSucc ∶ (NatTy ⤳ NatTy) := by
  apply Typing.abs ∅
  intro n₁ _
  apply Typing.abs {n₁}
  intro f₁ hf₁
  apply Typing.abs {n₁, f₁}
  intro x₁ hx₁
  have hwf : ([⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩, ⟨n₁, NatTy⟩] : Context ℕ (Ty Unit))✓ := by
    simp only [Context.haswellformed_def, List.nodupKeys_cons, List.mem_keys]
    grind
  have hn_ty : [⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩, ⟨n₁, NatTy⟩] ⊢ fvar n₁ ∶ NatTy :=
    Typing.var hwf (by simp)
  have hf_ty : [⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩, ⟨n₁, NatTy⟩] ⊢ fvar f₁ ∶ (ι ⤳ ι) :=
    Typing.var hwf (by simp)
  have hx_ty : [⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩, ⟨n₁, NatTy⟩] ⊢ fvar x₁ ∶ ι :=
    Typing.var hwf (by simp)
  exact Typing.app hf_ty (Typing.app (Typing.app hn_ty hf_ty) hx_ty)

/-- Church addition `λn. λm. λf. λx. n f (m f x)` in locally nameless form. -/
def churchAdd : Term ℕ :=
  lam nVar (lam mVar (lam f (lam x
    (app (app (fvar nVar) (fvar f)) (app (app (fvar mVar) (fvar f)) (fvar x))))))

/-- Church addition has STLC type `NatTy ⤳ NatTy ⤳ NatTy`. -/
theorem typing_add : ([] : Context ℕ (Ty Unit)) ⊢ churchAdd ∶ (NatTy ⤳ NatTy ⤳ NatTy) := by
  apply Typing.abs ∅
  intro n₁ _
  apply Typing.abs {n₁}
  intro m₁ hm₁
  apply Typing.abs {n₁, m₁}
  intro f₁ hf₁
  apply Typing.abs {n₁, m₁, f₁}
  intro x₁ hx₁
  have hwf : ([⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩, ⟨m₁, NatTy⟩, ⟨n₁, NatTy⟩] : Context ℕ (Ty Unit))✓ := by
    simp only [Context.haswellformed_def, List.nodupKeys_cons, List.mem_keys]
    grind
  have hn_ty : [⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩, ⟨m₁, NatTy⟩, ⟨n₁, NatTy⟩] ⊢ fvar n₁ ∶ NatTy :=
    Typing.var hwf (by simp)
  have hm_ty : [⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩, ⟨m₁, NatTy⟩, ⟨n₁, NatTy⟩] ⊢ fvar m₁ ∶ NatTy :=
    Typing.var hwf (by simp)
  have hf_ty : [⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩, ⟨m₁, NatTy⟩, ⟨n₁, NatTy⟩] ⊢ fvar f₁ ∶ (ι ⤳ ι) :=
    Typing.var hwf (by simp)
  have hx_ty : [⟨x₁, ι⟩, ⟨f₁, ι ⤳ ι⟩, ⟨m₁, NatTy⟩, ⟨n₁, NatTy⟩] ⊢ fvar x₁ ∶ ι :=
    Typing.var hwf (by simp)
  exact Typing.app (Typing.app hn_ty hf_ty) (Typing.app (Typing.app hm_ty hf_ty) hx_ty)

/-- Open term `λz. y` (`((fvar y)⟦0 ↜ z⟧).abs`), with free variable `y`. -/
def openConstY : Term ℕ := lam z (fvar y)

/-- Open term typing `[⟨y, ι⟩] ⊢ (λz. y) ∶ (ι ⤳ ι)`. -/
theorem typing_openConstY : ([⟨y, ι⟩] : Context ℕ (Ty Unit)) ⊢ openConstY ∶ (ι ⤳ ι) := by
  apply Typing.abs {y}
  intro z₁ hz₁
  have hwf : ([⟨z₁, ι⟩, ⟨y, ι⟩] : Context ℕ (Ty Unit))✓ := by
    simp only [Context.haswellformed_def, List.nodupKeys_cons, List.mem_keys]
    grind
  exact Typing.var hwf (by simp)

/-- Typed capture-avoiding substitution via `typing_subst_head`: weakening
`[⟨y, ι⟩] ⊢ λz. y ∶ (ι ⤳ ι)` to `[⟨y, ι⟩, ⟨w, ι⟩]` and substituting `[y := app idTerm (fvar w)]`
produces a well-typed term in `[⟨w, ι⟩]` without capturing `w`. -/
theorem typing_subst_head_openConstY :
    ([⟨w, ι⟩] : Context ℕ (Ty Unit)) ⊢ openConstY[y := app idTerm (fvar w)] ∶ (ι ⤳ ι) := by
  have hweak : ([⟨y, ι⟩, ⟨w, ι⟩] : Context ℕ (Ty Unit)) ⊢ openConstY ∶ (ι ⤳ ι) :=
    typing_openConstY.weaken (by simp [Context.haswellformed_def])
  have hw_wf : ([⟨w, ι⟩] : Context ℕ (Ty Unit))✓ := by
    simp [Context.haswellformed_def]
  have hw_arg : ([⟨w, ι⟩] : Context ℕ (Ty Unit)) ⊢ app idTerm (fvar w) ∶ ι := by
    have hid_w : ([⟨w, ι⟩] : Context ℕ (Ty Unit)) ⊢ idTerm ∶ (ι ⤳ ι) :=
      typing_id_base.weaken hw_wf
    exact Typing.app hid_w (Typing.var hw_wf (by simp))
  exact typing_subst_head hweak hw_arg

/-- Even substituting `fvar z` for `y` into `openConstY = lam z (fvar y)` preserves typing
`[⟨z, ι⟩] ⊢ (λz. y)[y := z] ∶ (ι ⤳ ι)` via `typing_subst_head`, with `z` remaining free. -/
theorem typing_subst_head_no_capture_z :
    ([⟨z, ι⟩] : Context ℕ (Ty Unit)) ⊢ openConstY[y := fvar z] ∶ (ι ⤳ ι) ∧
      openConstY[y := fvar z] = Term.abs (fvar z) := by
  refine ⟨?_, rfl⟩
  have hweak : ([⟨y, ι⟩, ⟨z, ι⟩] : Context ℕ (Ty Unit)) ⊢ openConstY ∶ (ι ⤳ ι) :=
    typing_openConstY.weaken (by simp [Context.haswellformed_def])
  have hz_wf : ([⟨z, ι⟩] : Context ℕ (Ty Unit))✓ := by
    simp [Context.haswellformed_def]
  exact typing_subst_head hweak (Typing.var hz_wf (by simp))

/-- Multi-step subject reduction for STLC full β-reduction, derived from `FullBeta.preservation`
and `Relation.preserves_reflTransGen_iff`. -/
theorem preservation_steps {Γ : Context ℕ (Ty Unit)} {t t' : Term ℕ} {τ : Ty Unit}
    (ht : Γ ⊢ t ∶ τ) (hsteps : t ↠βᶠ t') : Γ ⊢ t' ∶ τ :=
  (Relation.preserves_reflTransGen_iff.mpr (@FullBeta.preservation ℕ Unit _ _ Γ τ)) hsteps ht

/-- Concrete multi-step reduction `churchSucc churchOne ↠βᶠ churchTwo` under nested binders. -/
theorem succ_c1_steps_c2 : app churchSucc churchOne ↠βᶠ churchTwo := by
  have hlc_succ : LC churchSucc := typing_succ.lc
  have hlc_c1 : LC churchOne := typing_c1.lc
  have step₁ : app churchSucc churchOne ⭢βᶠ
      Term.abs (Term.abs (app (bvar 1) (app (app churchOne (bvar 1)) (bvar 0)))) :=
    Xi.base (Beta.beta hlc_succ hlc_c1)
  have steps₂ :
      Term.abs (Term.abs (app (bvar 1) (app (app churchOne (bvar 1)) (bvar 0)))) ↠βᶠ churchTwo := by
    apply FullBeta.redex_abs_cong ∅
    intro f₁ _
    apply FullBeta.redex_abs_cong ∅
    intro x₁ _
    change app (fvar f₁) (app (app churchOne (fvar f₁)) (fvar x₁)) ↠βᶠ
      app (fvar f₁) (app (fvar f₁) (fvar x₁))
    apply FullBeta.redex_app_r_cong _ (LC.fvar f₁)
    have sub₁ : app (app churchOne (fvar f₁)) (fvar x₁) ⭢βᶠ
        app (Term.abs (app (fvar f₁) (bvar 0))) (fvar x₁) :=
      Xi.appR (LC.fvar x₁) (Xi.base (Beta.beta hlc_c1 (LC.fvar f₁)))
    have hlc_mid : LC (Term.abs (app (fvar f₁) (bvar 0))) :=
      LC.abs ∅ _ fun u _ => LC.app (LC.fvar f₁) (LC.fvar u)
    have sub₂ : app (Term.abs (app (fvar f₁) (bvar 0))) (fvar x₁) ⭢βᶠ
        app (fvar f₁) (fvar x₁) :=
      Xi.base (Beta.beta hlc_mid (LC.fvar x₁))
    exact ReflTransGen.head sub₁ (ReflTransGen.single sub₂)
  exact ReflTransGen.head step₁ steps₂

/-- Subject reduction on `churchSucc churchOne ↠βᶠ churchTwo` preserves `NatTy`. -/
theorem preservation_succ_c1_c2 : ([] : Context ℕ (Ty Unit)) ⊢ churchTwo ∶ NatTy :=
  preservation_steps (Typing.app typing_succ typing_c1) succ_c1_steps_c2

/-- Concrete multi-step reduction `(λf. λx. f (f x)) id a ↠βᶠ a`
(`churchTwo idTerm (fvar x) ↠βᶠ fvar x`). -/
theorem churchTwo_id_steps_var : app (app churchTwo idTerm) (fvar x) ↠βᶠ fvar x := by
  have hlc_c2 : LC churchTwo := typing_c2.lc
  have hlc_id : LC idTerm := typing_id_base.lc
  have hlc_x : LC (fvar x) := LC.fvar x
  have hlc_body : LC (Term.abs (app idTerm (app idTerm (bvar 0)))) :=
    LC.abs ∅ _ fun u _ => LC.app hlc_id (LC.app hlc_id (LC.fvar u))
  have s₁ : app (app churchTwo idTerm) (fvar x) ⭢βᶠ
      app (Term.abs (app idTerm (app idTerm (bvar 0)))) (fvar x) :=
    Xi.appR hlc_x (Xi.base (Beta.beta hlc_c2 hlc_id))
  have s₂ : app (Term.abs (app idTerm (app idTerm (bvar 0)))) (fvar x) ⭢βᶠ
      app idTerm (app idTerm (fvar x)) :=
    Xi.base (Beta.beta hlc_body hlc_x)
  have s₃ : app idTerm (app idTerm (fvar x)) ⭢βᶠ app idTerm (fvar x) :=
    Xi.appL hlc_id (Xi.base (Beta.beta hlc_id hlc_x))
  have s₄ : app idTerm (fvar x) ⭢βᶠ fvar x :=
    Xi.base (Beta.beta hlc_id hlc_x)
  exact ReflTransGen.head s₁ (ReflTransGen.head s₂ (ReflTransGen.head s₃ (ReflTransGen.single s₄)))

/-- Subject reduction on `churchTwo idTerm (fvar x) ↠βᶠ fvar x` in open context `[⟨x, ι⟩]`. -/
theorem preservation_churchTwo_id_var :
    ([⟨x, ι⟩] : Context ℕ (Ty Unit)) ⊢ app (app churchTwo idTerm) (fvar x) ∶ ι ∧
      ([⟨x, ι⟩] : Context ℕ (Ty Unit)) ⊢ fvar x ∶ ι := by
  have hx_wf : ([⟨x, ι⟩] : Context ℕ (Ty Unit))✓ := by
    simp [Context.haswellformed_def]
  have hc2 : ([⟨x, ι⟩] : Context ℕ (Ty Unit)) ⊢ churchTwo ∶ NatTy :=
    typing_c2.weaken hx_wf
  have hid : ([⟨x, ι⟩] : Context ℕ (Ty Unit)) ⊢ idTerm ∶ (ι ⤳ ι) :=
    typing_id_base.weaken hx_wf
  have hx : ([⟨x, ι⟩] : Context ℕ (Ty Unit)) ⊢ fvar x ∶ ι :=
    Typing.var hx_wf (by simp)
  have happ : ([⟨x, ι⟩] : Context ℕ (Ty Unit)) ⊢ app (app churchTwo idTerm) (fvar x) ∶ ι :=
    Typing.app (Typing.app hc2 hid) hx
  exact ⟨happ, preservation_steps happ churchTwo_id_steps_var⟩

/-- Progress and strong normalization hold for closed STLC applications such as
`app churchSucc churchOne`. -/
theorem safety_and_sn_succ_c1 :
    ((app churchSucc churchOne).Value ∨ ∃ t', app churchSucc churchOne ⭢βᶠ t') ∧
      SN FullBeta (app churchSucc churchOne) :=
  ⟨FullBeta.progress (Typing.app typing_succ typing_c1),
    Stlc.strong_norm (Typing.app typing_succ typing_c1)⟩

end CslibTests.LocallyNamelessStlc
