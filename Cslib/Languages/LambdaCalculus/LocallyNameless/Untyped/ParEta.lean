/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/

module

public import Cslib.Foundations.Relation.Attr
public import Cslib.Foundations.Relation.Defs
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.BetaNfLc
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta

/-!  # Parallel η-reduction

This file formalises [Takahashi1995] Section 3.

## Design

This file only contain theorems related to `ParEta` and `etaExp`.
η-postpone theorems are placed in `EtaPostpone.lean`.

## Reference

* [Y. Takahashi, *Parallel Reductions in λ-Calculus*][Takahashi1995]

-/


@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

open Relation Function

variable {Var : Type u}

/-- A parallel η-reduction step. -/
inductive ParEta : Term Var → Term Var → Prop
/-- Free variables parallel step to themselves. -/
  | fvar (x : Var) : ParEta (fvar x) (fvar x)
/-- A parallel left and right congruence rule for application. -/
  | app : ParEta M M' → ParEta N N' → ParEta (app M N) (app M' N')
/-- Congruence rule for lambda terms. -/
  | abs (xs : Finset Var) :
    (∀ x ∉ xs, ParEta (M ^ fvar x) (M' ^ fvar x)) → ParEta (abs M) (abs M')
/-- A parallel η-reduction. -/
  | eta : ParEta M M' → ParEta (abs (app M (bvar 0))) M'

variable {L M M' N N' : Term Var} {xs : Finset Var}

/-- Parallel η-reduction is reflexive on locally closed terms. -/
@[scoped grind ->]
theorem ParEta.lc_refl (h : LC M) : ParEta M M := by
  induction h with
  | fvar x => exact ParEta.fvar x
  | abs xs t _ ih => exact ParEta.abs xs ih
  | app _ _ ihM ihN => exact ParEta.app ihM ihN

theorem FullEta.le_parallel : (· ⭢ηᶠ ·) ≤ (ParEta : Term Var → Term Var → Prop) := by
  intro M N step
  induction step with
  | base h => cases h with | eta h => exact ParEta.eta (ParEta.lc_refl h)
  | appL h_lc _ ih => exact ParEta.app (ParEta.lc_refl h_lc) ih
  | appR h_lc _ ih => exact ParEta.app ih (ParEta.lc_refl h_lc)
  | abs xs _ ih => exact ParEta.abs xs ih

@[scoped grind ->]
theorem ParEta.step_lc_r (h : ParEta M N) : LC N := by
  induction h with
  | fvar x => exact LC.fvar x
  | app _ _ ihM ihN => exact LC.app ihM ihN
  | abs xs _ ih => exact LC.abs xs _ fun x hx => ih x hx
  | @eta M M' _ ih => exact ih

@[scoped grind ->]
theorem ParEta.step_lc_l [HasFresh Var] (h : ParEta M N) : LC M := by
  induction h with
  | fvar x => exact LC.fvar x
  | app _ _ ihM ihN => exact LC.app ihM ihN
  | abs xs _ ih => exact LC.abs xs _ fun x hx => (ih x hx)
  | @eta M M' _ ih => exact LC.abs ∅ _ fun x _ => LC.app (by grind) (by grind)

theorem ParEta.le_reflTransGen_fullEta [DecidableEq Var] [HasFresh Var] :
  (ParEta : Term Var → Term Var → Prop) ≤ (· ↠ηᶠ ·) := by
  intro M N para
  induction para with
  | fvar x => exact ReflTransGen.refl
  | eta hMM' ih => exact .head (Xi.base (.eta (ParEta.step_lc_l hMM'))) ih
  | app hM hN ihM ihN => exact .trans (FullEta.redex_app_l_cong ihM ((ParEta.step_lc_l hN)))
                                      (FullEta.redex_app_r_cong ihN ((ParEta.step_lc_r hM)))
  | abs xs h ih => exact FullEta.redex_abs_cong xs ih

theorem reflTransGen_parallel_fullEta [DecidableEq Var] [HasFresh Var] :
  (ReflTransGen ParEta : Term Var → Term Var → Prop) = (· ↠ηᶠ ·) := by
  apply le_antisymm
  · exact reflTransGen_le_of_le ParEta.le_reflTransGen_fullEta
  · exact ReflTransGen.mono FullEta.le_parallel

/-- Parallel reduction respects substitution. -/
theorem ParEta.para_subst [DecidableEq Var] [HasFresh Var] (x : Var)
  (pm : ParEta M M') (pn : ParEta N N') : ParEta (M[x:=N]) (M'[x:= N']) := by
  induction pm generalizing N N' with
  | fvar _ => grind
  | app _ _ _ _ => exact ParEta.app (by grind) (by grind)
  | abs xs h ih => exact ParEta.abs (xs ∪ { x }) fun x hx => by grind
  | eta hMM' ih => exact ParEta.eta (ih pn)

/-- Parallel substitution respects fresh opening. -/
theorem ParEta.para_open_out [DecidableEq Var] [HasFresh Var]
    (hbody : ∀ x ∉ xs, ParEta (M ^ Term.fvar x) (M' ^ Term.fvar x))
    (hN : ParEta N N') : ParEta (M ^ N) (M' ^ N') := by
  have ⟨z, hz⟩ := fresh_exists <| free_union [fv] Var
  convert ParEta.para_subst z (hbody z (by grind)) hN
  · rw [Term.subst_intro z _ _ (by grind)]
  · rw [Term.subst_intro z _ _ (by grind)]

/-- `etaExp M` is the standard η-expansion of a term `M`, represented as `λ. M (bvar 0)`. -/
abbrev etaExp (M : Term Var) : Term Var := abs (app M (bvar 0))

/- [Takahashi1995] Lemma 3.2 (variable case). -/
theorem parEta_inv_fvar {x : Var} (h : ParEta M (fvar x)) : ∃ k, M = etaExp^[k] (fvar x) := by
  generalize hm : fvar x = M at h
  induction h with
  | fvar x => exists 0
  | app _ _ _ _ => grind
  | abs xs _ _ => grind
  | eta _ ih =>
      obtain ⟨k, rfl⟩ := ih hm
      exists k + 1
      rw [add_comm, Function.iterate_add]
      simp

/- [Takahashi1995] Lemma 3.2 (application case).-/
theorem parEta_inv_app : ParEta L (app M' N') ->
    ∃ k M N, L = etaExp^[k] (app M N) ∧ ParEta M M' ∧ ParEta N N' := by
  induction n : Term.size L using Nat.strong_induction_on generalizing L M' N' with
  | h n ih =>
  rintro (h | h | h | h)
  · exact ⟨0, _, _, rfl, h, by assumption⟩
  · obtain ⟨k, A', B', rfl, hA', hB'⟩ := ih _ (by grind) rfl h
    refine ⟨k + 1, A', B', ?_, hA', hB'⟩
    rw [add_comm, Function.iterate_add]
    simp

/- [Takahashi1995] Lemma 3.2 (abstraction case). -/
theorem parEta_inv_abs : ParEta M (Term.abs N) ->
    ∃ (k : ℕ) (A' : Term Var) (xs : Finset Var), M = etaExp^[k] (Term.abs A') ∧
      ∀ x ∉ xs, ParEta (A' ^ fvar x) (N ^ fvar x) := by
  induction n : Term.size M using Nat.strong_induction_on generalizing M N with
  | h n ih =>
  rintro (h | h | h | h)
  · exact ⟨0, _, h, rfl, by assumption⟩
  · obtain ⟨k, A', xs, rfl, hA'⟩ := ih _ (by grind) rfl h
    refine ⟨k + 1, A', xs, ?_, hA'⟩
    rw [add_comm, Function.iterate_add]
    simp

theorem parEta_etaExp (h : ParEta M N) (k : ℕ) : ParEta (etaExp^[k] M) N := by
  induction k with
  | zero => exact h
  | succ k ih =>
      rw [add_comm, Function.iterate_add]
      exact ParEta.eta ih

variable [HasFresh Var]

@[simp, scoped grind <-]
theorem etaExp_lc (hM : LC M) (k : ℕ) : LC (etaExp^[k] M) := by
  induction k with
  | zero => exact hM
  | succ k ih =>
      rw [add_comm, Function.iterate_add]
      exact LC.abs ∅ _ (by grind)

theorem etaExp_fullEtaStar (hM : LC M) (k : ℕ) : (etaExp^[k] M) ↠ηᶠ M := by
  induction k with
  | zero => exact .refl
  | succ n ih =>
      refine .trans ?_ ih
      rw [add_comm, Function.iterate_add, iterate_one, comp_apply, etaExp]
      grind

theorem etaExp_app_collapse (hm : LC M) (hn : LC N) (k : ℕ) :
    (app (etaExp^[k] M) N) ↠βᶠ (app M N) := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
    rw [add_comm, Function.iterate_add, Function.iterate_one, Function.comp_apply]
    exact .trans (.head (.base (.beta (LC.abs ∅ _ (by grind)) hn)) (by grind)) ih

theorem Normal.etaExp_one (h : BetaNfLcNotAbs M) : BetaNfLc (etaExp M) :=
  .abs ∅ fun x hx => .app (by grind) (by grind) (.fvar _)

theorem parallel_etaExp_abs_app (h : ∀ x ∉ xs, (M ^ fvar x) ⭢ₚ (M' ^ fvar x))
    (step : N ⭢ₚ N') (j : ℕ) : (Term.app (etaExp^[j] M.abs) N) ⭢ₚ (M' ^ N') := by
  induction j generalizing M M' N N' xs with
  | zero => exact Parallel.beta xs h step
  | succ j ih =>
    have hCabs : M.abs.LC := LC.abs xs _ (by grind)
    rw [add_comm, Function.iterate_add]
    exact .beta xs (fun x hx => by grind [ih h (.fvar x), etaExp_lc hCabs j]) step


variable [DecidableEq Var]

theorem etaExp_betaStar_congr (h : M ↠βᶠ M') (k : ℕ) : (etaExp^[k] M) ↠βᶠ (etaExp^[k] M') := by
  cases FullBeta.steps_lc_or_rfl h with
  | inr => grind
  | inl hM =>
    induction k with
    | zero => exact h
    | succ k ih =>
      rw [add_comm, Function.iterate_add]
      exact FullBeta.redex_abs_cong ∅
                (fun _ _ => FullBeta.redex_app_l_cong (by grind [etaExp_lc hM.1 k]) (.fvar _))

theorem etaExp_abs_collapse (hm : M.abs.LC) (k : ℕ) : (etaExp^[k] M.abs) ↠βᶠ M.abs := by
  have h_beta : FullBeta (M.abs.app (bvar 0)).abs M.abs := by
    obtain ⟨x, hx⟩ := fresh_exists <| free_union [fv] Var
    exact .abs { x } fun y _ =>
      by grind [Xi.base (Beta.beta (show LC M.abs from hm) (show LC (fvar y) from LC.fvar y))]
  induction k with
  | zero =>  exact .refl
  | succ k ih =>
    rw [add_comm, Function.iterate_add]
    exact .tail
      (FullBeta.redex_abs_cong ∅
        (fun x _ => .trans (.trans (by grind) (FullBeta.redex_app_l_cong ih (.fvar x))) (by grind)))
      h_beta

theorem etaExp_NormalNotAbs_normalForm (hne : BetaNfLcNotAbs M) (k : ℕ) :
    ∃ M', (etaExp^[k] M) ↠βᶠ M' ∧ BetaNfLc M' := by
  by_cases hk : k = 0
  · exact ⟨M, by subst hk; exact ReflTransGen.refl, hne.1⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    exists (M.app (bvar 0)).abs
    induction k with
    | zero => exact ⟨ReflTransGen.refl, Normal.etaExp_one hne⟩
    | succ n h =>
      refine ⟨?_, by grind⟩
      have heq : (n + 1).succ = 1 + (n + 1) := by omega
      rw [heq, Function.iterate_add]
      apply FullBeta.redex_abs_cong ∅ fun x hx => ?_
      apply BetaNfLcNotAbs.lc at hne
      unfold open' openRec
      rw [open_lc _ _ M hne, open_lc]
      apply etaExp_app_collapse <;> grind
      apply etaExp_lc hne

theorem parBeta_etaExp_congr (h : M ⭢ₚ M') (k : ℕ) : (etaExp^[k] M) ⭢ₚ (etaExp^[k] M') := by
  induction k with
  | zero => exact h
  | succ k ih =>
      rw [add_comm, Function.iterate_add]
      exact Parallel.abs ∅ (by grind)

theorem core_par (hm : BetaNfLc M) : ∀ L, ParEta L M →
    (∃ N, L ↠βᶠ N ∧ BetaNfLc N) ∧
    (BetaNfLcNotAbs M → ∃ k B, L ↠βᶠ (etaExp^[k] B) ∧ BetaNfLcNotAbs B) := by
  induction hm with
  | fvar x =>
      intro L hL
      obtain ⟨k, rfl⟩ := parEta_inv_fvar hL
      exact ⟨etaExp_NormalNotAbs_normalForm (BetaNfLcNotAbs.fvar x) k,
        fun _ => ⟨k, Term.fvar x, ReflTransGen.refl, BetaNfLcNotAbs.fvar x⟩⟩
  | @app M N hM hMne hN ihM ihN =>
      intro L hL
      obtain ⟨j, M', N', rfl, hM', hN'⟩ := parEta_inv_app hL
      have lcN' : LC N' := (ParEta.step_lc_l hN')
      obtain ⟨k1, B1, hB1red, hB1neu⟩ := (ihM M' hM').2 ⟨hM, (by grind)⟩
      obtain ⟨Nhat, hNred, hNnorm⟩ := (ihN N' hN').1
      have hcollapse : (app M' N') ↠βᶠ (app B1 Nhat) :=
        (FullBeta.redex_app_l_cong hB1red lcN').trans
          ((FullBeta.redex_app_r_cong hNred (etaExp_lc (BetaNfLcNotAbs.lc hB1neu) k1)).trans
            (etaExp_app_collapse (BetaNfLcNotAbs.lc hB1neu) (BetaNfLc.lc hNnorm) k1))
      have hBneu : BetaNfLcNotAbs (app B1 Nhat) := BetaNfLcNotAbs.app hB1neu hNnorm
      have hcongr : (etaExp^[j] (app M' N')) ↠βᶠ (etaExp^[j] (app B1 Nhat)) :=
        etaExp_betaStar_congr hcollapse j
      obtain ⟨M2, h2red, h2norm⟩ := etaExp_NormalNotAbs_normalForm hBneu j
      exact ⟨⟨M2, hcongr.trans h2red, h2norm⟩, fun _ => ⟨j, app B1 Nhat, hcongr, hBneu⟩⟩
  | @abs xs body hbody ihbody =>
      intro L hL
      obtain ⟨j, body', xs2, rfl, hred⟩ := parEta_inv_abs hL
      obtain ⟨x0, hx0⟩ := fresh_exists <| free_union [fv] Var
      obtain ⟨C0, hC0red, hC0norm⟩ :=
        (ihbody x0 (by grind) (body' ^ fvar x0) (hred x0 (by grind))).1
      set D := C0 ^* x0 with hDdef
      have hDred : ∀ x : Var, (body' ^ fvar x) ↠βᶠ (D ^ fvar x) := by
        intro x
        have e1 : body' ^ fvar x = (body' ^ fvar x0)[x0 := fvar x] :=
          by rw [Term.subst_intro x0]; grind
        have e2 : D  ^ fvar x = C0[x0 := fvar x] := by rw [hDdef, close_open_to_subst] <;> grind
        rw [e1, e2]
        exact FullBeta.steps_subst_cong _ _ _ _ hC0red (LC.fvar x)
      have hDnormal : BetaNfLc D.abs := by
        refine .abs ∅ (fun x _ => ?_)
        rw [hDdef, close_open_to_subst _ _ _ (by grind) (by grind)]
        exact .subst_fvar hC0norm x0 x
      exact ⟨⟨D.abs,
        (etaExp_betaStar_congr (FullBeta.redex_abs_cong ∅ (fun x _ => hDred x)) j).trans
          (etaExp_abs_collapse (BetaNfLc.lc hDnormal) j), hDnormal⟩, by grind⟩

/-
[Takahashi1995] Lemma 3.4: Parallel η/β postponement:
    a parallel η-step postpones over a parallel β-step:
    `M ⟹η P ⟹β N` implies `M ⟹β P' ⟹η N` for some `P'`.
-/
theorem diamondCommute_parEta_parBeta : DiamondCommute (swap (ParEta (Var := Var))) Parallel := by
  intros P M N hη hβ
  induction hβ generalizing M with
  | fvar x => exact ⟨M, Parallel.lc_refl M (ParEta.step_lc_l hη), by grind⟩
  | app _ _ ih1 ih2 =>
    obtain ⟨k, M1, M2, rfl, hM1, hM2⟩ := parEta_inv_app hη
    obtain ⟨P1, hP1, hP1'⟩ := ih1 hM1
    obtain ⟨P2, hP2, hP2'⟩ := ih2 hM2
    exact ⟨etaExp^[k] (app P1 P2),
            parBeta_etaExp_congr (Parallel.app hP1 hP2) k,
            parEta_etaExp (ParEta.app hP1' hP2') k⟩
  | abs xs hβ ih =>
    rename_i xs M M'
    obtain ⟨k, M0, xs2, rfl, hM0⟩ := parEta_inv_abs hη
    obtain ⟨x0, hx0⟩ := fresh_exists <| free_union [fv] Var
    obtain ⟨Q0, hQ0⟩ := ih x0 (by grind) (hM0 x0 (by grind))
    set M0' : Term Var := Q0 ^* x0
    have hM0_cofinite : ∀ x ∉ xs ∪ xs2, (M0 ^ fvar x) ⭢ₚ (M0' ^ fvar x) := by
      intro x hx
      have h_subst : M0 ^ fvar x = (M0 ^ fvar x0)[x0 := fvar x] := Term.subst_intro _ _ _ (by grind)
      have h_subst' : M0' ^ fvar x = Q0[x0 := fvar x] := by rw [close_open_to_subst] <;> grind
      rw [h_subst, h_subst']
      apply para_subst <;> grind
    have hM0'_cofinite : ∀ x ∉ xs ∪ xs2, ParEta (M0' ^ fvar x) (M' ^ fvar x) := by
      intro x hx
      have h_subst' : M0' ^ fvar x = Q0[x0 := fvar x] := by rw [close_open_to_subst] <;> grind
      have h_subst'' : M' ^ fvar x = (M' ^ fvar x0)[x0:= fvar x] := subst_intro _ _ _ (by grind)
      rw [h_subst', h_subst'']
      exact ParEta.para_subst x0 hQ0.2 (ParEta.fvar x)
    exact ⟨etaExp^[k] M0'.abs,
           parBeta_etaExp_congr (Parallel.abs (xs ∪ xs2) hM0_cofinite) _,
           parEta_etaExp (ParEta.abs (xs ∪ xs2) hM0'_cofinite) _⟩
  | beta xs h₁ h₂ h₃ h₄ =>
    rename_i xs M' N' M'' N''
    obtain ⟨k, M₁, M₂, rfl, hM₁, hM₂⟩ := parEta_inv_app hη
    obtain ⟨j, M₁b, xs', rfl, hM₁b⟩ := parEta_inv_abs hM₁
    obtain ⟨x0, hx0'⟩ := fresh_exists <| free_union [fv] Var
    obtain ⟨Q₁, hQ₁, hQ₂⟩ := h₃ x0 (by grind) (hM₁b x0 (by grind))
    set M₁b' : Term Var := Q₁ ^* x0
    have hM₁b'_family : ∀ x ∉ xs ∪ xs', (M₁b ^ fvar x) ⭢ₚ (M₁b' ^ fvar x) := by
      intro x hx
      have hsub : M₁b ^ fvar x = (M₁b ^ fvar x0)[x0 := fvar x] := by
        rw [Term.subst_intro]
        grind
      have hsub' : M₁b' ^ fvar x = Q₁[x0 := fvar x] := by rw [close_open_to_subst] <;> grind
      rw [hsub, hsub']
      exact para_subst x0 hQ₁ (Parallel.fvar x)
    have hM₁b'_family' : ∀ x ∉ xs ∪ xs', ParEta (M₁b' ^ fvar x) (N' ^ fvar x) := by
      intro x hx
      have hsub : M₁b' ^ fvar x = Q₁[x0 := fvar x] := by rw [close_open_to_subst] <;> grind
      have hsub' : N' ^ fvar x = (N' ^ fvar x0)[x0 := fvar x] := by
        rw [subst_intro x0 _ _ (by grind)]
      rw [hsub, hsub']
      exact ParEta.para_subst x0 hQ₂ (ParEta.fvar x)
    obtain ⟨P', hP', hP''⟩ := h₄ hM₂
    exact ⟨etaExp^[k] (M₁b' ^ P'),
           parBeta_etaExp_congr (parallel_etaExp_abs_app hM₁b'_family hP' j) k,
           parEta_etaExp (ParEta.para_open_out hM₁b'_family' hP'') k⟩

theorem commute_parEta_parBeta : Commute (swap (ParEta (Var := Var))) Parallel :=
  DiamondCommute.to_commute diamondCommute_parEta_parBeta

/-- [Takahashi1995] Lemma 3.6: If `M ⟹_η N` (parallel η-reduction) and `N` has a
β-normal form, then `M` has a β-normal form. -/
theorem parEta_hasBetaNF (h : ParEta M N) (hn : Normalizable FullBeta N) :
    Normalizable FullBeta M := by
  obtain ⟨N, hQN, hN⟩ := hn
  have hNlc : LC N := by cases (FullBeta.steps_lc_or_rfl hQN) with grind [ParEta.step_lc_r h]
  simp only [<- reflTransGen_parallel_fullBeta] at hQN
  obtain ⟨P', hPP', hP'N⟩ := DiamondCommute.diamond_commute_reflTransGen_right
      (r₁ := (swap (ParEta (Var := Var)))) (r₂ := Parallel) diamondCommute_parEta_parBeta h hQN
  obtain ⟨M, hP'M, hMnorm⟩ := (core_par (betaNF_normal hNlc hN) P' hP'N).1
  simp only [reflTransGen_parallel_fullBeta] at hPP'
  exact ⟨M, .trans hPP' hP'M, BetaNfLc.betaNF hMnorm⟩

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
