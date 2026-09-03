/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Leng
-/


module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Size

/-!
# η-expansion preserves β-strong-normalisation (`sn_eta_step`)

This file formalises the paper proof in `sn_eta_step_proof.md`:

  **If `t ⟶η t'` (a single full η-step) and `t'` is β-strongly-normalising,
  then `t` is β-strongly-normalising.**

("β-strongly-normalising" is `Acc (flip FullBeta)`, i.e. accessibility for single
β-steps.)

The proof follows Takahashi-style **parallel η-reduction with an explicit
`Eta`-count**.  We define `ParEtaC n M N` = "`M` reduces to `N` by a parallel
η-derivation containing exactly `n` contractions of an η-redex".  The three
ingredients are:

* `parEtaC_of_fullEta` (Fact 2.1): a single η-step gives a count-`1` derivation;
* `interaction` (the Interaction Lemma): a single β-step out of `t` either
  reflects to a genuine β-step out of `t'` (keeping some parallel η-derivation),
  or is *absorbed*, landing back on `t'` with a **strictly smaller** count;
* `sn_transfer` (the generalized SN-transfer theorem): lexicographic induction on
  `(β-accessibility rank of t', count n)`.
-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Untyped.Term

variable {Var : Type u}

/-- **Parallel η-reduction with `Eta`-count** `ParEtaC n M N`: `M` reduces to `N`
by a parallel η-derivation whose number of η-contractions is exactly `n`. -/
inductive ParEtaC : ℕ → Term Var → Term Var → Prop
  /-- (η1) A free variable reduces to itself, count `0`. -/
  | fvar (x : Var) : ParEtaC 0 (Term.fvar x) (Term.fvar x)
  /-- (η3) Congruence for application; counts add. -/
  | app {a b : ℕ} {M M' N N' : Term Var} :
      ParEtaC a M M' → ParEtaC b N N' → ParEtaC (a + b) (Term.app M N) (Term.app M' N')
  /-- (η2) Congruence for abstraction (cofinite quantification); count preserved. -/
  | abs (xs : Finset Var) {a : ℕ} {M M' : Term Var} :
      (∀ x ∉ xs, ParEtaC a (M ^ Term.fvar x) (M' ^ Term.fvar x)) →
        ParEtaC a (Term.abs M) (Term.abs M')
  /-- (η4) Parallel contraction of an η-redex `λz.(M z) ⟹ M'`; count `+1`. -/
  | eta {a : ℕ} {M M' : Term Var} :
      LC M → ParEtaC a M M' → ParEtaC (a + 1) (Term.abs (Term.app M (Term.bvar 0))) M'

/-- `ParEtaC` is reflexive at count `0` on locally closed terms. -/
theorem ParEtaC.refl {M : Term Var} (h : LC M) : ParEtaC 0 M M := by
  induction n : M.size using Nat.strong_induction_on generalizing M with | h n ih =>
  match h with
  | LC.fvar x => exact ParEtaC.fvar x
  | LC.app h₁ h₂ => exact ParEtaC.app (ih _ (by grind) h₁ rfl) (ih _ (by grind) h₂ rfl)
  | LC.abs xs t ht =>
      exact ParEtaC.abs xs (fun x hx => ih _ (by rw [size_open_fvar]; grind) (ht x hx) rfl)

/-- A single full η-step is a parallel η-derivation of count `1`. -/
theorem parEtaC_of_fullEta {t t' : Term Var} (h : FullEta t t') : ParEtaC 1 t t' := by
  induction h with
  | base hEta => cases hEta with | eta hLC => exact ParEtaC.eta hLC (ParEtaC.refl hLC)
  | appL hLC _ hih => exact ParEtaC.app (ParEtaC.refl hLC) hih
  | appR hLC _ hih => exact ParEtaC.app hih (ParEtaC.refl hLC)
  | abs k _ ih => exact ParEtaC.abs k ih

@[scoped grind →]
theorem ParEtaC.step_lc_r {n : ℕ} {M N : Term Var} (h : ParEtaC n M N) : LC N := by
  induction h with
  | fvar x => exact LC.fvar x
  | app _ _ ihM ihN => exact LC.app ihM ihN
  | abs xs _ ih => exact LC.abs xs _ (fun x hx => (ih x hx))
  | eta _ _ ih => exact ih

variable [HasFresh Var]

@[scoped grind →]
theorem ParEtaC.step_lc_l {n : ℕ} {M N : Term Var} (h : ParEtaC n M N) : LC M := by
  induction h with
  | fvar x => exact LC.fvar x
  | app _ _ ihM ihN => exact LC.app ihM ihN
  | abs xs _ ih => exact LC.abs xs _ (fun x hx => (ih x hx))
  | eta hM hMM' ih => exact LC.abs (∅ : Finset Var) _ (fun y _ => LC.app (by grind) (by grind))

variable [DecidableEq Var]

theorem ParEtaC.refl_rev {M N : Term Var} (h : ParEtaC 0 M N) : M = N := by
  generalize hi: 0 = i at h
  induction h with
  | fvar x => grind
  | app _ _ _ _ => grind
  | eta _ _ _ => grind
  | abs xs _ ih =>  have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
                    specialize ih x (by grind) hi
                    apply open_injective at ih <;> grind

theorem parEtaC_to_fullEta {t t' : Term Var} (h : ParEtaC 1 t t') : FullEta t t' := by
  generalize hi: 1 = i at h
  induction h with
  | fvar x => omega
  | abs xs _ _ => exact Xi.abs xs (by grind)
  | app ha hb iha ihb =>
    rename_i a b _ _ _ _
    have hab : (a = 0 /\ b = 1) \/ (a = 1 /\ b = 0) := by omega
    rcases hab with ⟨ha, hb⟩|⟨ha, hb⟩
    all_goals subst_vars
    · have := ParEtaC.refl_rev ha
      subst_vars
      exact Xi.appL (ParEtaC.step_lc_r ha) (by grind)
    · have := ParEtaC.refl_rev hb
      subst_vars
      exact Xi.appR (ParEtaC.step_lc_r hb) (by grind)
  | eta hlc h ih => cases hi
                    apply ParEtaC.refl_rev at h
                    grind

/-- **Renaming preserves the count.** Substituting one free variable for another
in a `ParEtaC` derivation preserves the derivation and its count. -/
theorem ParEtaC.subst {n : ℕ} {A B : Term Var} (h : ParEtaC n A B) (x y : Var) :
    ParEtaC n A[x:=Term.fvar y] B[x:=Term.fvar y] := by
  induction h with
  | fvar z => rw [subst_fvar]
              split <;> apply ParEtaC.refl (LC.fvar _)
  | eta hM hMM' ih => exact ParEtaC.eta (subst_lc hM (LC.fvar y)) ih
  | app hM hN ihM ihN => exact ParEtaC.app ihM ihN
  | @abs xs a M M' hbody ih =>
      refine ParEtaC.abs (xs ∪ {x}) (fun z hz => ?_)
      have key := ih z (by grind)
      rw [subst_open_var, subst_open_var] at key <;> grind

/-- Build an abstraction derivation from a single fresh-variable body instance. -/
theorem ParEtaC.abs_of_open {m : ℕ} {N s' : Term Var} (x : Var)
    (hx : x ∉ fv N) (hx' : x ∉ fv s') (h : ParEtaC m (N ^ Term.fvar x) (s' ^ Term.fvar x)) :
    ParEtaC m (Term.abs N) (Term.abs s') := by
  refine ParEtaC.abs (fv N ∪ fv s') ?_
  intro y hy
  by_cases hyc : y = x
  · rw [hyc]; exact h
  · grind [ParEtaC.subst h x y]

/-- **(Substitutivity)** If `M ⟹η M'` and `N ⟹η N'`, then
`M[x:=N] ⟹η M'[x:=N']` (for some count `c`). -/
theorem ParEtaC.substC {a b : ℕ} {M M' N N' : Term Var} (x : Var)
    (hM : ParEtaC a M M') (hN : ParEtaC b N N') :
    ∃ c, ParEtaC c M[x:=N] M'[x:=N'] := by
  induction hM generalizing N N' with
  | fvar y =>
      rw [subst_fvar, subst_fvar]
      split
      · grind
      · exact ⟨0, ParEtaC.fvar y⟩
  | app hM hN ihM ihN =>
      obtain ⟨c1, hc1⟩ := ihM hN
      obtain ⟨c2, hc2⟩ := ihN hN
      exact ⟨c1 + c2, ParEtaC.app hc1 hc2⟩
  | @abs xs a M M' hbody ih =>
      have ⟨y, hy⟩ := fresh_exists <| free_union [fv] Var
      obtain ⟨c, hc⟩ := ih y (by grind) hN
      refine ⟨c, abs_of_open y ?_ ?_ ?_⟩
      · grind [subst_preserve_not_fvar]
      · grind [subst_preserve_not_fvar]
      · grind [ParEtaC.step_lc_l, ParEtaC.step_lc_r]
  | @eta a M M' hM hMM' ih =>
      obtain ⟨c, hc⟩ := ih hN
      exact ⟨c + 1, ParEtaC.eta hc.step_lc_l hc⟩

/-- Opening form of substitutivity: from `abs M ⟹η abs M'` and `N ⟹η N'`, the
opened bodies satisfy `M^N ⟹η M'^N'` (for some count). -/
theorem ParEtaC.open_of_absBody {a b : ℕ} (xs : Finset Var) {M M' N N' : Term Var}
    (hbody : ∀ x ∉ xs, ParEtaC a (M ^ Term.fvar x) (M' ^ Term.fvar x))
    (hN : ParEtaC b N N') :
    ∃ c, ParEtaC c (M ^ N) (M' ^ N') := by
  have ⟨x, hx⟩ := fresh_exists <| free_union [fv] Var
  obtain ⟨c, hc⟩ := ParEtaC.substC x (hbody x (by grind)) hN
  exact ⟨c, by grind⟩

omit [HasFresh Var] in
/-- Opening by a fresh free variable is injective. -/
theorem open_fvar_inj {A B : Term Var} {x : Var} (hA : x ∉ fv A) (hB : x ∉ fv B)
    (h : A ^ Term.fvar x = B ^ Term.fvar x) : A = B := by
  have hcl : (A ^ Term.fvar x) ^* x = (B ^ Term.fvar x) ^* x := by rw [h]
  rw [<- open_close_var, <- open_close_var] at hcl
  all_goals grind

theorem ParEtaC.toFullEtaStar {i : Nat} {M N : Term Var} (h : ParEtaC i M N) : M ↠ηᶠ N := by
  induction h with
  | eta hM hMM' ih => exact .head (Xi.base (.eta hM)) ih
  | fvar x => exact Relation.ReflTransGen.refl
  | abs xs h ih => exact FullEta.redex_abs_cong xs ih
  | app hM hN ihM ihN =>
      exact Relation.ReflTransGen.trans (FullEta.redex_app_l_cong ihM ((ParEtaC.step_lc_l hN)))
                                        (FullEta.redex_app_r_cong ihN ((ParEtaC.step_lc_r hM)))


/-- The conclusion of the Interaction Lemma at a fixed source term `t`. -/
def InteractionAt (t : Term Var) : Prop :=
  ∀ (n : ℕ) (t' s : Term Var), ParEtaC n t t' → FullBeta t s →
    (∃ s' m, ParEtaC m s s' ∧ FullBeta t' s') ∨ (∃ m, m < n ∧ ParEtaC m s t')

/-- **The Interaction Lemma.** A single β-step `t ⟶β s` against a parallel
η-derivation `t ⟹η t'` either reflects to a genuine β-step `t' ⟶β s'` (with `s`
still parallel-η-reducing to `s'`), or is absorbed — landing back on `t'` with a
strictly smaller η-count. -/
theorem interaction (t : Term Var) : InteractionAt t := by
  induction heq : t.size using Nat.strong_induction_on generalizing t with | h n IH' =>
  have IH : ∀ t : Term Var, t.size < n → t.InteractionAt := fun t h =>
    IH' _ (Nat.lt_of_lt_of_eq (by omega) (by rfl)) _ rfl
  clear IH'
  subst n
  intro n t' s hp hb
  cases hb with
  | base hβ =>
    -- redex at the top: t = app (abs M) N, s = M ^ N
    cases hβ with
    | @beta M N hM hN =>
      cases hp with
      | @app a b _ F _ N' hf hn =>
        cases hf with
        | abs ys hbody =>
          -- t' = app (abs M') N' still a redex; genuine β-step on t'
          obtain ⟨c, hc⟩ := ParEtaC.open_of_absBody ys hbody hn
          exact Or.inl ⟨_, c, hc,
            Xi.base (Beta.beta (ParEtaC.step_lc_r (ParEtaC.abs ys hbody)) (ParEtaC.step_lc_r hn))⟩
        | @eta a2 P _ hP hPF =>
          -- M = app P (bvar 0); the β-step is absorbed by the η-redex
          refine Or.inr ⟨a2 + b, by omega, ParEtaC.app ?_ hn⟩
          rw [open_lc _ _ _ hP]
          exact hPF
  | @appL Z M0 N0 hZ hstep =>
    cases hp with
    | @app a b _ Z' _ M0' hZ' hM0 =>
      rcases IH M0 (by grind) _ _ _ hM0 hstep with ⟨s'', m, hpar, hbeta⟩ | ⟨m, hm, hpar⟩
      · exact Or.inl ⟨_, a + m, ParEtaC.app hZ' hpar, Xi.appL (ParEtaC.step_lc_r hZ') hbeta⟩
      · exact Or.inr ⟨a + m, by omega, ParEtaC.app hZ' hpar⟩
  | @appR Z M0 N0 hZ hstep =>
    cases hp with
    | @app a b M0' _ _ Z' hM0 hZ' =>
      rcases IH M0 (by grind) _ _ _ hM0 hstep with ⟨s'', m, hpar, hbeta⟩ | ⟨m, hm, hpar⟩
      · exact Or.inl ⟨_, m + b, ParEtaC.app hpar hZ', Xi.appR (ParEtaC.step_lc_r hZ') hbeta⟩
      · exact Or.inr ⟨m + b, by omega, ParEtaC.app hpar hZ'⟩
  | @abs M0 N0 xs hbodystep =>
    cases hp with
    | @abs _ _ ys M0' hbody =>
      -- t' = abs M0', hbody : ∀ x ∉ ys, ParEtaC n (M0^x) (M0'^x)
      have ⟨x, hx⟩ := fresh_exists <| free_union [fv] Var
      have hsz : size (M0 ^ Term.fvar x) < size M0.abs := by
        rw [size_open_fvar]
        grind
      rcases IH (M0 ^ Term.fvar x) hsz _ _ _ (hbody x (by grind)) (hbodystep x (by grind)) with
        ⟨s'', m, hpar, hbeta⟩ | ⟨m, hm, hpar⟩
      · refine Or.inl ⟨(s'' ^* x).abs, m, ParEtaC.abs_of_open x (by grind) (by grind) ?_, ?_⟩
        · rw [close_open _ _ (FullBeta.step_lc_r hbeta)]
          grind
        · rw [open_close x M0' 0 (by grind)]
          exact FullBeta.step_abs_close (by grind)
      · exact Or.inr ⟨m, hm, ParEtaC.abs_of_open x (by grind) (by grind) hpar⟩
    | @eta a2 P _ hP hPF =>
      -- M0 = app P (bvar 0), n = a2 + 1, hPF : ParEtaC a2 P t'
      have ⟨x, hx⟩ := fresh_exists <| free_union [fv] Var
      have hstepx : FullBeta (Term.app P (Term.fvar x)) (N0 ^ Term.fvar x) := by
        grind [hbodystep x (by grind)]
      generalize hw : N0 ^ Term.fvar x = w at hstepx
      cases hstepx with
      | base hβ =>
        cases hβ with
        | @beta Q Narg hQ hNarg =>
          -- P = abs Q, Narg = fvar x, w = Q ^ fvar x, hw : N0^x = Q^x
          have hN0Q : N0 = Q := open_fvar_inj (by grind) (by grind) hw
          exact Or.inr ⟨a2, by omega, by rw [hN0Q]; exact hPF⟩
      | @appL Z M N hZ hxi =>
        cases hxi with | base hb2 => cases hb2
      | @appR Z M N hZ hxi =>
        -- M = P, Z = fvar x; hxi : FullBeta P N; w = app N (fvar x)
        have hPsLC : LC N := FullBeta.step_lc_r hxi
        have hxN : x ∉ fv N := by grind [FullBeta.step_not_fv hxi]
        have hNe : N0 = Term.app N (Term.bvar 0) := by apply @open_fvar_inj _ _ _ _ x <;> grind
        rcases IH P (by grind) _ _ _ hPF hxi with ⟨s', m, hpar, hbeta⟩ | ⟨m, hm, hpar⟩
        · exact Or.inl ⟨s', m + 1, by rw [hNe]; exact ParEtaC.eta hPsLC hpar, hbeta⟩
        · exact Or.inr ⟨m + 1, by omega, by rw [hNe]; exact ParEtaC.eta hPsLC hpar⟩

/-- **Generalized SN-transfer theorem.**  If `t ⟹η t'` (parallel η, any count)
and `t'` is β-strongly-normalising, then so is `t`. -/
theorem sn_transfer {t t' : Term Var}
    (hacc : Relation.SN (FullBeta : Term Var → Term Var → Prop) t')
    {n : ℕ} (hp : ParEtaC n t t') :
    Relation.SN (FullBeta : Term Var → Term Var → Prop) t := by
  induction hacc generalizing t n with
  | intro c hc ih =>
    induction n using Nat.strong_induction_on generalizing t with
    | _ n ihn =>
      refine Acc.intro t (fun s hs => ?_)
      rcases interaction _ _ _ _ hp hs with ⟨s', m, hps', hb'⟩ | ⟨m, hm, hps⟩
      · exact ih s' hb' hps'
      · exact ihn m hm hps

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
