/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.Basic
import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.Properties
import Cslib.Computability.LambdaCalculus.Untyped.LocallyNameless.FullBeta
import Cslib.Data.Relation

/-! # β-confluence for the λ-calculus -/

universe u

variable {Var : Type u} 

namespace LambdaCalculus.LocallyNameless.Term

/-- A parallel β-reduction step. -/
@[aesop safe (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet]) [constructors], reduction_sys paraRs "ₚ"]
inductive Parallel : Term Var → Term Var → Prop
/-- Free variables parallel step to themselves. -/
| fvar (x : Var) : Parallel (fvar x) (fvar x)
/-- A parallel left and right congruence rule for application. -/
| app : Parallel L L' → Parallel M M' → Parallel (app L M) (app L' M')
/-- Congruence rule for lambda terms. -/
| abs (xs : Finset Var) : (∀ x ∉ xs, Parallel (m ^ fvar x) (m' ^ fvar x)) → Parallel (abs m) (abs m')
/-- A parallel β-reduction. -/
| beta (xs : Finset Var) : 
    (∀ x ∉ xs, Parallel (m ^ fvar x) (m' ^ fvar x) ) →
    Parallel n n' → 
    Parallel (app (abs m) n) (m' ^ n')

-- TODO: I think this could be generated along with `para_rs`
lemma para_rs_Red_eq {α} : (@paraRs α).Red = Parallel := by rfl

variable {M M' N N' : Term Var}

/-- The left side of a parallel reduction is locally closed. -/
@[aesop unsafe (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma para_lc_l (step : M ⭢ₚ N) : LC M  := by
  induction step
  case abs _ _ xs _ ih => exact LC.abs xs _ ih
  case beta => refine LC.app (LC.abs ?_ _ ?_) ?_ <;> assumption
  all_goals constructor <;> assumption

variable [HasFresh Var] [DecidableEq Var]

/-- The right side of a parallel reduction is locally closed. -/
@[aesop unsafe (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma para_lc_r (step : M ⭢ₚ N) : LC N := by
  induction step
  case abs _ _ xs _ ih => exact LC.abs xs _ ih
  case beta => refine beta_lc (LC.abs ?_ _ ?_) ?_ <;> assumption
  all_goals constructor <;> assumption

/-- Parallel reduction is reflexive for locally closed terms. -/
@[aesop safe (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
def Parallel.lc_refl (M : Term Var) : LC M → M ⭢ₚ M := by
  intros lc
  induction lc
  all_goals constructor <;> assumption

-- TODO: better ways to handle this?
-- The problem is that sometimes when we apply a theorem we get out of our notation, so aesop can't
-- see they are the same, including constructors.
@[aesop safe (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
def Parallel.lc_refl' (M : Term Var) : LC M → Parallel M M := Parallel.lc_refl M

omit [HasFresh Var] [DecidableEq Var] in
/-- A single β-reduction implies a single parallel reduction. -/
lemma step_to_para (step : M ⭢βᶠ N) : (M ⭢ₚ N) := by
  induction step <;> simp only [para_rs_Red_eq]
  case beta _ abs_lc _ => cases abs_lc with | abs xs _ => 
    apply Parallel.beta xs <;> intros <;> apply Parallel.lc_refl <;> aesop
  all_goals aesop (config := {enableSimp := false})

open FullBeta in
/-- A single parallel reduction implies a multiple β-reduction. -/
lemma para_to_redex (para : M ⭢ₚ N) : (M ↠βᶠ N) := by
  induction para
  case fvar => constructor
  case app _ _ _ _ l_para m_para redex_l redex_m =>
    trans
    exact redex_app_l_cong redex_l (para_lc_l m_para)
    exact redex_app_r_cong redex_m (para_lc_r l_para)
  case abs t t' xs _ ih =>
    apply redex_abs_cong xs
    intros x mem
    exact ih x mem
  case beta m m' n n' xs para_ih para_n redex_ih redex_n =>
    have m'_abs_lc : LC m'.abs := by
      apply LC.abs xs
      intros _ mem
      exact para_lc_r (para_ih _ mem)
    calc
      m.abs.app n ↠βᶠ m'.abs.app n  := redex_app_l_cong (redex_abs_cong xs (λ _ mem ↦ redex_ih _ mem)) (para_lc_l para_n)
      _           ↠βᶠ m'.abs.app n' := redex_app_r_cong redex_n m'_abs_lc
      _           ⭢βᶠ m' ^ n'       := beta m'_abs_lc (para_lc_r para_n)

/-- Multiple parallel reduction is equivalent to multiple β-reduction. -/
theorem parachain_iff_redex : (M ↠ₚ N) ↔ (M ↠βᶠ N) := by
  refine Iff.intro ?chain_to_redex ?redex_to_chain <;> intros h <;> induction' h <;> try rfl
  case redex_to_chain.tail redex chain => exact Relation.ReflTransGen.tail chain (step_to_para redex)
  case chain_to_redex.tail para  redex => exact Relation.ReflTransGen.trans redex (para_to_redex para)

/-- Parallel reduction respects substitution. -/
lemma para_subst (x : Var) : (M ⭢ₚ M') → (N ⭢ₚ N') → (M[x := N] ⭢ₚ M'[x := N']) := by
  intros pm pn
  induction pm
  case fvar => aesop
  case beta _ _ _ _ xs _ _ ih _ => 
    simp only [open']
    rw [subst_open _ _ _ _ _ (para_lc_r pn)]
    apply Parallel.beta (xs ∪ {x})
    intros y ymem
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at ymem
    push_neg at ymem
    rw [
      subst_def, 
      subst_open_var _ _ _ _ _ (para_lc_r pn), 
      subst_open_var _ _ _ _ _ (para_lc_l pn)
    ]
    apply ih
    all_goals aesop
  case app => constructor <;> assumption
  case abs u u' xs mem ih => 
    apply Parallel.abs (xs ∪ {x})
    intros y ymem
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at ymem
    repeat rw [subst_def]
    rw [subst_open_var _ _ _ _ ?_ (para_lc_l pn), subst_open_var _ _ _ _ ?_ (para_lc_r pn)]
    push_neg at ymem
    apply ih
    all_goals aesop

/-- Parallel substitution respects closing and opening. -/
lemma para_open_close (x y z) : 
  (M ⭢ₚ M') → 
  y ∉ (M.fv ∪ M'.fv ∪ {x}) → 
  M⟦z ↜ x⟧⟦z ↝ fvar y⟧ ⭢ₚ M'⟦z ↜ x⟧⟦z ↝ fvar y⟧ 
  := by
  intros para vars
  simp only [Finset.union_assoc, Finset.mem_union, Finset.mem_singleton, not_or] at vars
  rw [open_close_to_subst, open_close_to_subst] 
  apply para_subst
  exact para
  constructor
  exact para_lc_r para
  exact para_lc_l para

/-- Parallel substitution respects fresh opening. -/
lemma para_open_out (L : Finset Var) :
    (∀ x, x ∉ L → (M ^ fvar x) ⭢ₚ (N ^ fvar x))
    → (M' ⭢ₚ N') → (M ^ M') ⭢ₚ (N ^ N') := by
    intros mem para
    let ⟨x, qx⟩ := fresh_exists (L ∪ N.fv ∪ M.fv)
    simp only [Finset.union_assoc, Finset.mem_union, not_or] at qx
    obtain ⟨q1, q2, q3⟩ := qx
    rw [subst_intro x M' _ q3 (para_lc_l para), subst_intro x N' _ q2 (para_lc_r para)]
    exact para_subst x (mem x q1) para

-- TODO: the Takahashi translation would be a much nicer and shorter proof, but I had difficultly
-- writing it for locally nameless terms.

-- adapted from https://github.com/ElifUskuplu/Stlc_deBruijn/blob/main/Stlc/confluence.lean
/-- Parallel reduction has the diamond property. -/
theorem para_diamond : Diamond (@Parallel Var) := by
  intros t t1 t2 tpt1
  revert t2
  induction tpt1 <;> intros t2 tpt2
  case fvar x => exact ⟨t2, by aesop⟩
  case abs s1 s2' xs mem ih => 
    cases tpt2
    case abs t2' xs' mem' =>
      have ⟨x, qx⟩ := fresh_exists (xs ∪ xs' ∪ t2'.fv ∪ s2'.fv)
      simp only [Finset.union_assoc, Finset.mem_union, not_or] at qx
      have ⟨q1, q2, q3, q4⟩ := qx
      have ⟨t', qt'_l, qt'_r⟩ := ih x q1 (mem' _ q2)
      exists abs (t' ^* x)
      constructor 
      <;> [let z := s2'; let z := t2']
      <;> apply Parallel.abs ((z ^ fvar x).fv ∪ t'.fv ∪ {x})
      <;> intros y qy <;> simp only [open', close]
      <;> [rw [←open_close x _ 0 q4]; rw [←open_close x _ 0 q3]] 
      <;> refine para_open_close x y 0 ?_ qy <;> [exact qt'_l; exact qt'_r]
  case beta s1 s1' s2 s2' xs mem ps ih1 ih2 => 
    cases tpt2
    case app u2 u2' s1pu2 s2pu2' => 
      cases s1pu2
      case abs s1'' xs' mem' =>
        have ⟨x, qx⟩ := fresh_exists (xs ∪ xs' ∪ s1''.fv ∪ s1'.fv)
        simp only [Finset.union_assoc, Finset.mem_union, not_or] at qx
        obtain ⟨q1, q2, q3, q4⟩ := qx
        have ⟨t', qt'_l, qt'_r⟩ := ih2 s2pu2'
        have ⟨t'', qt''_l, qt''_r⟩ := @ih1 x q1 _ (mem' _ q2)
        exists (t'' ^* x) ^ t'
        constructor
        · rw [subst_intro x s2' _ q4 (para_lc_l qt'_l), 
              subst_intro x t' _ (close_var_not_fvar x t'') (para_lc_r qt'_l)]
          simp only [open', close]
          rw [close_open _ _ _ (para_lc_r qt''_l)]
          exact para_subst x qt''_l qt'_l
        · apply Parallel.beta ((s1'' ^ fvar x).fv ∪ t''.fv ∪ {x})
          intros y qy
          rw [←open_close x s1'' 0]
          apply para_open_close
          all_goals aesop
    case beta u1' u2' xs' mem' s2pu2' => 
      have ⟨x, qx⟩ := fresh_exists (xs ∪ xs' ∪ u1'.fv ∪ s1'.fv ∪ s2'.fv ∪ u2'.fv)
      simp only [Finset.union_assoc, Finset.mem_union, not_or] at qx
      have ⟨q1, q2, q3, q4, q5, q6⟩ := qx
      have ⟨t', qt'_l, qt'_r⟩ := ih2 s2pu2'
      have ⟨t'', qt''_l, qt''_r⟩ := @ih1 x q1 _ (mem' _ q2)
      rw [subst_intro x u2' u1' _ (para_lc_l qt'_r), subst_intro x s2' s1' _ (para_lc_l qt'_l)]
      exists t'' [x := t']
      exact ⟨para_subst x qt''_l qt'_l, para_subst x qt''_r qt'_r⟩
      all_goals aesop
  case app s1 s1' s2 s2' s1ps1' _ ih1 ih2  =>
    cases tpt2
    case app u1 u2' s1 s2 =>
      have ⟨l, _, _⟩ := ih1 s1
      have ⟨r, _, _⟩ := ih2 s2
      exact ⟨app l r, by aesop⟩
    case beta t1' u1' u2' xs mem s2pu2' => 
      cases s1ps1'
      case abs s1'' xs' mem' =>
        have ⟨x, qx⟩ := fresh_exists (xs ∪ xs' ∪ s1''.fv ∪ u1'.fv)
        simp only [Finset.union_assoc, Finset.mem_union, not_or] at qx
        obtain ⟨q1, q2, q3, q4⟩ := qx
        have ⟨t', qt'_l, qt'_r⟩ := ih2 s2pu2'
        have ⟨t'', qt''_l, qt''_r⟩ := @ih1 (abs u1') (Parallel.abs xs mem)
        cases qt''_l
        next w1 xs'' mem'' =>
        cases qt''_r
        case abs xs''' mem''' =>
          exists w1 ^ t'
          constructor
          · aesop (config := {enableSimp := false})
          · exact para_open_out xs''' mem''' qt'_r

/-- Parallel reduction is confluent. -/
theorem para_confluence : Confluence (@Parallel Var) := 
  Relation.ReflTransGen.diamond_confluence para_diamond

/-- β-reduction is confluent. -/
theorem confluence_beta : Confluence (@FullBeta Var) := by
  simp only [Confluence]
  have eq : Relation.ReflTransGen (@Parallel Var) = Relation.ReflTransGen (@FullBeta Var) := by
    ext
    exact parachain_iff_redex
  rw [←eq]
  exact @para_confluence Var _ _
